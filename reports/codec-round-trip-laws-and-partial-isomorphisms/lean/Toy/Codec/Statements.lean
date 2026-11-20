import Toy.Codec.Defs

/-!
# Main theorem statements (`Toy.Codec`)

Positive theorems and characterizations for codec round-trip laws,
re-encode-and-compare canonicalization, combinator closure, framed codecs
and list concatenation, and coproduct complement decompositions (`B ≃ A ⊕ C`).
-/

namespace Toy.Codec

universe u v w w₁ w₂ u₁ u₂ v₁ v₂

/-! ## Private helper lemmas used inside proofs -/

private theorem decompToFun_of_some {A : Type u} {B : Type v} {c : Codec A B} {b : B} {a : A}
    (h : c.dec b = some a) : decompToFun c b = Sum.inl a := by
  unfold decompToFun
  split
  · next a' h' => rw [h] at h'; cases h'; rfl
  · next h' => rw [h] at h'; cases h'

private theorem decompToFun_of_none {A : Type u} {B : Type v} {c : Codec A B} {b : B}
    (h : c.dec b = none) : decompToFun c b = Sum.inr ⟨b, h⟩ := by
  unfold decompToFun
  split
  · next a' h' => rw [h] at h'; cases h'
  · rfl

private theorem junkToC_spec' {A : Type u} {B : Type v} {C : Type w}
    (f : B → A ⊕ C) (g : A ⊕ C → B) (j : Junk (codecOfSplit f g)) :
    f j.1 = Sum.inr (junkToC f g j) := by
  have hj : inlMatcher (f j.1) = none := j.2
  unfold junkToC
  split
  · next a h => rw [h] at hj; cases hj
  · next k h => exact h

private theorem listEncDec_aux {A : Type u} {β : Type v} (fc : FramedCodec A β)
    (hped : PrefixEncDec fc) :
    ∀ (xs : List β) (as : List A), decList fc xs = some as → encList fc.enc as = xs
  | [], as, h => by
    rw [decList] at h; cases h; rfl
  | b :: bs, as, h => by
    rw [decList] at h
    cases hp : fc.decPrefix (b :: bs) with
    | none => simp [hp] at h
    | some p =>
      obtain ⟨a, rest⟩ := p
      simp only [hp] at h
      by_cases hlt : rest.length < (b :: bs).length
      · simp only [hlt, ↓reduceDIte] at h
        cases hd : decList fc rest with
        | none => rw [hd] at h; cases h
        | some as' =>
          rw [hd] at h
          cases h
          have e := listEncDec_aux fc hped rest as' hd
          show fc.enc a ++ encList fc.enc as' = b :: bs
          rw [e]; exact (hped _ a rest hp).symm
      · simp only [hlt, ↓reduceDIte] at h
        cases h
termination_by xs => xs.length

/-! ## Characterization, bijection with injections, and canonicalization -/

/-- `DecEnc` alone implies that the encoder `c.enc` is injective (`EncDec` is not needed). -/
theorem decEnc_imp_enc_injective {A : Type u} {B : Type v} (c : Codec A B)
    (hde : DecEnc c) : Function.Injective c.enc := by
  intro a₁ a₂ h
  have h1 := hde a₁
  rw [h, hde a₂] at h1
  exact (Option.some.inj h1).symm

/-- A codec satisfies both `DecEnc` and `EncDec` if and only if the graph of `c.dec`
    is the exact converse of the graph of `c.enc`.
    (`Function.Injective c.enc` is omitted from the right-hand side because it is
    derivable from either side; see `decEnc_imp_enc_injective` and
    `decEqSomeIff_imp_enc_injective`.) -/
theorem lawful_iff_dec_eq_some_iff {A : Type u} {B : Type v} (c : Codec A B) :
    (DecEnc c ∧ EncDec c) ↔ (∀ (b : B) (a : A), c.dec b = some a ↔ c.enc a = b) := by
  constructor
  · rintro ⟨hde, hed⟩ b a
    exact ⟨hed b a, fun h => by subst h; exact hde a⟩
  · intro h
    exact ⟨fun a => (h _ a).mpr rfl, fun b a => (h b a).mp⟩

/-- Corollary (hypothesis minimality for `lawful_iff_dec_eq_some_iff`): the graph-converse
    relation `∀ b a, c.dec b = some a ↔ c.enc a = b` alone implies `Function.Injective c.enc`. -/
theorem decEqSomeIff_imp_enc_injective {A : Type u} {B : Type v} (c : Codec A B)
    (hconv : ∀ (b : B) (a : A), c.dec b = some a ↔ c.enc a = b) :
    Function.Injective c.enc := by
  intro a₁ a₂ h
  have h1 : c.dec (c.enc a₂) = some a₁ := (hconv _ _).mpr h
  have h2 : c.dec (c.enc a₂) = some a₂ := (hconv _ _).mpr rfl
  rw [h1] at h2
  exact Option.some.inj h2

/-- Under `DecEnc`, `EncDec` (canonicality) is equivalent to `DecInj` (whole-input
    decoder injectivity / EverParse-style non-malleability). Note that `EncDec → DecInj`
    holds unconditionally (`encDec_imp_decInj`); only `DecInj → EncDec` requires `DecEnc`. -/
theorem lawful_iff_decEnc_and_decInj {A : Type u} {B : Type v} (c : Codec A B) :
    (DecEnc c ∧ EncDec c) ↔ (DecEnc c ∧ DecInj c) := by
  constructor
  · rintro ⟨hde, hed⟩
    exact ⟨hde, fun b₁ b₂ a h₁ h₂ => (hed b₁ a h₁).symm.trans (hed b₂ a h₂)⟩
  · rintro ⟨hde, hinj⟩
    exact ⟨hde, fun b a h => hinj _ _ a (hde a) h⟩

/-- A lawful codec's decoder is uniquely determined by its encoder (without `Classical.choice`,
    using function extensionality). -/
theorem dec_unique_of_lawful {A : Type u} {B : Type v} (c₁ c₂ : Codec A B)
    (henc : c₁.enc = c₂.enc)
    (hde₁ : DecEnc c₁) (hed₁ : EncDec c₁)
    (hde₂ : DecEnc c₂) (hed₂ : EncDec c₂) :
    c₁.dec = c₂.dec := by
  funext b
  cases h₁ : c₁.dec b with
  | none =>
    cases h₂ : c₂.dec b with
    | none => rfl
    | some a =>
      have e := hed₂ b a h₂
      rw [← henc] at e
      subst e
      rw [hde₁ a] at h₁
      cases h₁
  | some a =>
    have e := hed₁ b a h₁
    rw [henc] at e
    subst e
    exact (hde₂ a).symm

/-- Every injective function `f : A → B` induces a `DecEnc`-lawful codec via
    `classicalCodec f` (using `Classical.choice` to decide image membership and pick
    the unique preimage). -/
theorem classicalCodec_decEnc_of_injective {A : Type u} {B : Type v}
    (f : A → B) (hf : Function.Injective f) :
    DecEnc (classicalCodec f) := by
  intro a
  unfold classicalCodec classicalDec
  dsimp only
  split
  · next h => exact congrArg some (hf (Classical.choose_spec h))
  · next hn => exact absurd ⟨a, rfl⟩ hn

/-- Companion lemma: `classicalCodec f` always satisfies `EncDec`, even when `f` is not injective. -/
theorem classicalCodec_encDec {A : Type u} {B : Type v} (f : A → B) :
    EncDec (classicalCodec f) := by
  intro b a h
  unfold classicalCodec classicalDec at h
  dsimp only at h
  split at h
  · next hex => cases h; exact Classical.choose_spec hex
  · cases h

/-- Applying `classicalCodec` to the encoder of any lawful codec recovers that exact codec
    (together with `decEnc_imp_enc_injective`, `classicalCodec_decEnc_of_injective`,
    `classicalCodec_encDec`, and `classicalCodec_enc`, assembling the classical bijection
    between lawful codecs `A ⇄ B` and injections `A → B`). -/
theorem classicalCodec_recover_of_lawful {A : Type u} {B : Type v} (c : Codec A B)
    (hde : DecEnc c) (hed : EncDec c) :
    classicalCodec c.enc = c := by
  apply Codec.ext
  · rfl
  · funext b
    show classicalDec c.enc b = c.dec b
    unfold classicalDec
    split
    · next hex =>
      exact (hde _).symm.trans (congrArg c.dec (Classical.choose_spec hex))
    · next hn =>
      cases hd : c.dec b with
      | none => rfl
      | some a => exact absurd ⟨a, hed b a hd⟩ hn

/-- Constructive sufficiency of `FiberSplit`: given an injection `f : A → B` equipped with
    `s : FiberSplit f`, `codecOfFiberSplit f s` satisfies `DecEnc` (while `EncDec` holds
    unconditionally via `codecOfFiberSplit_encDec`, with zero axioms). -/
theorem codecOfFiberSplit_decEnc_of_injective {A : Type u} {B : Type v}
    (f : A → B) (s : FiberSplit f) (hf : Function.Injective f) :
    DecEnc (codecOfFiberSplit f s) := by
  intro a
  unfold codecOfFiberSplit
  dsimp only
  split
  · next a' h' _ => exact congrArg some (hf h')
  · next hn _ => exact absurd rfl (hn a)

/-- Constructive necessity and recovery for `FiberSplit`: every lawful codec `c` yields
    `fiberSplitOfLawful c hde hed : FiberSplit c.enc`, and for *any* `s : FiberSplit c.enc`,
    `codecOfFiberSplit c.enc s = c` (without `Classical.choice`). -/
theorem codecOfFiberSplit_eq_of_lawful {A : Type u} {B : Type v}
    (c : Codec A B) (hde : DecEnc c) (hed : EncDec c) (s : FiberSplit c.enc) :
    codecOfFiberSplit c.enc s = c := by
  apply Codec.ext
  · rfl
  · funext b
    unfold codecOfFiberSplit
    dsimp only
    split
    · next a h' _ => rw [← h', hde]
    · next hn _ =>
      cases hd : c.dec b with
      | none => rfl
      | some a => exact absurd (hed b a hd) (hn a)

/-- Any lawful codec's decoder tests membership in the image of `c.enc`:
    `(c.dec b).isSome = true ↔ ∃ a, c.enc a = b` (EverParse §2.1 exactness). -/
theorem lawful_dec_isSome_iff_mem_range {A : Type u} {B : Type v} (c : Codec A B)
    (hde : DecEnc c) (hed : EncDec c) :
    ∀ b : B, (c.dec b).isSome = true ↔ ∃ a : A, c.enc a = b := by
  intro b
  constructor
  · intro h
    cases hd : c.dec b with
    | none => rw [hd] at h; cases h
    | some a => exact ⟨a, hed b a hd⟩
  · rintro ⟨a, rfl⟩
    rw [hde a]; rfl

/-- Negated corollary of `lawful_dec_isSome_iff_mem_range` characterizing `Junk c`:
    for a lawful codec, `c.dec b = none` holds iff `b` lies outside the image of `c.enc`. -/
theorem junk_iff_not_in_image_of_lawful {A : Type u} {B : Type v} (c : Codec A B)
    (hde : DecEnc c) (hed : EncDec c) :
    ∀ b : B, c.dec b = none ↔ ∀ a : A, c.enc a ≠ b := by
  intro b
  constructor
  · intro hn a ha
    subst ha
    rw [hde a] at hn
    cases hn
  · intro hall
    cases hd : c.dec b with
    | none => rfl
    | some a => exact absurd (hed b a hd) (hall a)

/-- Escape hatch from single-law malleability: when `B` has decidable equality,
    `canonicalize c` preserves `DecEnc c` while upgrading the decoder to satisfy
    `EncDec (canonicalize c)` unconditionally (`canonicalize_encDec`) with the same encoder. -/
theorem canonicalize_decEnc_of_decEnc {A : Type u} {B : Type v} [DecidableEq B]
    (c : Codec A B) (hde : DecEnc c) :
    DecEnc (canonicalize c) := by
  intro a
  unfold canonicalize
  dsimp only
  rw [hde a]
  simp

/-! ## Closure under composition, products, and sums -/

/-- Sequential composition preserves `DecEnc` (independent of `EncDec`). -/
theorem comp_decEnc {A : Type u} {B : Type v} {C : Type w}
    (c₁ : Codec A B) (c₂ : Codec B C)
    (hde₁ : DecEnc c₁) (hde₂ : DecEnc c₂) :
    DecEnc (c₁.comp c₂) := by
  intro a
  show (c₂.dec (c₂.enc (c₁.enc a))).bind c₁.dec = some a
  rw [hde₂]
  exact hde₁ a

/-- Sequential composition preserves `EncDec` (independent of `DecEnc`). -/
theorem comp_encDec {A : Type u} {B : Type v} {C : Type w}
    (c₁ : Codec A B) (c₂ : Codec B C)
    (hed₁ : EncDec c₁) (hed₂ : EncDec c₂) :
    EncDec (c₁.comp c₂) := by
  intro x a h
  change (c₂.dec x).bind c₁.dec = some a at h
  cases h2 : c₂.dec x with
  | none => rw [h2] at h; cases h
  | some b =>
    rw [h2] at h
    change c₁.dec b = some a at h
    show c₂.enc (c₁.enc a) = x
    rw [hed₁ b a h, hed₂ x b h2]

/-- Product combinator preserves `DecEnc` (independent of `EncDec`). -/
theorem prod_decEnc {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
    (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
    (hde₁ : DecEnc c₁) (hde₂ : DecEnc c₂) :
    DecEnc (c₁.prod c₂) := by
  intro p
  obtain ⟨a₁, a₂⟩ := p
  simp only [Codec.prod]
  rw [hde₁ a₁, hde₂ a₂]

/-- Product combinator preserves `EncDec` (independent of `DecEnc`). -/
theorem prod_encDec {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
    (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
    (hed₁ : EncDec c₁) (hed₂ : EncDec c₂) :
    EncDec (c₁.prod c₂) := by
  intro b a h
  obtain ⟨b₁, b₂⟩ := b
  obtain ⟨a₁, a₂⟩ := a
  simp only [Codec.prod] at h ⊢
  cases h1 : c₁.dec b₁ with
  | none => rw [h1] at h; cases h
  | some x₁ =>
    cases h2 : c₂.dec b₂ with
    | none => rw [h1, h2] at h; cases h
    | some x₂ =>
      rw [h1, h2] at h
      cases h
      rw [hed₁ b₁ a₁ h1, hed₂ b₂ a₂ h2]

/-- Sum combinator preserves `DecEnc` (independent of `EncDec`). -/
theorem sum_decEnc {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
    (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
    (hde₁ : DecEnc c₁) (hde₂ : DecEnc c₂) :
    DecEnc (c₁.sum c₂) := by
  intro a
  cases a with
  | inl a =>
    show (c₁.dec (c₁.enc a)).map Sum.inl = some (Sum.inl a)
    rw [hde₁ a]; rfl
  | inr a =>
    show (c₂.dec (c₂.enc a)).map Sum.inr = some (Sum.inr a)
    rw [hde₂ a]; rfl

/-- Sum combinator preserves `EncDec` (independent of `DecEnc`). -/
theorem sum_encDec {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
    (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
    (hed₁ : EncDec c₁) (hed₂ : EncDec c₂) :
    EncDec (c₁.sum c₂) := by
  intro b a h
  cases b with
  | inl b =>
    change (c₁.dec b).map Sum.inl = some a at h
    cases hd : c₁.dec b with
    | none => rw [hd] at h; cases h
    | some x => rw [hd] at h; cases h; show Sum.inl (c₁.enc x) = Sum.inl b; rw [hed₁ b x hd]
  | inr b =>
    change (c₂.dec b).map Sum.inr = some a at h
    cases hd : c₂.dec b with
    | none => rw [hd] at h; cases h
    | some x => rw [hd] at h; cases h; show Sum.inr (c₂.enc x) = Sum.inr b; rw [hed₂ b x hd]

/-! ## Framed codecs over `List β` -/

/-- Framed analogue of `lawful_iff_dec_eq_some_iff`: a framed codec satisfies both
    `PrefixDecEnc` and `PrefixEncDec` iff `decPrefix xs = some (a, rest)` holds
    precisely when `xs = enc a ++ rest`. -/
theorem framed_lawful_iff_decPrefix_eq_some_iff {A : Type u} {β : Type v}
    (fc : FramedCodec A β) :
    (PrefixDecEnc fc ∧ PrefixEncDec fc) ↔
      (∀ (xs : List β) (a : A) (rest : List β),
        fc.decPrefix xs = some (a, rest) ↔ xs = fc.enc a ++ rest) := by
  constructor
  · rintro ⟨h1, h2⟩ xs a rest
    exact ⟨h2 xs a rest, fun h => by subst h; exact h1 a rest⟩
  · intro h
    exact ⟨fun a rest => (h _ a rest).mpr rfl, fun xs a rest => (h xs a rest).mp⟩

/-- The prefix round-trip law `PrefixDecEnc` implies `PrefixFree fc.enc`
    (the encoder is injective and its codeword image is prefix-free). -/
theorem prefixDecEnc_imp_prefixFree {A : Type u} {β : Type v}
    (fc : FramedCodec A β) (hpde : PrefixDecEnc fc) :
    PrefixFree fc.enc := by
  intro a₁ a₂ s h
  have e1 := hpde a₁ s
  have e2 := hpde a₂ []
  rw [List.append_nil, ← h, e1] at e2
  exact (Prod.mk.inj (Option.some.inj e2)).1

/-- Heterogeneous framed sequencing preserves `PrefixDecEnc` (without needing
    `PrefixEncDec` or `NonEmptyEnc`). -/
theorem seq_prefixDecEnc {A₁ : Type u₁} {A₂ : Type u₂} {β : Type v}
    (fc₁ : FramedCodec A₁ β) (fc₂ : FramedCodec A₂ β)
    (hpde₁ : PrefixDecEnc fc₁) (hpde₂ : PrefixDecEnc fc₂) :
    PrefixDecEnc (fc₁.seq fc₂) := by
  intro p rest
  obtain ⟨a₁, a₂⟩ := p
  simp only [FramedCodec.seq, List.append_assoc]
  rw [hpde₁ a₁ (fc₂.enc a₂ ++ rest)]
  dsimp only
  rw [hpde₂ a₂ rest]

/-- Heterogeneous framed sequencing preserves `PrefixEncDec` (without needing
    `PrefixDecEnc` or `NonEmptyEnc`). -/
theorem seq_prefixEncDec {A₁ : Type u₁} {A₂ : Type u₂} {β : Type v}
    (fc₁ : FramedCodec A₁ β) (fc₂ : FramedCodec A₂ β)
    (hped₁ : PrefixEncDec fc₁) (hped₂ : PrefixEncDec fc₂) :
    PrefixEncDec (fc₁.seq fc₂) := by
  intro xs p rest h
  unfold FramedCodec.seq at h
  dsimp only at h
  cases h₁ : fc₁.decPrefix xs with
  | none => rw [h₁] at h; cases h
  | some p₁ =>
    obtain ⟨a₁, rest₁⟩ := p₁
    rw [h₁] at h
    dsimp only at h
    cases h₂ : fc₂.decPrefix rest₁ with
    | none => rw [h₂] at h; cases h
    | some p₂ =>
      obtain ⟨a₂, rest₂⟩ := p₂
      rw [h₂] at h
      cases h
      have e₁ := hped₁ xs a₁ rest₁ h₁
      have e₂ := hped₂ rest₁ a₂ rest h₂
      show xs = (fc₁.enc a₁ ++ fc₂.enc a₂) ++ rest
      rw [e₁, e₂, List.append_assoc]

/-- Under `PrefixDecEnc fc`, the whole-input list codec `listCodec fc` satisfies `DecEnc`
    if and only if every codeword is non-empty (`NonEmptyEnc fc.enc`).
    Note: when `A` has two distinct values, `NonEmptyEnc fc.enc` follows automatically
    from `PrefixDecEnc fc` (`nonEmptyEnc_of_prefixDecEnc_of_ne`), so `NonEmptyEnc`
    can fail under `PrefixDecEnc` only when `A` is a subsingleton. -/
theorem listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc {A : Type u} {β : Type v}
    (fc : FramedCodec A β) (hpde : PrefixDecEnc fc) :
    DecEnc (listCodec fc) ↔ NonEmptyEnc fc.enc := by
  constructor
  · intro hde a ha
    have h1 := hde [a]
    have h0 := hde []
    change decList fc (fc.enc a ++ []) = some [a] at h1
    change decList fc [] = some [] at h0
    rw [ha, List.append_nil, h0] at h1
    cases h1
  · intro hne as
    show decList fc (encList fc.enc as) = some as
    induction as with
    | nil => rw [encList, decList]
    | cons a tail ih =>
      have hcons : encList fc.enc (a :: tail) = fc.enc a ++ encList fc.enc tail := rfl
      obtain ⟨b, bs, hb⟩ : ∃ b bs, fc.enc a = b :: bs := by
        cases h : fc.enc a with
        | nil => exact absurd h (hne a)
        | cons b bs => exact ⟨b, bs, rfl⟩
      rw [hcons, hb, List.cons_append, decList]
      have hp : fc.decPrefix (b :: (bs ++ encList fc.enc tail)) =
          some (a, encList fc.enc tail) := by
        rw [← List.cons_append, ← hb]; exact hpde a _
      simp only [hp]
      have hlt : (encList fc.enc tail).length < (b :: (bs ++ encList fc.enc tail)).length := by
        simp only [List.length_cons, List.length_append]; omega
      simp only [hlt, ↓reduceDIte, ih]
      rfl

/-- If a framed codec satisfies the converse prefix law `PrefixEncDec`, then its induced
    `listCodec fc` satisfies `EncDec` (neither `PrefixDecEnc` nor `NonEmptyEnc` is needed). -/
theorem listCodec_encDec_of_prefixEncDec {A : Type u} {β : Type v}
    (fc : FramedCodec A β) (hped : PrefixEncDec fc) :
    EncDec (listCodec fc) := by
  intro xs as h
  exact listEncDec_aux fc hped xs as h

/-! ## Coproduct complement decompositions (`B ≃ A ⊕ C`) -/

/-- Law-by-law left-inverse equivalence for the canonical split `(decompToFun c, decompInvFun c)`:
    `LeftInv (decompToFun c) (decompInvFun c)` holds if and only if `EncDec c` holds. -/
theorem leftInv_decomp_iff_encDec {A : Type u} {B : Type v} (c : Codec A B) :
    LeftInv (decompToFun c) (decompInvFun c) ↔ EncDec c := by
  constructor
  · intro hl b a h
    have := hl b
    rw [decompToFun_of_some h] at this
    exact this
  · intro hed b
    cases hd : c.dec b with
    | none => rw [decompToFun_of_none hd]; rfl
    | some a => rw [decompToFun_of_some hd]; exact hed b a hd

/-- Law-by-law right-inverse equivalence for the canonical split `(decompToFun c, decompInvFun c)`:
    `RightInv (decompToFun c) (decompInvFun c)` holds if and only if `DecEnc c` holds. -/
theorem rightInv_decomp_iff_decEnc {A : Type u} {B : Type v} (c : Codec A B) :
    RightInv (decompToFun c) (decompInvFun c) ↔ DecEnc c := by
  constructor
  · intro hr a
    have h := hr (Sum.inl a)
    change decompToFun c (c.enc a) = Sum.inl a at h
    cases hd : c.dec (c.enc a) with
    | none => rw [decompToFun_of_none hd] at h; cases h
    | some a' => rw [decompToFun_of_some hd] at h; cases h; rfl
  · intro hde x
    cases x with
    | inl a => exact decompToFun_of_some (hde a)
    | inr j =>
      obtain ⟨b, hb⟩ := j
      exact decompToFun_of_none hb

/-- Exact canonical decomposition characterization: `(decompToFun c, decompInvFun c)`
    is a two-sided equivalence (`IsEquiv`, witnessing `B ≃ A ⊕ Junk c`) if and only if
    `c` satisfies both `DecEnc c` and `EncDec c`. -/
theorem decomp_isEquiv_iff_lawful {A : Type u} {B : Type v} (c : Codec A B) :
    IsEquiv (decompToFun c) (decompInvFun c) ↔ (DecEnc c ∧ EncDec c) := by
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨(rightInv_decomp_iff_decEnc c).mp hr, (leftInv_decomp_iff_encDec c).mp hl⟩
  · rintro ⟨hde, hed⟩
    exact ⟨(leftInv_decomp_iff_encDec c).mpr hed, (rightInv_decomp_iff_decEnc c).mpr hde⟩

/-- Reverse prism construction and complement identification: any pair of mutual inverses
    `f : B → A ⊕ C` and `g : A ⊕ C → B` induces a lawful codec `codecOfSplit f g`,
    identifies `C` bijectively with `Junk (codecOfSplit f g)` via `g ∘ Sum.inr` and
    `junkToC f g`, and agrees with `decompToFun (codecOfSplit f g)` under that identification. -/
theorem decomp_induces_lawful_and_complement {A : Type u} {B : Type v} {C : Type w}
    (f : B → A ⊕ C) (g : A ⊕ C → B)
    (hl : LeftInv f g) (hr : RightInv f g) :
    DecEnc (codecOfSplit f g) ∧
    EncDec (codecOfSplit f g) ∧
    (∀ k : C, (codecOfSplit f g).dec (g (Sum.inr k)) = none) ∧
    (∀ j : Junk (codecOfSplit f g), g (Sum.inr (junkToC f g j)) = j.1) ∧
    (∀ (k : C) (hj : (codecOfSplit f g).dec (g (Sum.inr k)) = none),
      junkToC f g ⟨g (Sum.inr k), hj⟩ = k) ∧
    (∀ b : B,
      Sum.map id Subtype.val (decompToFun (codecOfSplit f g) b) =
      Sum.map id (fun k => g (Sum.inr k)) (f b)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    show inlMatcher (f (g (Sum.inl a))) = some a
    rw [hr]; rfl
  · intro b a h
    change inlMatcher (f b) = some a at h
    show g (Sum.inl a) = b
    cases hf : f b with
    | inl a' => rw [hf] at h; cases h; rw [← hf, hl]
    | inr k => rw [hf] at h; cases h
  · intro k
    show inlMatcher (f (g (Sum.inr k))) = none
    rw [hr]; rfl
  · intro j
    rw [← junkToC_spec' f g j, hl]
  · intro k hj
    have hs := junkToC_spec' f g ⟨g (Sum.inr k), hj⟩
    rw [hr] at hs
    exact (Sum.inr.inj hs).symm
  · intro b
    cases hf : f b with
    | inl a =>
      have hd : (codecOfSplit f g).dec b = some a := by
        show inlMatcher (f b) = some a
        rw [hf]; rfl
      rw [decompToFun_of_some hd]; rfl
    | inr k =>
      have hd : (codecOfSplit f g).dec b = none := by
        show inlMatcher (f b) = none
        rw [hf]; rfl
      rw [decompToFun_of_none hd]
      show Sum.inr b = Sum.inr (g (Sum.inr k))
      rw [← hf, hl]

/-- Witness-carrying intertwining law for `complementEquivOfCodecEq`: when two mutually
    inverse splits `(f₁, g₁)` and `(f₂, g₂)` induce equal codecs, the explicit equivalence
    `complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq : Equiv C₁ C₂` intertwines
    `f₁` and `f₂`. -/
theorem complementEquivOfCodecEq_intertwines
    {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂}
    (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B)
    (f₂ : B → A ⊕ C₂) (g₂ : A ⊕ C₂ → B)
    (hl₁ : LeftInv f₁ g₁) (hr₁ : RightInv f₁ g₁)
    (hl₂ : LeftInv f₂ g₂) (hr₂ : RightInv f₂ g₂)
    (heq : codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂) :
    ∀ b : B, f₂ b =
      Sum.map id (complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq).toFun (f₁ b) := by
  intro b
  have hdec : ∀ x, inlMatcher (f₁ x) = inlMatcher (f₂ x) :=
    fun x => congrFun (congrArg Codec.dec heq) x
  cases hf : f₁ b with
  | inl a =>
    have h1 := hdec b
    rw [hf] at h1
    cases hf2 : f₂ b with
    | inl a' => rw [hf2] at h1; cases h1; rfl
    | inr k => rw [hf2] at h1; cases h1
  | inr k =>
    have hj : (codecOfSplit f₂ g₂).dec (g₁ (Sum.inr k)) = none := by
      have h1 := hdec (g₁ (Sum.inr k))
      rw [hr₁] at h1
      exact h1.symm
    have hb : g₁ (Sum.inr k) = b := by rw [← hf]; exact hl₁ b
    have hs := junkToC_spec' f₂ g₂ ⟨g₁ (Sum.inr k), hj⟩
    show f₂ b = Sum.inr ((complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq).toFun k)
    rw [← hb]
    exact hs

/-- Exact correspondence modulo intertwining complement equivalence: two mutually inverse
    coproduct decompositions `(f₁, g₁)` of `B` as `A ⊕ C₁` and `(f₂, g₂)` of `B` as `A ⊕ C₂`
    induce the same codec if and only if there exists an equivalence `φ : Equiv C₁ C₂`
    intertwining `f₁` and `f₂`. -/
theorem codecOfSplit_eq_iff_exists_intertwining_equiv
    {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂}
    (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B)
    (f₂ : B → A ⊕ C₂) (g₂ : A ⊕ C₂ → B)
    (hl₁ : LeftInv f₁ g₁) (hr₁ : RightInv f₁ g₁)
    (hl₂ : LeftInv f₂ g₂) (hr₂ : RightInv f₂ g₂) :
    codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂ ↔
      ∃ (φ : Equiv C₁ C₂), ∀ b : B, f₂ b = Sum.map id φ.toFun (f₁ b) := by
  constructor
  · intro heq
    exact ⟨complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq,
      complementEquivOfCodecEq_intertwines f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq⟩
  · rintro ⟨φ, hφ⟩
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

end Toy.Codec
