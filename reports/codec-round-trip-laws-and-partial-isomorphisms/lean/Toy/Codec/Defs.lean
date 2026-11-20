/-!
# Core definitions for codec round-trip laws and partial isomorphisms

This module defines:
- Structural inverse predicates (`LeftInv`, `RightInv`, `IsEquiv`) and bundled
  equivalences (`Equiv`) without external library dependencies.
- Total-encoder / partial-decoder codecs (`Codec`), their separate laws
  (`DecEnc`, `EncDec`, `DecInj`, `Lawful`), and the re-encode-and-compare
  canonicalization wrapper (`canonicalize`).
- Classical (`classicalDec`, `classicalCodec`) and constructive
  (`FiberSplit`, `codecOfFiberSplit`, `fiberSplitOfLawful`) inverse constructions.
- Codec combinators (`Codec.id`, `Codec.comp`, `Codec.prod`, `Codec.sum`).
- Framed codecs over token lists (`FramedCodec`), their prefix laws
  (`PrefixDecEnc`, `PrefixEncDec`), heterogeneous sequencing (`FramedCodec.seq`),
  codeword properties (`PrefixFree`, `ImagePrefixFree`, `NonEmptyEnc`), and the
  induced whole-input list codec (`encList`, `decList`, `listCodec`).
- Coproduct complement decompositions (`Junk`, `inlMatcher`, `decompToFun`,
  `decompInvFun`, `codecOfSplit`, `junkToC`, `complementEquivOfCodecEq`)
  characterizing monomorphic lawful codecs via splits `B ≃ A ⊕ C`.
-/

namespace Toy.Codec

universe u v w w₁ w₂ u₁ u₂ v₁ v₂

/-! ## Equivalences and inverse predicates -/

/-- `g` is a left inverse of `f`: applying `g` after `f` recovers every input.
    Captures total lossless round-tripping for a pair of total maps. -/
def LeftInv {α : Type u} {β : Type v} (f : α → β) (g : β → α) : Prop :=
  ∀ a : α, g (f a) = a

/-- `g` is a right inverse of `f`: applying `f` after `g` recovers every output.
    Captures reverse section-retraction behavior for a pair of total maps. -/
def RightInv {α : Type u} {β : Type v} (f : α → β) (g : β → α) : Prop :=
  ∀ b : β, f (g b) = b

/-- `f` and `g` are mutual two-sided inverses, witnessing a bijection between `α` and `β`. -/
def IsEquiv {α : Type u} {β : Type v} (f : α → β) (g : β → α) : Prop :=
  LeftInv f g ∧ RightInv f g

/-- A bundled equivalence (bijection with explicit inverse maps) between `α` and `β`. -/
structure Equiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : LeftInv toFun invFun
  right_inv : RightInv toFun invFun

/-! ## Plain codecs and round-trip laws -/

/-- A codec between source values `A` and wire/representation values `B`:
    a total encoder `enc : A → B` paired with a fallible decoder `dec : B → Option A`.
    Models serialization frameworks (and monomorphic concrete prisms) where every
    source value has an encoding while malformed wire inputs are rejected (`none`). -/
structure Codec (A : Type u) (B : Type v) where
  enc : A → B
  dec : B → Option A

/-- Extensionality for `Codec`: two codecs are equal iff they agree on `enc` and `dec`. -/
theorem Codec.ext {A : Type u} {B : Type v} {c₁ c₂ : Codec A B}
    (henc : c₁.enc = c₂.enc) (hdec : c₁.dec = c₂.dec) : c₁ = c₂ := by
  cases c₁; cases c₂; cases henc; cases hdec; rfl

/-- Decode-after-encode round-trip law (called parser correctness in EverParse §2.1,
    `serializer_correct` in LowParse, `pcancel` in SSReflect, and the first prism law):
    every encoded source value decodes back to itself. -/
def DecEnc {A : Type u} {B : Type v} (c : Codec A B) : Prop :=
  ∀ a : A, c.dec (c.enc a) = some a

/-- Encode-after-decode round-trip law (canonicality; called `serializer_complete` in
    LowParse, `ocancel` in SSReflect, and the second prism law):
    any representation accepted by `dec` must equal the encoding of the decoded value. -/
def EncDec {A : Type u} {B : Type v} (c : Codec A B) : Prop :=
  ∀ (b : B) (a : A), c.dec b = some a → c.enc a = b

/-- Whole-input decoder injectivity on accepted representations (called non-malleability
    in EverParse §2.1): at most one wire representation decodes to any given source value. -/
def DecInj {A : Type u} {B : Type v} (c : Codec A B) : Prop :=
  ∀ (b₁ b₂ : B) (a : A), c.dec b₁ = some a → c.dec b₂ = some a → b₁ = b₂

/-- Conjunction of both codec round-trip laws (`DecEnc` and `EncDec`). -/
def Lawful {A : Type u} {B : Type v} (c : Codec A B) : Prop :=
  DecEnc c ∧ EncDec c

/-- Re-encode-and-compare canonicalization wrapper (cf. Mathlib `Encodable.decode₂`):
    when the wire type `B` has decidable equality, wraps `c.dec` so that a decoded
    candidate `a` is accepted only when `c.enc a = b`, rejecting non-canonical inputs. -/
def canonicalize {A : Type u} {B : Type v} [DecidableEq B] (c : Codec A B) : Codec A B where
  enc := c.enc
  dec b :=
    match c.dec b with
    | some a => if c.enc a = b then some a else none
    | none => none

/-! ## Classical and constructive inverse decoders for an encoder -/

/-- Classical inverse decoder for an arbitrary encoder `f : A → B`
    (cf. Mathlib `Function.partialInv`): decides membership in the image of `f` via
    `Classical.propDecidable` and selects a preimage via `Classical.choose`. -/
noncomputable def classicalDec {A : Type u} {B : Type v} (f : A → B) (b : B) : Option A :=
  haveI : Decidable (∃ a : A, f a = b) := Classical.propDecidable _
  if h : ∃ a : A, f a = b then some (Classical.choose h) else none

/-- Classical codec constructed from an encoder `f : A → B` by pairing it with
    `classicalDec f`. -/
noncomputable def classicalCodec {A : Type u} {B : Type v} (f : A → B) : Codec A B where
  enc := f
  dec := classicalDec f

/-- Constructive decidable-fiber splitter for `f : A → B` (cf. `is-decidable-map` in
    dependent type theory): for every `b : B`, explicitly produces either a preimage
    `{ a : A // f a = b }` or a proof that `b` lies outside the image of `f`.
    Captures the constructive data equivalent to a lawful decoder for an injection. -/
def FiberSplit {A : Type u} {B : Type v} (f : A → B) : Type (max u v) :=
  ∀ b : B, PSum { a : A // f a = b } (∀ a : A, f a ≠ b)

/-- Computable codec obtained from an encoder `f : A → B` and a constructive
    `FiberSplit f`, without using classical choice. -/
def codecOfFiberSplit {A : Type u} {B : Type v} (f : A → B) (s : FiberSplit f) : Codec A B where
  enc := f
  dec b :=
    match s b with
    | PSum.inl ⟨a, _⟩ => some a
    | PSum.inr _ => none

/-- Constructive `FiberSplit` extracted from any lawful codec `c : Codec A B`:
    maps accepted wire values `c.dec b = some a` to `PSum.inl ⟨a, hed b a h⟩` and
    rejected wire values `c.dec b = none` to `PSum.inr _`. Uses zero axioms. -/
def fiberSplitOfLawful {A : Type u} {B : Type v} (c : Codec A B)
    (hde : DecEnc c) (hed : EncDec c) : FiberSplit c.enc := fun b =>
  match h : c.dec b with
  | some a => PSum.inl ⟨a, hed b a h⟩
  | none => PSum.inr (fun a ha => by
      have h1 := hde a
      rw [ha, h] at h1
      cases h1)

/-! ## Codec combinators -/

/-- Identity codec on `A`. -/
def Codec.id (A : Type u) : Codec A A where
  enc a := a
  dec a := some a

/-- Sequential composition of codecs `A → B` and `B → C`:
    encodes through `c₁` then `c₂`, and decodes through `c₂` then `c₁` via `Option.bind`. -/
def Codec.comp {A : Type u} {B : Type v} {C : Type w}
    (c₁ : Codec A B) (c₂ : Codec B C) : Codec A C where
  enc a := c₂.enc (c₁.enc a)
  dec c := (c₂.dec c).bind c₁.dec

/-- Product (pair) combinator for codecs:
    encodes each component independently into `B₁ × B₂` and succeeds on decoding
    only when both component decoders succeed. -/
def Codec.prod {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
    (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂) : Codec (A₁ × A₂) (B₁ × B₂) where
  enc p := (c₁.enc p.1, c₂.enc p.2)
  dec p :=
    match c₁.dec p.1, c₂.dec p.2 with
    | some a₁, some a₂ => some (a₁, a₂)
    | _, _ => none

/-- Sum (tagged union) combinator for codecs:
    preserves the branch tag in `B₁ ⊕ B₂` on encoding and decodes each branch with
    its corresponding component decoder. -/
def Codec.sum {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
    (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂) : Codec (A₁ ⊕ A₂) (B₁ ⊕ B₂) where
  enc
    | Sum.inl a₁ => Sum.inl (c₁.enc a₁)
    | Sum.inr a₂ => Sum.inr (c₂.enc a₂)
  dec
    | Sum.inl b₁ => (c₁.dec b₁).map Sum.inl
    | Sum.inr b₂ => (c₂.dec b₂).map Sum.inr

/-! ## Framed codecs over token lists -/

/-- A framed (streaming/prefix) codec over token lists `List β`:
    `enc` serializes a value to a token sequence and `decPrefix` parses a single
    leading value together with the unconsumed remainder of the stream. -/
structure FramedCodec (A : Type u) (β : Type v) where
  enc : A → List β
  decPrefix : List β → Option (A × List β)

/-- Prefix decode-after-encode law (Vytiniotis–Kennedy Lemma 1; Narcissus Definition 3.1):
    `decPrefix` recovers `a` and the exact trailing stream `rest` from `enc a ++ rest`,
    regardless of what tokens follow in `rest`. -/
def PrefixDecEnc {A : Type u} {β : Type v} (fc : FramedCodec A β) : Prop :=
  ∀ (a : A) (rest : List β), fc.decPrefix (fc.enc a ++ rest) = some (a, rest)

/-- Prefix encode-after-decode law (converse / framed canonicality; Vytiniotis–Kennedy
    Lemma 3): whenever `decPrefix xs` yields `(a, rest)`, the input stream equals
    `enc a ++ rest`. -/
def PrefixEncDec {A : Type u} {β : Type v} (fc : FramedCodec A β) : Prop :=
  ∀ (xs : List β) (a : A) (rest : List β), fc.decPrefix xs = some (a, rest) → xs = fc.enc a ++ rest

/-- Heterogeneous sequential concatenation of two framed codecs over the same token
    type `β`: encodes `(a₁, a₂)` by concatenating `fc₁.enc a₁ ++ fc₂.enc a₂`, and
    decodes by running `fc₁.decPrefix` followed by `fc₂.decPrefix` on the remainder. -/
def FramedCodec.seq {A₁ : Type u₁} {A₂ : Type u₂} {β : Type v}
    (fc₁ : FramedCodec A₁ β) (fc₂ : FramedCodec A₂ β) :
    FramedCodec (A₁ × A₂) β where
  enc p := fc₁.enc p.1 ++ fc₂.enc p.2
  decPrefix xs :=
    match fc₁.decPrefix xs with
    | none => none
    | some (a₁, rest₁) =>
      match fc₂.decPrefix rest₁ with
      | none => none
      | some (a₂, rest₂) => some ((a₁, a₂), rest₂)

/-- Indexed prefix-freeness of an encoding into token lists (Vytiniotis–Kennedy
    Corollary 2): whenever `enc a₁ ++ s = enc a₂`, `a₁ = a₂`.
    Note: setting `s = []` specializes this condition to `Function.Injective enc`, so
    `PrefixFree enc` is equivalent to `Function.Injective enc ∧ ImagePrefixFree enc`. -/
def PrefixFree {A : Type u} {β : Type v} (enc : A → List β) : Prop :=
  ∀ (a₁ a₂ : A) (s : List β), enc a₁ ++ s = enc a₂ → a₁ = a₂

/-- Set-level (image) prefix-freeness of an encoding: no codeword in the image of `enc`
    is a proper prefix (`s ≠ []`) of any codeword in the image of `enc`
    (cf. Mathlib `InformationTheory.IsPrefixFree` on `Set.range enc`). Unlike
    `PrefixFree`, a non-injective constant encoding satisfies `ImagePrefixFree`. -/
def ImagePrefixFree {A : Type u} {β : Type v} (enc : A → List β) : Prop :=
  ∀ (a₁ a₂ : A) (s : List β), enc a₁ ++ s = enc a₂ → s = []

/-- Non-empty codeword condition:
    every encoded value occupies at least one token (`enc a ≠ []`).
    Necessary for `DecEnc (listCodec fc)` because an empty codeword makes
    `encList enc [] = encList enc [a]`; under `PrefixDecEnc` or `PrefixFree`,
    `NonEmptyEnc` can fail only when `A` is a subsingleton. -/
def NonEmptyEnc {A : Type u} {β : Type v} (enc : A → List β) : Prop :=
  ∀ a : A, enc a ≠ []

/-- List encoder obtained by concatenating individual encodings in order. -/
def encList {A : Type u} {β : Type v} (enc : A → List β) : List A → List β
  | [] => []
  | a :: as => enc a ++ encList enc as

/-- Whole-input list decoder obtained by repeatedly running `fc.decPrefix` until the
    stream is exhausted, rejecting any non-progressing step (`rest.length ≥ xs.length`)
    to ensure termination on arbitrary framed codecs (cf. LowParse `parse_list_aux`). -/
def decList {A : Type u} {β : Type v} (fc : FramedCodec A β) (xs : List β) : Option (List A) :=
  match xs with
  | [] => some []
  | b :: bs =>
    match fc.decPrefix (b :: bs) with
    | none => none
    | some (a, rest) =>
      if _h : rest.length < (b :: bs).length then
        (decList fc rest).map (a :: ·)
      else
        none
termination_by xs.length

/-- The whole-input list codec induced by a framed codec: concatenation on encode,
    repeated prefix decoding until exhaustion on decode. -/
def listCodec {A : Type u} {β : Type v} (fc : FramedCodec A β) : Codec (List A) (List β) where
  enc := encList fc.enc
  dec := decList fc

/-! ## Prisms and coproduct complement decompositions -/

/-- The junk (rejected wire values) of a codec `c : Codec A B`:
    the subtype of representations on which `c.dec` returns `none`. -/
def Junk {A : Type u} {B : Type v} (c : Codec A B) : Type v :=
  { b : B // c.dec b = none }

/-- Canonical `Sum.inl` matcher on a coproduct `A ⊕ C`:
    returns `some a` on `Sum.inl a` and `none` on `Sum.inr _`. -/
def inlMatcher {A : Type u} {C : Type w} : A ⊕ C → Option A
  | Sum.inl a => some a
  | Sum.inr _ => none

/-- Forward map of the canonical decomposition `B → A ⊕ Junk c` induced by a codec `c`:
    valid representations go to `Sum.inl a`, rejected ones to `Sum.inr ⟨b, h⟩`. -/
def decompToFun {A : Type u} {B : Type v} (c : Codec A B) (b : B) : A ⊕ Junk c :=
  match h : c.dec b with
  | some a => Sum.inl a
  | none => Sum.inr ⟨b, h⟩

/-- Backward map of the canonical decomposition `A ⊕ Junk c → B` induced by a codec `c`:
    embeds `A` via `c.enc` and embeds `Junk c` via `Subtype.val`. -/
def decompInvFun {A : Type u} {B : Type v} (c : Codec A B) : A ⊕ Junk c → B
  | Sum.inl a => c.enc a
  | Sum.inr ⟨b, _⟩ => b

/-- Codec induced by a pair of split maps `f : B → A ⊕ C` and `g : A ⊕ C → B`:
    encodes via `g ∘ Sum.inl` and decodes via `inlMatcher ∘ f`. -/
def codecOfSplit {A : Type u} {B : Type v} {C : Type w}
    (f : B → A ⊕ C) (g : A ⊕ C → B) : Codec A B where
  enc a := g (Sum.inl a)
  dec b := inlMatcher (f b)

/-- Extracts the complement witness in `C` from a junk element of `codecOfSplit f g`. -/
def junkToC {A : Type u} {B : Type v} {C : Type w}
    (f : B → A ⊕ C) (g : A ⊕ C → B) (j : Junk (codecOfSplit f g)) : C :=
  match h : f j.1 with
  | Sum.inl a =>
    absurd (by
      have hj := j.2
      change inlMatcher (f j.1) = none at hj
      rw [h] at hj
      exact hj) (by intro h'; cases h')
  | Sum.inr k => k

private theorem junkToC_spec {A : Type u} {B : Type v} {C : Type w}
    (f : B → A ⊕ C) (g : A ⊕ C → B) (j : Junk (codecOfSplit f g)) :
    f j.1 = Sum.inr (junkToC f g j) := by
  have hj : inlMatcher (f j.1) = none := j.2
  unfold junkToC
  split
  · rename_i a h
    rw [h] at hj
    cases hj
  · rename_i k h
    exact h

/-- Explicit complement equivalence `Equiv C₁ C₂` extracted from two mutually inverse
    coproduct decompositions `(f₁, g₁)` and `(f₂, g₂)` that induce equal codecs
    `codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂`. Transports `C₁` to `C₂` through `B`
    and `junkToC` without classical choice. -/
def complementEquivOfCodecEq
    {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂}
    (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B)
    (f₂ : B → A ⊕ C₂) (g₂ : A ⊕ C₂ → B)
    (hl₁ : LeftInv f₁ g₁) (hr₁ : RightInv f₁ g₁)
    (hl₂ : LeftInv f₂ g₂) (hr₂ : RightInv f₂ g₂)
    (heq : codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂) : Equiv C₁ C₂ :=
  let hdec : ∀ b, inlMatcher (f₁ b) = inlMatcher (f₂ b) :=
    fun b => congrFun (congrArg Codec.dec heq) b
  let pf₂ : ∀ k : C₁, (codecOfSplit f₂ g₂).dec (g₁ (Sum.inr k)) = none := fun k => by
    have h1 := hdec (g₁ (Sum.inr k))
    rw [hr₁] at h1
    exact h1.symm
  let pf₁ : ∀ k : C₂, (codecOfSplit f₁ g₁).dec (g₂ (Sum.inr k)) = none := fun k => by
    have h1 := hdec (g₂ (Sum.inr k))
    rw [hr₂] at h1
    exact h1
  let toF : C₁ → C₂ := fun k => junkToC f₂ g₂ ⟨g₁ (Sum.inr k), pf₂ k⟩
  let invF : C₂ → C₁ := fun k => junkToC f₁ g₁ ⟨g₂ (Sum.inr k), pf₁ k⟩
  { toFun := toF
    invFun := invF
    left_inv := fun k => by
      have e1 : f₁ (g₂ (Sum.inr (toF k))) = Sum.inr (invF (toF k)) :=
        junkToC_spec f₁ g₁ ⟨g₂ (Sum.inr (toF k)), pf₁ (toF k)⟩
      have hφ : f₂ (g₁ (Sum.inr k)) = Sum.inr (toF k) :=
        junkToC_spec f₂ g₂ ⟨g₁ (Sum.inr k), pf₂ k⟩
      have e2 : g₂ (Sum.inr (toF k)) = g₁ (Sum.inr k) := by
        rw [← hφ]; exact hl₂ _
      rw [e2, hr₁] at e1
      exact (Sum.inr.inj e1).symm
    right_inv := fun k => by
      have e1 : f₂ (g₁ (Sum.inr (invF k))) = Sum.inr (toF (invF k)) :=
        junkToC_spec f₂ g₂ ⟨g₁ (Sum.inr (invF k)), pf₂ (invF k)⟩
      have hψ : f₁ (g₂ (Sum.inr k)) = Sum.inr (invF k) :=
        junkToC_spec f₁ g₁ ⟨g₂ (Sum.inr k), pf₁ k⟩
      have e2 : g₁ (Sum.inr (invF k)) = g₂ (Sum.inr k) := by
        rw [← hψ]; exact hl₁ _
      rw [e2, hr₂] at e1
      exact (Sum.inr.inj e1).symm }

end Toy.Codec
