# Codec Round-Trip Laws and Partial Isomorphisms in Lean 4

## Summary

This package is a kernel-checked Lean 4 toy model (namespace `Toy.Codec`) of total-encoder, fallible-decoder codecs (`enc : A → B`, `dec : B → Option A`), framed prefix codecs over token lists (`enc : A → List β`, `decPrefix : List β → Option (A × List β)`), and monomorphic coproduct complement decompositions (`B ≃ A ⊕ C`). It separates the decode-after-encode law `DecEnc` (`dec (enc a) = some a`), the encode-after-decode canonicality law `EncDec` (`dec b = some a → enc a = b`), and whole-input decoder injectivity `DecInj` (`dec b₁ = some a → dec b₂ = some a → b₁ = b₂`), characterizes lawful codecs classically (bijection with injections `A → B`), constructively (decidable fibers `FiberSplit`), and categorically (`B ≃ A ⊕ C` modulo intertwining complement equivalence), and pins down the prefix-framing and non-emptiness requirements for list concatenation.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

One-sentence summary of each result (every Lean statement, hypothesis ledger, and modeling bridge is in **Findings**):

1. **`decEnc_imp_enc_injective`** (T0, theorem): For any codec c : Codec A B, the decode-after-encode round-trip law DecEnc c alone implies that the encoder c.enc is injective (EncDec c is not required).
2. **`lawful_iff_dec_eq_some_iff`** (T0, characterization): For any codec c : Codec A B, satisfying both DecEnc c and EncDec c is equivalent to c.dec having the converse graph of c.enc (∀ b a, c.dec b = some a ↔ c.enc a = b); as a hypothesis-minimality corollary (decEqSomeIff_imp_enc_injective, reference point), that converse-graph condition alone implies Function.Injective c.enc.
3. **`lawful_iff_decEnc_and_decInj`** (T0, characterization): For any codec c : Codec A B, satisfying DecEnc c and EncDec c is equivalent to satisfying DecEnc c and whole-input decoder injectivity DecInj c (at most one wire representation decodes to each source value).
4. **`dec_unique_of_lawful`** (T0, theorem): If two codecs c₁ c₂ : Codec A B share the same encoder (c₁.enc = c₂.enc) and both satisfy DecEnc and EncDec, then they have the same decoder (c₁.dec = c₂.dec), without Classical.choice (using function extensionality; established by the kernel axiom record: [Quot.sound]).
5. **`classicalCodec_bijection`** (T0, characterization): Classically (via Classical.choice), classicalCodec f satisfies DecEnc for every injective f : A → B (classicalCodec_decEnc_of_injective) and satisfies EncDec unconditionally for every f (classicalCodec_encDec, reference-point companion), while classicalCodec c.enc = c holds for every codec satisfying DecEnc c and EncDec c (classicalCodec_recover_of_lawful); together with decEnc_imp_enc_injective and the definitional equality classicalCodec_enc ((classicalCodec f).enc = f), these five named declarations establish a bijection between lawful codecs A ⇄ B and injections A → B.
6. **`codecOfFiberSplit_correspondence`** (T0, characterization): Constructively (without Classical.choice, established by the kernel axiom record: no axioms for codecOfFiberSplit_decEnc_of_injective, codecOfFiberSplit_encDec, and fiberSplitOfLawful; [Quot.sound] only for codecOfFiberSplit_eq_of_lawful), any injection f : A → B equipped with a decidable-fiber witness s : FiberSplit f yields a computable lawful codec codecOfFiberSplit f s (satisfying DecEnc via codecOfFiberSplit_decEnc_of_injective and EncDec unconditionally via codecOfFiberSplit_encDec); conversely, every lawful codec c constructively yields fiberSplitOfLawful c hde hed : FiberSplit c.enc, and for every s : FiberSplit c.enc, codecOfFiberSplit c.enc s = c (codecOfFiberSplit_eq_of_lawful).
7. **`lawful_dec_isSome_iff_mem_range`** (T0, characterization): For any codec c : Codec A B satisfying DecEnc c and EncDec c, (c.dec b).isSome = true holds if and only if b lies in the image of c.enc (lawful_dec_isSome_iff_mem_range), and—as an immediate negated corollary (junk_iff_not_in_image_of_lawful, definitional via eq_none_iff_of_isSome_iff)—b belongs to Junk c (c.dec b = none) if and only if ∀ a : A, c.enc a ≠ b.
8. **`decEnc_admits_malleable_codec`** (T1, counterexample): Demanding DecEnc alone does not prevent malleability: nonCanonicalBoolCodec : Codec Bool Nat satisfies DecEnc yet violates both EncDec and DecInj because the distinct wire values 1 and 2 both decode to true.
9. **`encDec_admits_always_failing_codec`** (T1, counterexample): Demanding EncDec alone does not prevent vacuous rejection: alwaysFailBoolCodec : Codec Bool Bool satisfies EncDec yet violates DecEnc and returns none on every wire input.
10. **`canonicalize_decEnc_of_decEnc`** (T0, theorem): Given a [DecidableEq B] instance on the wire type B (always available classically, and needed computably for an executable wrapper), wrapping any codec c : Codec A B satisfying DecEnc c in the re-encode-and-compare check canonicalize c preserves DecEnc (canonicalize_decEnc_of_decEnc) while guaranteeing EncDec (canonicalize c) unconditionally (canonicalize_encDec) with the identical encoder c.enc.
11. **`combinator_closure_decEnc_and_encDec`** (T0, theorem): Each round-trip law (DecEnc and EncDec) is preserved independently of the other under sequential Kleisli composition c₁.comp c₂ (comp_decEnc, comp_encDec), componentwise products c₁.prod c₂ over B₁ × B₂ (prod_decEnc, prod_encDec), and tagged sums c₁.sum c₂ over B₁ ⊕ B₂ (sum_decEnc, sum_encDec); consequently, lawful codecs are closed under all three combinators.
12. **`framed_lawful_iff_decPrefix_eq_some_iff`** (T0, characterization): For any framed codec fc : FramedCodec A β, satisfying both PrefixDecEnc fc and PrefixEncDec fc is equivalent to fc.decPrefix xs = some (a, rest) holding if and only if xs = fc.enc a ++ rest.
13. **`prefixDecEnc_imp_prefixFree`** (T0, theorem): For any framed codec fc : FramedCodec A β, the prefix round-trip law PrefixDecEnc fc alone implies PrefixFree fc.enc: fc.enc is injective and no codeword is a prefix of another distinct value's codeword.
14. **`framed_seq_closure`** (T0, theorem): For any framed codecs fc₁ : FramedCodec A₁ β and fc₂ : FramedCodec A₂ β over a shared token type β, their sequential concatenation fc₁.seq fc₂ : FramedCodec (A₁ × A₂) β preserves PrefixDecEnc when both factors satisfy PrefixDecEnc (seq_prefixDecEnc) and preserves PrefixEncDec when both factors satisfy PrefixEncDec (seq_prefixEncDec), requiring neither the opposite law nor NonEmptyEnc.
15. **`listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc`** (T0, characterization): For any framed codec fc : FramedCodec A β satisfying PrefixDecEnc fc, the induced whole-input list codec listCodec fc satisfies DecEnc if and only if every codeword is non-empty (NonEmptyEnc fc.enc); moreover, when A has two distinct elements, NonEmptyEnc fc.enc follows automatically from PrefixDecEnc fc (nonEmptyEnc_of_prefixDecEnc_of_ne).
16. **`listCodec_encDec_of_prefixEncDec`** (T0, theorem): For any framed codec fc : FramedCodec A β satisfying the converse prefix law PrefixEncDec fc, the concatenated whole-input list codec listCodec fc satisfies EncDec (requiring neither PrefixDecEnc nor NonEmptyEnc).
17. **`lawful_injective_nonEmpty_enc_admits_ambiguous_concat`** (T1, counterexample): Single-value lawfulness with an injective, non-empty encoding admits ambiguous concatenation: ambiguousCodec : Codec Bool (List Bool) (false ↦ [false], true ↦ [false, false]) satisfies DecEnc, EncDec, Function.Injective enc, and NonEmptyEnc, yet violates PrefixFree and maps the distinct lists [false, false] and [true] to the same concatenation [false, false], ruling out any DecEnc list decoder.
18. **`decomp_isEquiv_iff_lawful`** (T1, characterization): For any codec c : Codec A B, the specific canonical split maps decompToFun c : B → A ⊕ Junk c and decompInvFun c : A ⊕ Junk c → B satisfy LeftInv if and only if EncDec c holds (leftInv_decomp_iff_encDec), satisfy RightInv if and only if DecEnc c holds (rightInv_decomp_iff_decEnc), and therefore form mutual two-sided inverses (IsEquiv (decompToFun c) (decompInvFun c)) if and only if DecEnc c ∧ EncDec c holds (decomp_isEquiv_iff_lawful, without Classical.choice; by contrast, the bare existence of some non-canonical equivalence Equiv B (A ⊕ Junk c) does not make c lawful, as proved for nonCanonicalBoolCodec by nonCanonicalBoolCodec_not_encDec_yet_admits_equiv; axiom qualifiers established by the kernel axiom record: no axioms for decomp_isEquiv_iff_lawful, leftInv_decomp_iff_encDec, and rightInv_decomp_iff_decEnc, and [propext] without Classical.choice for nonCanonicalBoolCodec_not_encDec_yet_admits_equiv).
19. **`decomp_induces_lawful_and_complement`** (T0, theorem): For any mutual inverses f : B → A ⊕ C and g : A ⊕ C → B (LeftInv f g and RightInv f g), the induced codec codecOfSplit f g satisfies DecEnc and EncDec, g ∘ Sum.inr maps C into Junk (codecOfSplit f g) as a two-sided inverse to junkToC f g, and f agrees with decompToFun (codecOfSplit f g) under this identification (without Classical.choice; established by the kernel axiom record: no axioms).
20. **`codecOfSplit_eq_iff_exists_intertwining_equiv`** (T1, characterization): Given two mutually inverse coproduct decompositions (f₁, g₁) of B as A ⊕ C₁ and (f₂, g₂) of B as A ⊕ C₂, they induce the same codec (codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂) if and only if there exists an equivalence φ : Equiv C₁ C₂ intertwining them (∀ b, f₂ b = Sum.map id φ.toFun (f₁ b)); moreover, when the codecs are equal, complementEquivOfCodecEq constructs that Equiv C₁ C₂ in Type with zero axioms and complementEquivOfCodecEq_intertwines proves the intertwining equation (axiom qualifiers established by the kernel axiom record: [Quot.sound] for codecOfSplit_eq_iff_exists_intertwining_equiv, and no axioms for complementEquivOfCodecEq and complementEquivOfCodecEq_intertwines).

**Non-claims come first under Boundaries.** Before applying any result to a real parser, serializer, relational wire format, or lens/prism abstraction, read **Applicability** and the package-wide and per-result non-claims in **Boundaries**. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real parsers and serializers (such as EverParse/LowParse, Narcissus, and encoder/decoder combinator libraries), relational wire formats, or prism and lens libraries (such as the Isabelle AFP `Optics` prisms and Haskell `lens`); the modeling-bridge statements under **Findings** argue the connection separately.

## Applicability

**Model fidelity: this is a toy model.** All definitions live in the Lean 4 namespace `Toy.Codec` (`lean/Toy/Codec/Defs.lean`) and are written from scratch without mirroring any production codebase. They model pure serialization/deserialization specifications (such as EverParse/LowParse, Narcissus, and encoder/decoder combinator libraries) and monomorphic concrete prisms (`match`/`build` pairs). Known gaps between this model and real systems:

- **Implementation boundary:** The model has no byte layouts, bit-packing, lengths, endianness, mutable state, streaming I/O, panic/exception paths, resource bounds, or error reporting. Nothing here is a security property of an implemented parser.
- **Single-encoder relational boundary:** The laws are stated for one deterministic encoder function `enc : A → B`. A format that permits several encodings of one value (a format relation rather than a single function, as in Narcissus) cannot satisfy `EncDec` for any single encoder; for such formats the corresponding requirement is that the decoder accepts exactly the strings the format relates to the decoded value. Failing `EncDec` for a chosen encoder is therefore not by itself evidence that malformed input is accepted.
- **Propositional equality:** Every round-trip law uses Lean's propositional equality `=`, not observational equivalence, quotient equality, or equivalence modulo padding/provenance.
- **Computability vs. propositional statements:** Propositional theorems in Lean (such as `lawful_dec_isSome_iff_mem_range` or `canonicalize_decEnc_of_decEnc`) apply equally to noncomputable functions (`classicalCodec f`) and classical `DecidableEq B` instances. Obtaining an executable validator or canonicalizing wrapper requires an executable decoder, a computable `FiberSplit`, or a computable `DecidableEq B` instance.
- **Token streams as finite lists:** `FramedCodec A β` models wire streams as finite lists `List β` with list concatenation `++`, without lazy streams, framing delimiters outside the token alphabet, or bounded-lookahead type signatures.
- **Monomorphic optics and optics-duality boundary:** `Codec A B` matches a monomorphic concrete prism (`s = t = B`, `a = b = A`), not a polymorphic `Prism s t a b`. No statement about lenses is proved in this package. 'Dual to lenses' describes the shape of the result; the lens-side decomposition needs extra assumptions (for instance an inhabited view type).

**Evidence roles.** Every theorem proved in `lean/` carries `Basis: execution (Lean kernel check)`. Every statement connecting a theorem to real parsers, serializers, or optics is recorded separately as `Basis: derived (modeling bridge)` with its reasoning.

### Cross-Literature Terminology Map

| `Toy.Codec` notion | EverParse (§2.1 / §5) | LowParse (`Spec.Base` / `Spec.List`) | Rocq SSReflect / MathComp | Lean Mathlib | Isabelle AFP `Optics` / Haskell `lens` | Vytiniotis–Kennedy / Narcissus |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `DecEnc c` (`dec (enc a) = some a`) | parser *correct* (`p(s(m)) = m`) | `serializer_correct` | `pcancel` (`valK`) | `Encodable.encodek`, `Encoding.decode_encode` | `wb_prism.match_build` / prism law 1 | — / Def. 2.2 clause 1 (relational) |
| `EncDec c` (`dec b = some a → enc a = b`) | implies *non-malleable* (`encDec_imp_decInj`) and accepts only serialized messages (one half of *exact*); does not imply *correct* | `serializer_complete` | `ocancel` (`insubK`) | — (bundled in `IsPartialInv`) | `wb_prism.build_match` / prism law 2 | — / Def. 2.2 clause 2 (relational) |
| `DecEnc c ∧ EncDec c` (`Lawful c`) | *correct* + *exact* (equivalently, *correct* + *non-malleable*) | `serializer_correct` + `serializer_complete` | `pcancel` + `ocancel` | `Function.IsPartialInv` | `locale wb_prism` (`build_match_iff`) | — |
| `DecInj c` (`dec b₁ = some a → dec b₂ = some a → b₁ = b₂`) | *non-malleable* (whole-input) | `injective` (on consumed slice) | — | — | — | — |
| `(c.dec b).isSome = true ↔ ∃ a, c.enc a = b` | *exact* (`p⁻¹(V) = s(V)`) | — | — | `Encodable.decidableRangeEncode` | `wb_prism.range_build` | — |
| `∀ a, ∃ b, c.dec b = some a` | *complete* (parser surjectivity; **not** `DecEnc`) | — | — | — | — | — |
| `canonicalize c` | — | — | — | `Encodable.decode₂` | — | — |
| `classicalDec f` / `FiberSplit f` | — | — | — | `Function.partialInv` / — | — | (`agda-unimath` `is-decidable-map`) |
| `PrefixDecEnc fc` / `PrefixEncDec fc` | strong prefix property (§5 Def. 2) | `ParserStrong` + `serializer_correct` | — | — | — | Lemma 1 & Lemma 3 / Def. 3.1 |
| `PrefixFree enc` vs. `ImagePrefixFree enc` | — | — | — | — vs. `InformationTheory.IsPrefixFree` | — | Corollary 2 (indexed, bundles `Injective`) |

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`). No Mathlib and no external dependencies: `lean/lakefile.toml` declares a single `[[lean_lib]]` (`Toy`) and no `[[require]]` entries, using core Lean / `Std` only.

**Relationship among the subjects in `REPORT.json`.** The Lean 4 toolchain is the kernel that checked every definition, theorem, counterexample, and witness in `lean/`. The listed directly examined papers and pinned formalization repositories (`leanprover-community/mathlib4`, `isabelle-prover/mirror-afp-2026` (`thys/Optics/Prisms.thy`), `project-everest/everparse`, `rocq-prover/rocq`, `math-comp/math-comp`, `UniMath/agda-unimath`) are primary prior-art sources that classify results as `T0` (re-derivation) or `T1` (folklore or categorical observation made precise); secondary bibliographic citations for which only metadata/abstracts were consulted (Kennedy & Vytiniotis 2012; Foster et al. 2005/2007) are recorded in prose rather than `REPORT.json` `subjects`. This package does not re-check external repositories' proofs. The reading depth for every source is recorded in **Evidence**.

**Proof status.** All 31 theorems in `Toy/Codec/Statements.lean`, all 3 standalone counterexample theorems in `Toy/Codec/Counterexamples.lean`, and every definition example, positive control, tightness counterexample, non-vacuity witness, and supporting lemma (481 non-internal declarations audited in total) are fully proved with zero `sorry` and depend at most on `propext`, `Classical.choice`, and `Quot.sound`.

## Findings

### How to read this section

- Each card presents the Lean `#check` pretty-printed signature captured from the compiled project, the statement quoted verbatim from the cited source lines (`-- file:lines`; proof omitted), and an unfolded elementary statement with core predicates expanded. The unfolded statements are written in theorem syntax and labelled prose; each is definitionally equal to the corresponding Lean theorem (`example : ∀ <binders>, <type> := @<name>` elaborates for each of them). Card 17 quotes its source statement without a separate unfolded form.
- Proof-level axiom qualifiers such as *without `Classical.choice`* or *zero axioms* are not encoded in statement types; they are verified directly by the kernel axiom audit (`audit/axioms.json`, summarized on each card and tabulated in **Evidence**).
- Every theorem carries `Basis: execution (Lean kernel check)`. Claims relating a theorem to real parsers, serializers, or optics appear on a separate `Basis: derived (modeling bridge)` line.
- Depth labels follow one uniform criterion across all 20 cards: `definitional` means true by `rfl` / definitional unfolding alone (such as the companion identity `classicalCodec_enc`), whereas `shallow` means a short non-`rfl` proof by propositional, equality, or case-split reasoning (including Cards 2, 3, and 12).
- Hypothesis ledgers mark every hypothesis of every card theorem and hashed companion `tight` (with a proved counterexample where all remaining hypotheses hold and the conclusion fails) or `harmless` (with justification). On Card 20 (`complementEquivOfCodecEq_intertwines`), all five proof hypotheses (`hl₁`, `hr₁`, `hl₂`, `hr₂`, and `heq`) appear inside the conclusion's term `complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq` and are explicitly marked as structurally required with surrogate counterexamples.
- Every package constant, witness codec, helper map, supporting lemma, definition example, tightness counterexample, and non-vacuity witness named anywhere in the prose is either defined in full in **Core Definitions** / **Witness Definitions and Supporting / Counterexample Declarations** (at the end of **Findings**) or quoted with its kernel `#check` signature.
- Where a signature printed with Lean's default options would not elaborate back to the declaration's statement, it is printed with one added option: `set_option pp.funBinderTypes true` (types of `fun` and `∃` binders shown, as in `∃ (φ : Toy.Codec.Equiv C₁ C₂), …`, which the default prints as `∃ φ, …`), `set_option pp.proofs true` (proof arguments shown instead of `⋯`, as in `⟨true, rfl⟩`), or `set_option pp.analyze true` (implicit arguments that the printed term does not determine shown as named arguments, as in `Toy.Codec.inlMatcher (C := Nat) (Sum.inl true)`). Every card or listing that contains such an entry names it and its option.

### Core Definitions (`lean/Toy/Codec/Defs.lean`)

Every core definition in `Toy.Codec.Defs` is reproduced in full below:

```lean
-- lean/Toy/Codec/Defs.lean:1-361
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
```

### Definition Example Index (`lean/Toy/Codec/Examples.lean` and `Counterexamples.lean`)

| Definition(s) | Captures | Proved positive example(s) | Proved negative example(s) |
| :--- | :--- | :--- | :--- |
| `LeftInv`, `RightInv`, `IsEquiv`, `Equiv` | Two-sided inverse predicates and bundled bijections | `ex_leftInv_pos`, `ex_rightInv_pos`, `ex_isEquiv_pos`, `ex_equiv_pos` | `ex_leftInv_neg`, `ex_rightInv_neg`, `ex_isEquiv_neg`, `ex_equiv_neg` |
| `Codec`, `DecEnc`, `EncDec`, `DecInj`, `Lawful` | Total encoder + fallible decoder and separated round-trip / injectivity laws | `ex_decEnc_pos`, `ex_encDec_pos`, `ex_decInj_pos`, `ex_lawful_pos` | `ex_decEnc_neg`, `ex_encDec_neg`, `ex_decInj_neg`, `ex_lawful_neg_malleable`, `ex_lawful_neg_failing` |
| `canonicalize` | Re-encode-and-compare canonicalization wrapper given `[DecidableEq B]` | `ex_canonicalize_pos` (`nonCanonicalBoolCodec` upgraded, `dec 2 = none`) | `ex_canonicalize_neg` (`alwaysFailBoolCodec` still fails `DecEnc`) |
| `classicalDec`, `classicalCodec` | Noncomputable inverse decoder via `Classical.choice` | `ex_classicalCodec_pos` | `ex_classicalCodec_neg` |
| `FiberSplit`, `codecOfFiberSplit`, `fiberSplitOfLawful` | Constructive decidable-fiber witness equivalent to a lawful decoder | `ex_fiberSplit_pos`, `ex_fiberSplitOfLawful_pos` | `ex_fiberSplit_neg_nonInjective`, `ex_fiberSplitOfLawful_neg` |
| `Codec.id`, `Codec.comp`, `Codec.prod`, `Codec.sum` | Identity, sequential Kleisli composition, structured pairs, tagged sums | `codecId_lawful`, `ex_comp_pos`, `ex_prod_pos`, `ex_sum_pos` | `ex_codecId_ne_boolNot` (`Codec.id Bool ≠ boolNotCodec ∧ Codec.id Bool ≠ alwaysFailBoolCodec`), `ex_comp_neg`, `ex_prod_neg`, `ex_sum_neg` |
| `FramedCodec`, `PrefixDecEnc`, `PrefixEncDec`, `FramedCodec.seq` | Streaming prefix codecs and heterogeneous flat-stream record sequencing | `ex_prefixDecEnc_pos`, `ex_prefixEncDec_pos`, `ex_seq_pos` | `ex_prefixDecEnc_neg`, `ex_prefixEncDec_neg`, `ex_seq_neg` |
| `PrefixFree`, `ImagePrefixFree`, `NonEmptyEnc` | Indexed prefix-freeness (with injectivity), set-level proper-prefix-freeness, positive token length | `ex_prefixFree_pos`, `ex_imagePrefixFree_pos`, `ex_nonEmptyEnc_pos` | `ex_prefixFree_neg`, `ex_imagePrefixFree_neg`, `const_imagePrefixFree_not_prefixFree`, `ex_nonEmptyEnc_neg` |
| `encList`, `decList`, `listCodec` | Whole-input concatenation and progress-guarded repeat-until-exhausted decoding | `ex_listCodec_pos` | `ex_listCodec_neg`, `ex_decList_guard_rejects` (reaches `rest.length ≥ xs.length` guard) |
| `Junk`, `inlMatcher`, `decompToFun`, `decompInvFun`, `codecOfSplit`, `junkToC`, `complementEquivOfCodecEq` | Coproduct complement split `B ≃ A ⊕ C` and explicit complement equivalence extraction | `ex_junk_pos`, `ex_inlMatcher_pos`, `ex_decomp_pos`, `ex_codecOfSplit_pos`, `ex_junkToC_pos`, `ex_complementEquivOfCodecEq_pos` | `ex_junk_neg`, `ex_inlMatcher_neg`, `ex_decomp_neg_malleable`, `ex_decomp_neg_failing`, `ex_codecOfSplit_neg`, `ex_junkToC_neg_nonRightInv`, `ex_complementEquivOfCodecEq_neg` |

### Proved Supporting Lemmas and Boundary Witnesses

Supporting lemmas cited across the result cards (`Toy/Codec/Witnesses.lean` and `Toy/Codec/Counterexamples.lean`), with verified axiom sets from `audit/axioms.json`:

- **Unconditional & derivability lemmas (`Witnesses.lean`):** `classicalCodec_enc` (`['Classical.choice', 'Quot.sound', 'propext']`), `codecOfFiberSplit_encDec` (`[]`), `canonicalize_encDec` (`[]`), `encDec_imp_decInj` (`[]`), `lawful_iff_decEnc_and_accepts_only_range` (`[]`), `enc_unique_of_dec_eq` (`['Quot.sound']`), `isSome_imp_mem_range_of_encDec` (`[]`), `mem_range_imp_isSome_of_decEnc` (`[]`), `eq_none_iff_of_isSome_iff` (`[]`), `prefixFree_iff_injective_and_imagePrefixFree` (`['Quot.sound', 'propext']`), `prefixDecEnc_nil_codeword_imp_subsingleton` (`['propext']`), `prefixFree_nil_codeword_imp_subsingleton` (`[]`), `nonEmptyEnc_of_prefixDecEnc_of_ne` (`['propext']`), `nonEmptyEnc_of_listCodec_decEnc` (`['propext']`), `dec_eq_inlMatcher_decompToFun` (`['propext']`), `codecOfSplit_decomp_eq` (`['Quot.sound', 'propext']`), `decompToFun_enc_of_rightInv` (`[]`), `codecOfSplit_eq_of_intertwining_fun` (`['Quot.sound']`), `codecOfSplit_lawful_of_leftInv_and_rightInv_inl` (`[]`), `untaggedSum_decEnc_imp_disjoint_images` (`[]`), `untaggedSum_lawful_iff_disjoint_images` (`[]`).
- **Positive controls & boundary witnesses (`Counterexamples.lean`):** `suffixEnc_not_prefixFree_yet_concat_lawful` (`['Quot.sound', 'propext']`), `decInj_and_surjective_dec_not_lawful` (`[]`), `const_imagePrefixFree_not_prefixFree` (`['propext']`), `lenient_not_prefixDecEnc_yet_listCodec_decEnc` (`['Quot.sound', 'propext']`), `encList_not_prefixFree` (`[]`), `no_prefixDecEnc_for_encList` (`['propext']`), `framed_lawful_but_firstOnly_not_decInj` (`['propext']`), `firstOnly_decEnc_and_not_decInj` (`['propext']`), `same_complement_different_codec` (`[]`), `nonCanonicalBoolCodec_not_encDec_yet_admits_equiv` (`['propext']`).
- **Additional boundary witnesses (`Witnesses.lean`):** `bareList_first_field_lawful` (`['propext']`; a bare `encList`-encoded list as the first field of a lawful `FramedCodec.seq` record, with no length prefix or terminator; helper lemmas `bareListGreedy_encList`, `bareListGreedy_sound`, and `bareListSeq_decPrefix_eq`, each `['propext']`), `fiberSplit_exists_for_every_function` (`['Classical.choice', 'Quot.sound', 'propext']`; classically every function has a `FiberSplit`, via the noncomputable `classicalFiberSplit`).

### Result Cards

#### Part A: Characterization and Bijection with Injections

##### Card 1 (`decEnc_imp_enc_injective`): `Toy.Codec.decEnc_imp_enc_injective`

- **Kind:** `theorem` | **Tier:** `T0` (re-derivation: a total encoder with a partial left inverse is injective) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `decEnc_imp_enc_injective`: none (`[]`)
- **Plain claim:** For any codec c : Codec A B, the decode-after-encode round-trip law DecEnc c alone implies that the encoder c.enc is injective (EncDec c is not required).
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.decEnc_imp_enc_injective.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    Toy.Codec.DecEnc c → Function.Injective c.enc
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:69-70
  theorem decEnc_imp_enc_injective {A : Type u} {B : Type v} (c : Codec A B)
      (hde : DecEnc c) : Function.Injective c.enc
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem decEnc_imp_enc_injective {A : Type u} {B : Type v} (c : Codec A B)
      (hde : ∀ a : A, c.dec (c.enc a) = some a) :
      ∀ ⦃a₁ a₂ : A⦄, c.enc a₁ = c.enc a₂ → a₁ = a₂
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `hde` | Makes c.dec a left retraction of c.enc up to Option.some, so equal encodings yield equal decoded values. | `tight` | `Toy.Codec.ce_decEnc_imp_enc_injective_drop_decEnc` |

- **Non-vacuity witness:** `Toy.Codec.nv_decEnc_imp_enc_injective` — boolToNatCodec : Codec Bool Nat (false ↦ 0, true ↦ 1, n ≥ 2 ↦ none) satisfies DecEnc.
- **Non-claims:**
  - Does not show that DecEnc c implies EncDec c or whole-input decoder injectivity (DecInj c); see decEnc_admits_malleable_codec.
  - Does not show that EncDec c implies Function.Injective c.enc; alwaysFailConstCodec satisfies EncDec with a constant encoder Bool → Unit.
  - Does not construct an executable decoder for an arbitrary injective function without FiberSplit or Classical.choice.
- **Prior art:**
  - Rocq Corelib SSReflect, repository rocq-prover/rocq, file theories/Corelib/ssr/ssrfun.v, commit 25f5b18a320e4796f181f938d3b74bebe7db4dc4 (pcancel, ocancel, pcan_inj, pcan_pcomp, ocan_comp) and Mathematical Components, repository math-comp/math-comp, file boot/eqtype.v, commit 1cf23375ae1948bc37a50f153a6fdd2338dacf98 (valK, insubK).
  - Simon Foster, Christian Pardillo-Laursen, and Frank Zeyda, 'Optics', Archive of Formal Proofs, 2017, https://www.isa-afp.org/entries/Optics.html, official AFP Isabelle2026 release mirror isabelle-prover/mirror-afp-2026, commit 749ee1bd79285aeb2597f31d797d0e55d9af62c9, file thys/Optics/Prisms.thy (locale wb_prism with match_build, build_match, build_match_iff, range_build, inj_build, wb_prim_suml, wb_prim_sumr, and disjoint-range prism_plus_wb).
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/Logic/Encodable/Basic.lean (Encodable.encodek, Encodable.decode₂, mem_decode₂, decode₂_isPartialInv, decidableRangeEncode) and Mathlib/Computability/Encoding.lean (Encoding.encode_injective).
  - EverParse / LowParse mechanization, repository project-everest/everparse, commit f3e4ce51d9b68593fd98472cadcdeb8b6abf388f, file lib/everparse/lowparse/LowParse.Spec.Base.fsti (serializer_correct, serializer_complete, serializer_correct_implies_complete, serializer_injective, serializer_parser_unique).
  - Dimitrios Vytiniotis and Andrew J. Kennedy, 'Functional pearl: every bit counts', Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming (ICFP '10), pp. 15–26, 2010, DOI 10.1145/1863543.1863548 (Section 3, Coq-checked Lemma 1 for PrefixDecEnc, Corollary 1 for encoder injectivity, Corollary 2 for indexed PrefixFree, and Lemma 3 for PrefixEncDec); journal version: Andrew J. Kennedy and Dimitrios Vytiniotis, 'Every bit counts: The binary representation of typed data and programs', Journal of Functional Programming 22(4–5), pp. 529–573, 2012, DOI 10.1017/S0956796812000263.
  - Benjamin Delaware, Sorawit Suriyakarn, Clément Pit-Claudel, Qianchuan Ye, and Adam Chlipala, 'Narcissus: Correct-by-Construction Derivation of Decoders and Encoders from Binary Formats', Proceedings of the ACM on Programming Languages 3 (ICFP), Article 82, 2019, DOI 10.1145/3341686 (Definition 2.2 requires both that every target in the format relation decodes to its source value and that every accepted target lies in the format relation; because a format is a relation rather than a single function, multiple encodings of one value may be valid without accepting malformed input, so functional EncDec relative to one chosen encoder need not hold).
- **Design question:** Does demanding decode-after-encode (DecEnc) alone guarantee that an encoder loses no source information (is injective), even when canonicality (EncDec) is not yet enforced?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.decEnc_imp_enc_injective` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `decEnc_imp_enc_injective`: none (`[]`).
- **Basis: derived (modeling bridge)** — For any pure, deterministic serializer/deserializer pair modeled by a total `enc` and option-valued `dec`, verifying only decode-after-encode (`DecEnc`) already rules out serializer collisions (`enc a₁ = enc a₂` for `a₁ ≠ a₂`). This bridge does not cover non-deterministic or stateful encoders, nor does it guard against parser malleability.

##### Card 2 (`lawful_iff_dec_eq_some_iff`): `Toy.Codec.lawful_iff_dec_eq_some_iff`, `Toy.Codec.decEqSomeIff_imp_enc_injective`

- **Kind:** `characterization` | **Tier:** `T0` (re-derivation: partial-inverse graph characterization and hypothesis-minimality corollary) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `lawful_iff_dec_eq_some_iff`: none (`[]`); `decEqSomeIff_imp_enc_injective`: none (`[]`)
- **Plain claim:** For any codec c : Codec A B, satisfying both DecEnc c and EncDec c is equivalent to c.dec having the converse graph of c.enc (∀ b a, c.dec b = some a ↔ c.enc a = b); as a hypothesis-minimality corollary (decEqSomeIff_imp_enc_injective, reference point), that converse-graph condition alone implies Function.Injective c.enc.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.lawful_iff_dec_eq_some_iff.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    Toy.Codec.DecEnc c ∧ Toy.Codec.EncDec c ↔ ∀ (b : B) (a : A), c.dec b = some a ↔ c.enc a = b
  Toy.Codec.decEqSomeIff_imp_enc_injective.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    (∀ (b : B) (a : A), c.dec b = some a ↔ c.enc a = b) → Function.Injective c.enc
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:81-82
  theorem lawful_iff_dec_eq_some_iff {A : Type u} {B : Type v} (c : Codec A B) :
      (DecEnc c ∧ EncDec c) ↔ (∀ (b : B) (a : A), c.dec b = some a ↔ c.enc a = b)

  -- lean/Toy/Codec/Statements.lean:91-93
  theorem decEqSomeIff_imp_enc_injective {A : Type u} {B : Type v} (c : Codec A B)
      (hconv : ∀ (b : B) (a : A), c.dec b = some a ↔ c.enc a = b) :
      Function.Injective c.enc
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem lawful_iff_dec_eq_some_iff {A : Type u} {B : Type v} (c : Codec A B) :
      ((∀ a : A, c.dec (c.enc a) = some a) ∧
       (∀ (b : B) (a : A), c.dec b = some a → c.enc a = b)) ↔
      (∀ (b : B) (a : A), c.dec b = some a ↔ c.enc a = b)

  theorem decEqSomeIff_imp_enc_injective {A : Type u} {B : Type v} (c : Codec A B)
      (hconv : ∀ (b : B) (a : A), c.dec b = some a ↔ c.enc a = b) :
      ∀ ⦃a₁ a₂ : A⦄, c.enc a₁ = c.enc a₂ → a₁ = a₂
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `hconv (in decEqSomeIff_imp_enc_injective)` | Forces c.dec (c.enc a) = some a for every a, so equal encodings yield equal outputs of the function c.dec; lawful_iff_dec_eq_some_iff itself is unconditional. | `tight` | `Toy.Codec.ce_decEqSomeIff_imp_enc_injective_drop_hconv` |

- **Non-vacuity witness:** `Toy.Codec.nv_lawful_iff_dec_eq_some_iff`, `Toy.Codec.nv_decEqSomeIff_imp_enc_injective` — boolToNatCodec : Codec Bool Nat satisfies both sides of lawful_iff_dec_eq_some_iff and the hypothesis of decEqSomeIff_imp_enc_injective.
- **Non-claims:**
  - Does not show that the encoder implements any intended format. Classically, every injective function `A → B` is the encoder of a codec satisfying both laws; the laws constrain the decoder relative to the encoder and nothing else.
  - The model has no byte layouts, lengths, state, or error reporting. Nothing here is a security property of an implemented parser.
  - Does not require listing Function.Injective c.enc on the right-hand side of lawful_iff_dec_eq_some_iff because injectivity is derivable from either side (decEnc_imp_enc_injective, decEqSomeIff_imp_enc_injective); a third equivalent formulation matching EverParse's 'correct and exact' is proved in Witnesses.lean as lawful_iff_decEnc_and_accepts_only_range.
  - Does not imply c.enc is surjective or c.dec is total, and does not guarantee unambiguous list concatenation when B = List β (see lawful_injective_nonEmpty_enc_admits_ambiguous_concat).
- **Prior art:**
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/Logic/Function/Basic.lean (Function.IsPartialInv, IsPartialInv.injective, injective_of_isPartialInv_right, IsPartialInv.comp, Function.partialInv, Injective.isPartialInv, partialInv_left) and Mathlib/Basic/PEquiv.lean (PEquiv).
  - Simon Foster, Christian Pardillo-Laursen, and Frank Zeyda, 'Optics', Archive of Formal Proofs, 2017, https://www.isa-afp.org/entries/Optics.html, official AFP Isabelle2026 release mirror isabelle-prover/mirror-afp-2026, commit 749ee1bd79285aeb2597f31d797d0e55d9af62c9, file thys/Optics/Prisms.thy (locale wb_prism with match_build, build_match, build_match_iff, range_build, inj_build, wb_prim_suml, wb_prim_sumr, and disjoint-range prism_plus_wb).
  - Haskell lens library, lens-5.3.2, module Control.Lens.Prism, Hackage documentation (states the prism laws preview l (review l b) ≡ Just b and preview l s ≡ Just a ⟹ review l a ≡ s).
  - Tillmann Rendel and Klaus Ostermann, 'Invertible syntax descriptions: unifying parsing and pretty printing', Proceedings of the Third ACM Haskell Symposium on Haskell (Haskell '10), pp. 1–12, 2010, DOI 10.1145/1863523.1863525 (defines partial isomorphisms as pairs α → Maybe β and β → Maybe α, with Category composition and product combinator (***) in Hackage package partial-isomorphisms-0.2.4.0; Codec specializes this shape to a total encoder).
  - Tahina Ramananandro, Antoine Delignat-Lavaud, Cédric Fournet, Nikhil Swamy, Tej Chajed, Nadim Kobeissi, and Jonathan Protzenko, 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 2.1 defines parser correctness p(s(m)) = m, exactness p⁻¹(V) = s(V), non-malleability as parser injectivity on accepted inputs, and completeness as parser surjectivity; Section 2.2 ('Attacks on Parsers') describes attacks enabled by malleable or non-exact parsers (PKCS #1 signature forgery via a malleable or non-exact ASN.1 parser, and Bitcoin transaction malleability), alongside memory-safety bugs such as Heartbleed).
- **Design question:** What exact relational condition on (encode, decode) is equivalent to demanding both DecEnc and EncDec—ensuring simultaneously that every encoding is accepted and decodes to its source, no junk outside the image is accepted, and no value has multiple accepted encodings?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.lawful_iff_dec_eq_some_iff`, `Toy.Codec.decEqSomeIff_imp_enc_injective` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `lawful_iff_dec_eq_some_iff`: none (`[]`); `decEqSomeIff_imp_enc_injective`: none (`[]`).
- **Basis: derived (modeling bridge)** — Specifying both `DecEnc` and `EncDec` for a serializer/parser pair is mathematically identical to fixing the parser's input-output relation to be the exact converse of the serializer's graph (and equivalently to EverParse's 'correct and exact' via `lawful_iff_decEnc_and_accepts_only_range`). The bridge stops at functional formats: relational wire formats that deliberately allow multiple encodings per value cannot satisfy `EncDec` relative to one encoder, and no memory-safety or byte-layout property is modeled.

##### Card 3 (`lawful_iff_decEnc_and_decInj`): `Toy.Codec.lawful_iff_decEnc_and_decInj`

- **Kind:** `characterization` | **Tier:** `T0` (re-derivation: equivalence of canonicality (`EncDec`) and whole-input non-malleability (`DecInj`) under `DecEnc`) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `lawful_iff_decEnc_and_decInj`: none (`[]`)
- **Plain claim:** For any codec c : Codec A B, satisfying DecEnc c and EncDec c is equivalent to satisfying DecEnc c and whole-input decoder injectivity DecInj c (at most one wire representation decodes to each source value).
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.lawful_iff_decEnc_and_decInj.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    Toy.Codec.DecEnc c ∧ Toy.Codec.EncDec c ↔ Toy.Codec.DecEnc c ∧ Toy.Codec.DecInj c
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:103-104
  theorem lawful_iff_decEnc_and_decInj {A : Type u} {B : Type v} (c : Codec A B) :
      (DecEnc c ∧ EncDec c) ↔ (DecEnc c ∧ DecInj c)
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem lawful_iff_decEnc_and_decInj {A : Type u} {B : Type v} (c : Codec A B) :
      ((∀ a : A, c.dec (c.enc a) = some a) ∧
       (∀ (b : B) (a : A), c.dec b = some a → c.enc a = b)) ↔
      ((∀ a : A, c.dec (c.enc a) = some a) ∧
       (∀ (b₁ b₂ : B) (a : A), c.dec b₁ = some a → c.dec b₂ = some a → b₁ = b₂))
  ```
- **Hypothesis ledger:** None (unconditional statement).
- **Non-vacuity witness:** `Toy.Codec.nv_lawful_iff_decEnc_and_decInj` — boolToNatCodec : Codec Bool Nat satisfies both sides of the equivalence.
- **Non-claims:**
  - `EncDec c` implies `DecInj c` with no other hypothesis; only the converse needs `DecEnc c`. A decoder that is injective on accepted inputs and surjective does not make a codec with a given encoder satisfy either law (`shiftedBoolCodec`).
  - Does not show that DecInj c implies DecEnc c; alwaysFailBoolCodec satisfies DecInj vacuously while rejecting every input (encDec_imp_decInj is proved unconditionally in Witnesses.lean, whereas DecInj → EncDec fails on shiftedBoolCodec via decInj_and_surjective_dec_not_lawful).
- **Prior art:**
  - Tahina Ramananandro, Antoine Delignat-Lavaud, Cédric Fournet, Nikhil Swamy, Tej Chajed, Nadim Kobeissi, and Jonathan Protzenko, 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 2.1 defines parser correctness p(s(m)) = m, exactness p⁻¹(V) = s(V), non-malleability as parser injectivity on accepted inputs, and completeness as parser surjectivity; Section 2.2 ('Attacks on Parsers') describes attacks enabled by malleable or non-exact parsers (PKCS #1 signature forgery via a malleable or non-exact ASN.1 parser, and Bitcoin transaction malleability), alongside memory-safety bugs such as Heartbleed).
  - EverParse / LowParse mechanization, repository project-everest/everparse, commit f3e4ce51d9b68593fd98472cadcdeb8b6abf388f, file lib/everparse/lowparse/LowParse.Spec.Base.fsti (serializer_correct, serializer_complete, serializer_correct_implies_complete, serializer_injective, serializer_parser_unique).
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/Logic/Function/Basic.lean (Function.IsPartialInv, IsPartialInv.injective, injective_of_isPartialInv_right, IsPartialInv.comp, Function.partialInv, Injective.isPartialInv, partialInv_left) and Mathlib/Basic/PEquiv.lean (PEquiv).
- **Design question:** When does parser-only non-malleability (DecInj: at most one wire input decodes to any value) coincide with encoder-relative canonicality (EncDec)?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.lawful_iff_decEnc_and_decInj` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `lawful_iff_decEnc_and_decInj`: none (`[]`).
- **Basis: derived (modeling bridge)** — In specification frameworks for single-encoder binary formats (such as EverParse/LowParse), proving parser correctness (`DecEnc`) plus parser non-malleability (`DecInj`) is equivalent to proving `DecEnc` plus encoder-relative canonicality (`EncDec`). Because `DecInj` alone does not anchor the decoder to `enc` (`shiftedBoolCodec`), parser-only non-malleability checks must be paired with `DecEnc` to establish canonicality.

##### Card 4 (`dec_unique_of_lawful`): `Toy.Codec.dec_unique_of_lawful`

- **Kind:** `theorem` | **Tier:** `T0` (re-derivation: uniqueness of a lawful partial inverse for a fixed encoder) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `dec_unique_of_lawful`: `Quot.sound`
- **Plain claim:** If two codecs c₁ c₂ : Codec A B share the same encoder (c₁.enc = c₂.enc) and both satisfy DecEnc and EncDec, then they have the same decoder (c₁.dec = c₂.dec), without Classical.choice (using function extensionality; established by the kernel axiom record: [Quot.sound]).
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.dec_unique_of_lawful.{u, v} : ∀ {A : Type u} {B : Type v} (c₁ c₂ : Toy.Codec.Codec A B),
    c₁.enc = c₂.enc →
      Toy.Codec.DecEnc c₁ →
        Toy.Codec.EncDec c₁ → Toy.Codec.DecEnc c₂ → Toy.Codec.EncDec c₂ → c₁.dec = c₂.dec
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:113-117
  theorem dec_unique_of_lawful {A : Type u} {B : Type v} (c₁ c₂ : Codec A B)
      (henc : c₁.enc = c₂.enc)
      (hde₁ : DecEnc c₁) (hed₁ : EncDec c₁)
      (hde₂ : DecEnc c₂) (hed₂ : EncDec c₂) :
      c₁.dec = c₂.dec
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem dec_unique_of_lawful {A : Type u} {B : Type v} (c₁ c₂ : Codec A B)
      (henc : c₁.enc = c₂.enc)
      (hde₁ : ∀ a : A, c₁.dec (c₁.enc a) = some a)
      (hed₁ : ∀ (b : B) (a : A), c₁.dec b = some a → c₁.enc a = b)
      (hde₂ : ∀ a : A, c₂.dec (c₂.enc a) = some a)
      (hed₂ : ∀ (b : B) (a : A), c₂.dec b = some a → c₂.enc a = b) :
      c₁.dec = c₂.dec
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `henc` | Aligns the two encoders so both decoders invert the same map. | `tight` | `Toy.Codec.ce_dec_unique_drop_henc` |
  | `hde₁` | Ensures c₁.dec accepts every encoded value in the shared image. | `tight` | `Toy.Codec.ce_dec_unique_drop_hde1` |
  | `hed₁` | Ensures c₁.dec rejects wire values outside the image of enc. | `tight` | `Toy.Codec.ce_dec_unique_drop_hed1` |
  | `hde₂` | Ensures c₂.dec accepts every encoded value in the shared image. | `tight` | `Toy.Codec.ce_dec_unique_drop_hde2` |
  | `hed₂` | Ensures c₂.dec rejects wire values outside the image of enc. | `tight` | `Toy.Codec.ce_dec_unique_drop_hed2` |

- **Non-vacuity witness:** `Toy.Codec.nv_dec_unique_of_lawful` — boolToNatCodec and codecOfFiberSplit boolToNatCodec.enc boolToNatFiberSplit share the same encoder and both satisfy DecEnc and EncDec.
- **Non-claims:**
  - Does not assert that a computable lawful decoder exists for an arbitrary injection without FiberSplit.
  - Does not assert uniqueness when only DecEnc holds (decoders may accept different non-canonical inputs) or when only EncDec holds (decoders may reject different valid encodings); by contrast, the dual encoder-uniqueness fact enc_unique_of_dec_eq (proved in Witnesses.lean) needs only DecEnc c₁ and EncDec c₂.
  - Does not assert algorithmic or complexity equivalence of the two decoders—only extensional function equality B → Option A.
- **Prior art:**
  - EverParse / LowParse mechanization, repository project-everest/everparse, commit f3e4ce51d9b68593fd98472cadcdeb8b6abf388f, file lib/everparse/lowparse/LowParse.Spec.Base.fsti (serializer_correct, serializer_complete, serializer_correct_implies_complete, serializer_injective, serializer_parser_unique).
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/Logic/Function/Basic.lean (Function.IsPartialInv, IsPartialInv.injective, injective_of_isPartialInv_right, IsPartialInv.comp, Function.partialInv, Injective.isPartialInv, partialInv_left) and Mathlib/Basic/PEquiv.lean (PEquiv).
  - Tahina Ramananandro et al., 'EverParse', USENIX Security 2019, Section 2.1 (states the dual direction: a non-malleable and surjective parser uniquely determines its serializer p⁻¹).
- **Design question:** Once an encoder is fixed, can two extensionally distinct decoders both satisfy DecEnc and EncDec, or do the two laws determine decode uniquely?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.dec_unique_of_lawful` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `dec_unique_of_lawful`: `Quot.sound`.
- **Basis: derived (modeling bridge)** — Once a canonical binary format is specified by a deterministic serializer `enc`, the extensional behavior of any lawful parser is completely determined—there is no design freedom in which wire values are accepted or rejected, only in implementation strategy (zero-copy vs. copying, time/space complexity, error diagnostics).

##### Card 5 (`classicalCodec_bijection`): `Toy.Codec.classicalCodec_decEnc_of_injective`, `Toy.Codec.classicalCodec_encDec`, `Toy.Codec.classicalCodec_recover_of_lawful`

- **Kind:** `characterization` | **Tier:** `T0` (re-derivation: classical bijection between lawful codecs and injections (Mathlib `Function.partialInv`)) | **Depth:** `shallow`
- **Hashed companion theorem(s) (`lean_names`):** `Toy.Codec.classicalCodec_enc`
- **Verified axioms (`audit/axioms.json`):** `classicalCodec_decEnc_of_injective`: `Classical.choice`, `Quot.sound`, `propext`; `classicalCodec_encDec`: `Classical.choice`, `Quot.sound`, `propext`; `classicalCodec_recover_of_lawful`: `Classical.choice`, `Quot.sound`, `propext`; `classicalCodec_enc`: `Classical.choice`, `Quot.sound`, `propext`
- **Plain claim:** Classically (via Classical.choice), classicalCodec f satisfies DecEnc for every injective f : A → B (classicalCodec_decEnc_of_injective) and satisfies EncDec unconditionally for every f (classicalCodec_encDec, reference-point companion), while classicalCodec c.enc = c holds for every codec satisfying DecEnc c and EncDec c (classicalCodec_recover_of_lawful); together with decEnc_imp_enc_injective and the definitional equality classicalCodec_enc ((classicalCodec f).enc = f), these five named declarations establish a bijection between lawful codecs A ⇄ B and injections A → B.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.classicalCodec_decEnc_of_injective.{u, v} : ∀ {A : Type u} {B : Type v} (f : A → B),
    Function.Injective f → Toy.Codec.DecEnc (Toy.Codec.classicalCodec f)
  Toy.Codec.classicalCodec_encDec.{u, v} : ∀ {A : Type u} {B : Type v} (f : A → B), Toy.Codec.EncDec (Toy.Codec.classicalCodec f)
  Toy.Codec.classicalCodec_recover_of_lawful.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    Toy.Codec.DecEnc c → Toy.Codec.EncDec c → Toy.Codec.classicalCodec c.enc = c
  Toy.Codec.classicalCodec_enc.{u, v} : ∀ {A : Type u} {B : Type v} (f : A → B), (Toy.Codec.classicalCodec f).enc = f
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:138-140
  theorem classicalCodec_decEnc_of_injective {A : Type u} {B : Type v}
      (f : A → B) (hf : Function.Injective f) :
      DecEnc (classicalCodec f)

  -- lean/Toy/Codec/Statements.lean:149-150
  theorem classicalCodec_encDec {A : Type u} {B : Type v} (f : A → B) :
      EncDec (classicalCodec f)

  -- lean/Toy/Codec/Statements.lean:162-164
  theorem classicalCodec_recover_of_lawful {A : Type u} {B : Type v} (c : Codec A B)
      (hde : DecEnc c) (hed : EncDec c) :
      classicalCodec c.enc = c

  -- lean/Toy/Codec/Witnesses.lean:20-21
  theorem classicalCodec_enc {A : Type u} {B : Type v} (f : A → B) :
      (classicalCodec f).enc = f
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem classicalCodec_decEnc_of_injective {A : Type u} {B : Type v}
      (f : A → B) (hf : ∀ ⦃a₁ a₂ : A⦄, f a₁ = f a₂ → a₁ = a₂) :
      ∀ a : A, classicalDec f (f a) = some a

  theorem classicalCodec_encDec {A : Type u} {B : Type v} (f : A → B) :
      ∀ (b : B) (a : A), classicalDec f b = some a → f a = b

  theorem classicalCodec_recover_of_lawful {A : Type u} {B : Type v} (c : Codec A B)
      (hde : ∀ a : A, c.dec (c.enc a) = some a)
      (hed : ∀ (b : B) (a : A), c.dec b = some a → c.enc a = b) :
      (⟨c.enc, classicalDec c.enc⟩ : Codec A B) = c

  theorem classicalCodec_enc {A : Type u} {B : Type v} (f : A → B) :
      (classicalCodec f).enc = f
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `hf (in classicalCodec_decEnc_of_injective)` | Forces Classical.choose ⟨a, rfl⟩ to equal a; not required for classicalCodec_encDec. | `tight` | `Toy.Codec.ce_classicalCodec_decEnc_drop_inj` |
  | `hde (in classicalCodec_recover_of_lawful)` | Ensures c.dec accepts every element in the image of c.enc, matching classicalDec c.enc. | `tight` | `Toy.Codec.ce_classicalCodec_recover_drop_decEnc` |
  | `hed (in classicalCodec_recover_of_lawful)` | Ensures c.dec rejects every element outside the image of c.enc, matching classicalDec c.enc. | `tight` | `Toy.Codec.ce_classicalCodec_recover_drop_encDec` |

- **Non-vacuity witness:** `Toy.Codec.nv_classicalCodec_decEnc_of_injective`, `Toy.Codec.nv_classicalCodec_encDec`, `Toy.Codec.nv_classicalCodec_recover_of_lawful` — boolToNatCodec.enc : Bool → Nat is injective, classicalCodec satisfies EncDec on both boolToNatCodec.enc and fun _ : Bool => (), and boolToNatCodec is lawful.
- **Non-claims:**
  - Does not produce an executable decoder; classicalDec uses Classical.propDecidable and Classical.choose (Classical.choice).
  - Does not imply DecEnc (classicalCodec f) when f is not injective (ce_classicalCodec_decEnc_drop_inj), nor does it recover single-law codecs from their encoder.
- **Prior art:**
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/Logic/Function/Basic.lean (Function.IsPartialInv, IsPartialInv.injective, injective_of_isPartialInv_right, IsPartialInv.comp, Function.partialInv, Injective.isPartialInv, partialInv_left) and Mathlib/Basic/PEquiv.lean (PEquiv).
  - Mitchell Riley, 'Categories of Optics', arXiv:1809.00738v2 [math.CT], 2018 (Section 4.2 states concrete prism laws and observes in the proof of Proposition 4.2.2 that the first law makes Review injective so S ≅ C ⊔ A for some complement C in Set; Proposition 4.1.3, generalizing Johnson, Rosebrugh, and Wood, J.UCS 16(5):729–748, 2010, treats the lens-side complement under pullbacks and a global element of the view).
- **Design question:** Ignoring computability, does a lawful codec A ⇄ B carry any additional mathematical data beyond an injective encoder A → B?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.classicalCodec_decEnc_of_injective`, `Toy.Codec.classicalCodec_encDec`, `Toy.Codec.classicalCodec_recover_of_lawful`, `Toy.Codec.classicalCodec_enc` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `classicalCodec_decEnc_of_injective`: `Classical.choice`, `Quot.sound`, `propext`; `classicalCodec_encDec`: `Classical.choice`, `Quot.sound`, `propext`; `classicalCodec_recover_of_lawful`: `Classical.choice`, `Quot.sound`, `propext`; `classicalCodec_enc`: `Classical.choice`, `Quot.sound`, `propext`.
- **Basis: derived (modeling bridge)** — Mathematically (ignoring computability), once a single deterministic encoder `A → B` is fixed, a lawful codec carries no further abstract mathematical data beyond injectivity of that encoder. In real systems, beyond choosing the wire format and injective encoder, the remaining difficulty is constructing an executable (efficient, memory-safe) decoder rather than proving abstract existence of a partial inverse.

##### Card 6 (`codecOfFiberSplit_correspondence`): `Toy.Codec.codecOfFiberSplit_decEnc_of_injective`, `Toy.Codec.codecOfFiberSplit_eq_of_lawful`

- **Kind:** `characterization` | **Tier:** `T0` (re-derivation: constructive decidable-fiber correspondence (`agda-unimath` `is-decidable-emb`)) | **Depth:** `shallow`
- **Hashed companion declaration(s) (`lean_names`):** `Toy.Codec.codecOfFiberSplit_encDec`, `Toy.Codec.fiberSplitOfLawful`
- **Verified axioms (`audit/axioms.json`):** `codecOfFiberSplit_decEnc_of_injective`: none (`[]`); `codecOfFiberSplit_eq_of_lawful`: `Quot.sound`; `codecOfFiberSplit_encDec`: none (`[]`); `fiberSplitOfLawful`: none (`[]`)
- **Plain claim:** Constructively (without Classical.choice, established by the kernel axiom record: no axioms for codecOfFiberSplit_decEnc_of_injective, codecOfFiberSplit_encDec, and fiberSplitOfLawful; [Quot.sound] only for codecOfFiberSplit_eq_of_lawful), any injection f : A → B equipped with a decidable-fiber witness s : FiberSplit f yields a computable lawful codec codecOfFiberSplit f s (satisfying DecEnc via codecOfFiberSplit_decEnc_of_injective and EncDec unconditionally via codecOfFiberSplit_encDec); conversely, every lawful codec c constructively yields fiberSplitOfLawful c hde hed : FiberSplit c.enc, and for every s : FiberSplit c.enc, codecOfFiberSplit c.enc s = c (codecOfFiberSplit_eq_of_lawful).
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.codecOfFiberSplit_decEnc_of_injective.{u, v} : ∀ {A : Type u} {B : Type v} (f : A → B) (s : Toy.Codec.FiberSplit f),
    Function.Injective f → Toy.Codec.DecEnc (Toy.Codec.codecOfFiberSplit f s)
  Toy.Codec.codecOfFiberSplit_eq_of_lawful.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    Toy.Codec.DecEnc c →
      Toy.Codec.EncDec c →
        ∀ (s : Toy.Codec.FiberSplit c.enc), Toy.Codec.codecOfFiberSplit c.enc s = c
  Toy.Codec.codecOfFiberSplit_encDec.{u, v} : ∀ {A : Type u} {B : Type v} (f : A → B) (s : Toy.Codec.FiberSplit f),
    Toy.Codec.EncDec (Toy.Codec.codecOfFiberSplit f s)
  Toy.Codec.fiberSplitOfLawful.{u, v} : {A : Type u} →
    {B : Type v} →
      (c : Toy.Codec.Codec A B) → Toy.Codec.DecEnc c → Toy.Codec.EncDec c → Toy.Codec.FiberSplit c.enc
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:181-183
  theorem codecOfFiberSplit_decEnc_of_injective {A : Type u} {B : Type v}
      (f : A → B) (s : FiberSplit f) (hf : Function.Injective f) :
      DecEnc (codecOfFiberSplit f s)

  -- lean/Toy/Codec/Statements.lean:194-196
  theorem codecOfFiberSplit_eq_of_lawful {A : Type u} {B : Type v}
      (c : Codec A B) (hde : DecEnc c) (hed : EncDec c) (s : FiberSplit c.enc) :
      codecOfFiberSplit c.enc s = c

  -- lean/Toy/Codec/Witnesses.lean:24-25
  theorem codecOfFiberSplit_encDec {A : Type u} {B : Type v}
      (f : A → B) (s : FiberSplit f) : EncDec (codecOfFiberSplit f s)

  -- Type of fiberSplitOfLawful (defined in Defs.lean):
  -- ∀ {A : Type u} {B : Type v} (c : Codec A B),
  --   (∀ a : A, c.dec (c.enc a) = some a) →
  --   (∀ (b : B) (a : A), c.dec b = some a → c.enc a = b) →
  --   (∀ b : B, PSum { a : A // c.enc a = b } (∀ a : A, c.enc a ≠ b))
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem codecOfFiberSplit_decEnc_of_injective {A : Type u} {B : Type v}
      (f : A → B) (s : ∀ b : B, PSum { a : A // f a = b } (∀ a : A, f a ≠ b))
      (hf : ∀ ⦃a₁ a₂ : A⦄, f a₁ = f a₂ → a₁ = a₂) :
      ∀ a : A, (codecOfFiberSplit f s).dec (f a) = some a

  theorem codecOfFiberSplit_eq_of_lawful {A : Type u} {B : Type v}
      (c : Codec A B)
      (hde : ∀ a : A, c.dec (c.enc a) = some a)
      (hed : ∀ (b : B) (a : A), c.dec b = some a → c.enc a = b)
      (s : ∀ b : B, PSum { a : A // c.enc a = b } (∀ a : A, c.enc a ≠ b)) :
      codecOfFiberSplit c.enc s = c

  theorem codecOfFiberSplit_encDec {A : Type u} {B : Type v}
      (f : A → B) (s : ∀ b : B, PSum { a : A // f a = b } (∀ a : A, f a ≠ b)) :
      ∀ (b : B) (a : A), (codecOfFiberSplit f s).dec b = some a → f a = b

  -- Type of fiberSplitOfLawful (defined in Defs.lean):
  -- ∀ {A : Type u} {B : Type v} (c : Codec A B),
  --   (∀ a : A, c.dec (c.enc a) = some a) →
  --   (∀ (b : B) (a : A), c.dec b = some a → c.enc a = b) →
  --   (∀ b : B, PSum { a : A // c.enc a = b } (∀ a : A, c.enc a ≠ b))
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `hf (in codecOfFiberSplit_decEnc_of_injective)` | Forces the preimage returned by s (f a) to equal a rather than a distinct colliding preimage. | `tight` | `Toy.Codec.ce_codecOfFiberSplit_decEnc_drop_inj` |
  | `hde (in codecOfFiberSplit_eq_of_lawful)` | Ensures c.dec accepts every element in the image of c.enc, matching codecOfFiberSplit c.enc s. | `tight` | `Toy.Codec.ce_codecOfFiberSplit_eq_drop_decEnc` |
  | `hed (in codecOfFiberSplit_eq_of_lawful)` | Ensures c.dec rejects every element outside the image of c.enc, matching codecOfFiberSplit c.enc s. | `tight` | `Toy.Codec.ce_codecOfFiberSplit_eq_drop_encDec` |
  | `hde (in fiberSplitOfLawful)` | Used only in the none branch of the choice-free construction of fiberSplitOfLawful: if c.dec b = none, hde shows that no a has c.enc a = b. It is needed only to build this particular FiberSplit c.enc from c.dec without Classical.choice; classically every function f has a FiberSplit f (fiberSplit_exists_for_every_function, axioms [propext, Classical.choice, Quot.sound]), so no counterexample to the existence of FiberSplit c.enc without hde can exist. | `harmless` | — (`harmless`) |
  | `hed (in fiberSplitOfLawful)` | Used only in the some branch of the choice-free construction of fiberSplitOfLawful: if c.dec b = some a, hed gives the preimage witness c.enc a = b. It is needed only to build this particular FiberSplit c.enc from c.dec without Classical.choice; classically every function f has a FiberSplit f (fiberSplit_exists_for_every_function, axioms [propext, Classical.choice, Quot.sound]), so no counterexample to the existence of FiberSplit c.enc without hed can exist. | `harmless` | — (`harmless`) |

- **Non-vacuity witness:** `Toy.Codec.nv_codecOfFiberSplit_decEnc_of_injective`, `Toy.Codec.nv_codecOfFiberSplit_eq_of_lawful` — boolToNatCodec.enc : Bool → Nat is injective and admits computable boolToNatFiberSplit, with codecOfFiberSplit boolToNatCodec.enc boolToNatFiberSplit = boolToNatCodec.
- **Non-claims:**
  - Does not construct, without Classical.choice, a FiberSplit f for an arbitrary injection f without a lawful decoder (classically every function f has one: fiberSplit_exists_for_every_function, via the noncomputable classicalFiberSplit f); rather, together with fiberSplitOfLawful (Defs.lean), it establishes that FiberSplit f (decidable fibers) is both necessary and sufficient constructive data for a lawful decoder.
  - Does not imply that FiberSplit f alone forces Function.Injective f or DecEnc; constUnitFiberSplit splits fibers for the non-injective constant map Bool → Unit.
- **Prior art:**
  - agda-unimath, repository UniMath/agda-unimath, commit c0022bfc4e6f57fc84ca70d4d4e3aa568def5e3f, files src/foundation/decidable-maps.lagda.md and decidable-embeddings.lagda.md (is-decidable-map f and is-decidable-emb f).
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/Logic/Encodable/Basic.lean (Encodable.encodek, Encodable.decode₂, mem_decode₂, decode₂_isPartialInv, decidableRangeEncode) and Mathlib/Computability/Encoding.lean (Encoding.encode_injective).
- **Design question:** What constructive decidability data on an injective encoder f : A → B is both necessary and sufficient to build a lawful decoder without Classical.choice?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.codecOfFiberSplit_decEnc_of_injective`, `Toy.Codec.codecOfFiberSplit_eq_of_lawful`, `Toy.Codec.codecOfFiberSplit_encDec`, `Toy.Codec.fiberSplitOfLawful` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `codecOfFiberSplit_decEnc_of_injective`: none (`[]`); `codecOfFiberSplit_eq_of_lawful`: `Quot.sound`; `codecOfFiberSplit_encDec`: none (`[]`); `fiberSplitOfLawful`: none (`[]`).
- **Basis: derived (modeling bridge)** — In a constructive setting (such as writing an executable parser in Lean or extracting code without classical choice), implementing a lawful decoder for an injective encoder `f` is equivalent to supplying a constructive fiber-decision procedure `FiberSplit f` that either extracts a preimage or proves wire-input invalidity. Proving merely propositional decidability of image membership (`Decidable (∃ a, f a = b)`) does not extract the decoded value without choice or an explicit witness.

##### Card 7 (`lawful_dec_isSome_iff_mem_range`): `Toy.Codec.lawful_dec_isSome_iff_mem_range`, `Toy.Codec.junk_iff_not_in_image_of_lawful`

- **Kind:** `characterization` | **Tier:** `T0` (re-derivation: decoder acceptance domain equals encoder image (Isabelle `wb_prism.range_build`)) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `lawful_dec_isSome_iff_mem_range`: none (`[]`); `junk_iff_not_in_image_of_lawful`: none (`[]`)
- **Plain claim:** For any codec c : Codec A B satisfying DecEnc c and EncDec c, (c.dec b).isSome = true holds if and only if b lies in the image of c.enc (lawful_dec_isSome_iff_mem_range), and—as an immediate negated corollary (junk_iff_not_in_image_of_lawful, definitional via eq_none_iff_of_isSome_iff)—b belongs to Junk c (c.dec b = none) if and only if ∀ a : A, c.enc a ≠ b.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.lawful_dec_isSome_iff_mem_range.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    Toy.Codec.DecEnc c →
      Toy.Codec.EncDec c → ∀ (b : B), Option.isSome (c.dec b) = true ↔ ∃ a, c.enc a = b
  Toy.Codec.junk_iff_not_in_image_of_lawful.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    Toy.Codec.DecEnc c → Toy.Codec.EncDec c → ∀ (b : B), c.dec b = none ↔ ∀ (a : A), c.enc a ≠ b
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:211-213
  theorem lawful_dec_isSome_iff_mem_range {A : Type u} {B : Type v} (c : Codec A B)
      (hde : DecEnc c) (hed : EncDec c) :
      ∀ b : B, (c.dec b).isSome = true ↔ ∃ a : A, c.enc a = b

  -- lean/Toy/Codec/Statements.lean:225-227
  theorem junk_iff_not_in_image_of_lawful {A : Type u} {B : Type v} (c : Codec A B)
      (hde : DecEnc c) (hed : EncDec c) :
      ∀ b : B, c.dec b = none ↔ ∀ a : A, c.enc a ≠ b
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem lawful_dec_isSome_iff_mem_range {A : Type u} {B : Type v} (c : Codec A B)
      (hde : ∀ a : A, c.dec (c.enc a) = some a)
      (hed : ∀ (b : B) (a : A), c.dec b = some a → c.enc a = b) :
      ∀ b : B, (c.dec b).isSome = true ↔ ∃ a : A, c.enc a = b

  theorem junk_iff_not_in_image_of_lawful {A : Type u} {B : Type v} (c : Codec A B)
      (hde : ∀ a : A, c.dec (c.enc a) = some a)
      (hed : ∀ (b : B) (a : A), c.dec b = some a → c.enc a = b) :
      ∀ b : B, c.dec b = none ↔ ∀ a : A, c.enc a ≠ b
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `hde (in lawful_dec_isSome_iff_mem_range and junk_iff_not_in_image_of_lawful)` | Ensures every b in the image of c.enc yields isSome = true (and ≠ none); see mem_range_imp_isSome_of_decEnc. | `tight` | `Toy.Codec.ce_lawful_dec_isSome_drop_decEnc`, `Toy.Codec.ce_junk_iff_not_in_image_of_lawful_drop_decEnc` |
  | `hed (in lawful_dec_isSome_iff_mem_range and junk_iff_not_in_image_of_lawful)` | Ensures every accepted b (isSome = true) lies in the image of c.enc; see isSome_imp_mem_range_of_encDec. | `tight` | `Toy.Codec.ce_lawful_dec_isSome_drop_encDec`, `Toy.Codec.ce_junk_iff_not_in_image_of_lawful_drop_encDec` |

- **Non-vacuity witness:** `Toy.Codec.nv_lawful_dec_isSome_iff_mem_range`, `Toy.Codec.nv_junk_iff_not_in_image_of_lawful` — boolToNatCodec : Codec Bool Nat satisfies both DecEnc and EncDec (accepting 0 and 1 and rejecting n ≥ 2 as Junk).
- **Non-claims:**
  - Says nothing about computability. In Lean, `classicalCodec f` satisfies both laws for every injective `f`, including encoders whose image is undecidable. The reading 'a computable lawful decoder yields a computable membership test for the image' is a modeling remark, not part of the statement.
  - Does not assert that Junk c is inhabited (for bijective codecs such as Codec.id, Junk c is empty), nor does it constrain the runtime complexity of evaluating (c.dec b).isSome.
- **Prior art:**
  - Simon Foster, Christian Pardillo-Laursen, and Frank Zeyda, 'Optics', Archive of Formal Proofs, 2017, https://www.isa-afp.org/entries/Optics.html, official AFP Isabelle2026 release mirror isabelle-prover/mirror-afp-2026, commit 749ee1bd79285aeb2597f31d797d0e55d9af62c9, file thys/Optics/Prisms.thy (locale wb_prism with match_build, build_match, build_match_iff, range_build, inj_build, wb_prim_suml, wb_prim_sumr, and disjoint-range prism_plus_wb).
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/Logic/Encodable/Basic.lean (Encodable.encodek, Encodable.decode₂, mem_decode₂, decode₂_isPartialInv, decidableRangeEncode) and Mathlib/Computability/Encoding.lean (Encoding.encode_injective).
  - Tahina Ramananandro, Antoine Delignat-Lavaud, Cédric Fournet, Nikhil Swamy, Tej Chajed, Nadim Kobeissi, and Jonathan Protzenko, 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 2.1 defines parser correctness p(s(m)) = m, exactness p⁻¹(V) = s(V), non-malleability as parser injectivity on accepted inputs, and completeness as parser surjectivity; Section 2.2 ('Attacks on Parsers') describes attacks enabled by malleable or non-exact parsers (PKCS #1 signature forgery via a malleable or non-exact ASN.1 parser, and Bitcoin transaction malleability), alongside memory-safety bugs such as Heartbleed).
- **Design question:** Which wire values does a lawful decoder accept and which belong to its rejected complement Junk c?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.lawful_dec_isSome_iff_mem_range`, `Toy.Codec.junk_iff_not_in_image_of_lawful` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `lawful_dec_isSome_iff_mem_range`: none (`[]`); `junk_iff_not_in_image_of_lawful`: none (`[]`).
- **Basis: derived (modeling bridge)** — When an executable decoder satisfies both `DecEnc` and `EncDec`, running `(c.dec b).isSome` yields a sound and complete validator for membership in the serializer's image (and `c.dec b = none` characterizes invalid inputs `Junk c`). Because the Lean theorem itself applies equally to noncomputable decoders like `classicalCodec f`, the computability of that validator is a modeling remark rather than a consequence of the statement.

#### Part B: Single-Law Failure Modes and Canonicalization Escape Hatch

##### Card 8 (`decEnc_admits_malleable_codec`): `Toy.Codec.decEnc_admits_malleable_codec`

- **Kind:** `counterexample` | **Tier:** `T1` (folklore counterexample mechanized against `DecEnc`, `EncDec`, and `DecInj`) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `decEnc_admits_malleable_codec`: `propext`
- **Plain claim:** Demanding DecEnc alone does not prevent malleability: nonCanonicalBoolCodec : Codec Bool Nat satisfies DecEnc yet violates both EncDec and DecInj because the distinct wire values 1 and 2 both decode to true.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.decEnc_admits_malleable_codec : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
    ¬Toy.Codec.EncDec Toy.Codec.nonCanonicalBoolCodec ∧
      ¬Toy.Codec.DecInj Toy.Codec.nonCanonicalBoolCodec ∧
        1 ≠ 2 ∧
          Toy.Codec.nonCanonicalBoolCodec.dec 1 = some true ∧
            Toy.Codec.nonCanonicalBoolCodec.dec 2 = some true
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Counterexamples.lean:111-117
  theorem decEnc_admits_malleable_codec :
      DecEnc nonCanonicalBoolCodec ∧
      ¬ EncDec nonCanonicalBoolCodec ∧
      ¬ DecInj nonCanonicalBoolCodec ∧
      (1 : Nat) ≠ 2 ∧
      nonCanonicalBoolCodec.dec 1 = some true ∧
      nonCanonicalBoolCodec.dec 2 = some true
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem decEnc_admits_malleable_codec :
      (∀ a : Bool, nonCanonicalBoolCodec.dec (nonCanonicalBoolCodec.enc a) = some a) ∧
      ¬ (∀ (b : Nat) (a : Bool),
          nonCanonicalBoolCodec.dec b = some a → nonCanonicalBoolCodec.enc a = b) ∧
      ¬ (∀ (b₁ b₂ : Nat) (a : Bool),
          nonCanonicalBoolCodec.dec b₁ = some a → nonCanonicalBoolCodec.dec b₂ = some a → b₁ = b₂) ∧
      (1 : Nat) ≠ 2 ∧
      nonCanonicalBoolCodec.dec 1 = some true ∧
      nonCanonicalBoolCodec.dec 2 = some true
  ```
- **Hypothesis ledger:** None (unconditional statement).
- **Non-vacuity witness:** `Toy.Codec.decEnc_admits_malleable_codec` — nonCanonicalBoolCodec : Codec Bool Nat (false ↦ 0, true ↦ 1; dec 0 = some false, dec 1 = dec 2 = some true, dec (n + 3) = none).
- **Non-claims:**
  - Does not show that `EncDec` has to be established by a separate argument for each codec. When the wire type has decidable equality, wrapping a `DecEnc` decoder with a re-encode-and-compare check (`dec' b := match dec b with | some a => if enc a = b then some a else none | none => none`) gives a codec with the same encoder that satisfies both laws.
  - The laws are stated for one encoder function. A format that permits several encodings of one value cannot satisfy `EncDec` for any single encoder; for such formats the corresponding requirement is that the decoder accepts exactly the strings the format relates to the decoded value. Failing `EncDec` for a chosen encoder is therefore not by itself evidence that malformed input is accepted.
  - Does not show that every DecEnc-only codec is malleable; lawful codecs satisfy DecEnc without malleability.
- **Prior art:**
  - Tahina Ramananandro, Antoine Delignat-Lavaud, Cédric Fournet, Nikhil Swamy, Tej Chajed, Nadim Kobeissi, and Jonathan Protzenko, 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 2.1 defines parser correctness p(s(m)) = m, exactness p⁻¹(V) = s(V), non-malleability as parser injectivity on accepted inputs, and completeness as parser surjectivity; Section 2.2 ('Attacks on Parsers') describes attacks enabled by malleable or non-exact parsers (PKCS #1 signature forgery via a malleable or non-exact ASN.1 parser, and Bitcoin transaction malleability), alongside memory-safety bugs such as Heartbleed).
  - Benjamin Delaware, Sorawit Suriyakarn, Clément Pit-Claudel, Qianchuan Ye, and Adam Chlipala, 'Narcissus: Correct-by-Construction Derivation of Decoders and Encoders from Binary Formats', Proceedings of the ACM on Programming Languages 3 (ICFP), Article 82, 2019, DOI 10.1145/3341686 (Definition 2.2 requires both that every target in the format relation decodes to its source value and that every accepted target lies in the format relation; because a format is a relation rather than a single function, multiple encodings of one value may be valid without accepting malformed input, so functional EncDec relative to one chosen encoder need not hold).
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/Logic/Encodable/Basic.lean (Encodable.encodek, Encodable.decode₂, mem_decode₂, decode₂_isPartialInv, decidableRangeEncode) and Mathlib/Computability/Encoding.lean (Encoding.encode_injective).
- **Design question:** What concrete failure mode slips through when a serialization specification requires only the decode-after-encode law decode (encode a) = some a?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.decEnc_admits_malleable_codec` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `decEnc_admits_malleable_codec`: `propext`.
- **Basis: derived (modeling bridge)** — A specification or test suite checking only `decode (encode a) = some a` leaves a parser free to accept non-canonical encodings (such as non-minimal varints, nonzero padding, or duplicate representations), which in authenticated-message or signature-verification pipelines enables malleability bugs when downstream systems hash raw bytes. For formats defined relationally with multiple legitimate encodings, canonicality is instead a separate format-level policy.

##### Card 9 (`encDec_admits_always_failing_codec`): `Toy.Codec.encDec_admits_always_failing_codec`

- **Kind:** `counterexample` | **Tier:** `T1` (folklore counterexample mechanized against `EncDec` and `DecEnc`) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `encDec_admits_always_failing_codec`: none (`[]`)
- **Plain claim:** Demanding EncDec alone does not prevent vacuous rejection: alwaysFailBoolCodec : Codec Bool Bool satisfies EncDec yet violates DecEnc and returns none on every wire input.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.encDec_admits_always_failing_codec : Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
    ¬Toy.Codec.DecEnc Toy.Codec.alwaysFailBoolCodec ∧
      ∀ (b : Bool), Toy.Codec.alwaysFailBoolCodec.dec b = none
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Counterexamples.lean:123-126
  theorem encDec_admits_always_failing_codec :
      EncDec alwaysFailBoolCodec ∧
      ¬ DecEnc alwaysFailBoolCodec ∧
      (∀ b : Bool, alwaysFailBoolCodec.dec b = none)
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem encDec_admits_always_failing_codec :
      (∀ (b a : Bool), alwaysFailBoolCodec.dec b = some a → alwaysFailBoolCodec.enc a = b) ∧
      ¬ (∀ a : Bool, alwaysFailBoolCodec.dec (alwaysFailBoolCodec.enc a) = some a) ∧
      (∀ b : Bool, alwaysFailBoolCodec.dec b = none)
  ```
- **Hypothesis ledger:** None (unconditional statement).
- **Non-vacuity witness:** `Toy.Codec.encDec_admits_always_failing_codec` — alwaysFailBoolCodec : Codec Bool Bool (enc = id, dec _ = none).
- **Non-claims:**
  - Does not show that violating DecEnc forces total failure on every input; a partially failing decoder can accept some valid encodings and reject others while still satisfying EncDec.
  - Does not show that EncDec alone implies injectivity of enc (ce_decEnc_imp_enc_injective_drop_decEnc), nor that adding 'every encoding is accepted' without encoder injectivity rescues DecEnc (ce_codecOfFiberSplit_decEnc_drop_inj).
- **Prior art:**
  - Tahina Ramananandro, Antoine Delignat-Lavaud, Cédric Fournet, Nikhil Swamy, Tej Chajed, Nadim Kobeissi, and Jonathan Protzenko, 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 2.1 defines parser correctness p(s(m)) = m, exactness p⁻¹(V) = s(V), non-malleability as parser injectivity on accepted inputs, and completeness as parser surjectivity; Section 2.2 ('Attacks on Parsers') describes attacks enabled by malleable or non-exact parsers (PKCS #1 signature forgery via a malleable or non-exact ASN.1 parser, and Bitcoin transaction malleability), alongside memory-safety bugs such as Heartbleed).
  - Rocq Corelib SSReflect, repository rocq-prover/rocq, file theories/Corelib/ssr/ssrfun.v, commit 25f5b18a320e4796f181f938d3b74bebe7db4dc4 (pcancel, ocancel, pcan_inj, pcan_pcomp, ocan_comp) and Mathematical Components, repository math-comp/math-comp, file boot/eqtype.v, commit 1cf23375ae1948bc37a50f153a6fdd2338dacf98 (valK, insubK).
- **Design question:** What concrete failure mode slips through when a codec specification requires only the encode-after-decode law dec b = some a → enc a = b?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.encDec_admits_always_failing_codec` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `encDec_admits_always_failing_codec`: none (`[]`).
- **Basis: derived (modeling bridge)** — A specification checking only `decode b = some a → encode a = b` (or parser non-malleability `DecInj` alone) is vacuously satisfied by a parser that rejects every message, so canonicality specifications must always be paired with `DecEnc` (or a liveness/completeness guarantee).

##### Card 10 (`canonicalize_decEnc_of_decEnc`): `Toy.Codec.canonicalize_decEnc_of_decEnc`

- **Kind:** `theorem` | **Tier:** `T0` (re-derivation: re-encode-and-compare canonicalization (Mathlib `Encodable.decode₂`)) | **Depth:** `shallow`
- **Hashed companion theorem(s) (`lean_names`):** `Toy.Codec.canonicalize_encDec`
- **Verified axioms (`audit/axioms.json`):** `canonicalize_decEnc_of_decEnc`: `propext`; `canonicalize_encDec`: none (`[]`)
- **Plain claim:** Given a [DecidableEq B] instance on the wire type B (always available classically, and needed computably for an executable wrapper), wrapping any codec c : Codec A B satisfying DecEnc c in the re-encode-and-compare check canonicalize c preserves DecEnc (canonicalize_decEnc_of_decEnc) while guaranteeing EncDec (canonicalize c) unconditionally (canonicalize_encDec) with the identical encoder c.enc.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.canonicalize_decEnc_of_decEnc.{u, v} : ∀ {A : Type u} {B : Type v} [inst : DecidableEq B] (c : Toy.Codec.Codec A B),
    Toy.Codec.DecEnc c → Toy.Codec.DecEnc (Toy.Codec.canonicalize c)
  Toy.Codec.canonicalize_encDec.{u, v} : ∀ {A : Type u} {B : Type v} [inst : DecidableEq B] (c : Toy.Codec.Codec A B),
    Toy.Codec.EncDec (Toy.Codec.canonicalize c)
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:242-244
  theorem canonicalize_decEnc_of_decEnc {A : Type u} {B : Type v} [DecidableEq B]
      (c : Codec A B) (hde : DecEnc c) :
      DecEnc (canonicalize c)

  -- lean/Toy/Codec/Witnesses.lean:38-39
  theorem canonicalize_encDec {A : Type u} {B : Type v} [DecidableEq B]
      (c : Codec A B) : EncDec (canonicalize c)
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem canonicalize_decEnc_of_decEnc {A : Type u} {B : Type v} [DecidableEq B]
      (c : Codec A B) (hde : ∀ a : A, c.dec (c.enc a) = some a) :
      ∀ a : A, (canonicalize c).dec (c.enc a) = some a

  theorem canonicalize_encDec {A : Type u} {B : Type v} [DecidableEq B]
      (c : Codec A B) :
      ∀ (b : B) (a : A), (canonicalize c).dec b = some a → c.enc a = b
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `[DecidableEq B] (in canonicalize_decEnc_of_decEnc and canonicalize_encDec)` | Supplies the equality check c.enc a = b inside canonicalize; classically every type admits decidable equality (via Classical.propDecidable), so the theorem applies to every wire type B classically, while an executable wrapper requires a computable DecidableEq B instance. | `harmless` | — (`harmless`) |
  | `hde (in canonicalize_decEnc_of_decEnc)` | Ensures the underlying decoder c.dec returns some a on c.enc a before the equality guard c.enc a = c.enc a is checked. | `tight` | `Toy.Codec.ce_canonicalize_decEnc_drop_decEnc` |

- **Non-vacuity witness:** `Toy.Codec.nv_canonicalize_decEnc_of_decEnc` — nonCanonicalBoolCodec satisfies DecEnc while violating EncDec, and canonicalize nonCanonicalBoolCodec satisfies both DecEnc and EncDec (rejecting 2 while accepting 1).
- **Non-claims:**
  - Does not eliminate the runtime cost of re-encoding and comparing wire representations on every decode call (unlike zero-copy parsers that prove EncDec directly on the parser).
  - Classically every type B has decidable equality (via Classical.propDecidable), so canonicalize applies to every wire type B in logic; a computable DecidableEq B instance is needed only to obtain an executable wrapper. Moreover, canonicalize cannot repair a codec that violates DecEnc (ce_canonicalize_decEnc_drop_decEnc).
- **Prior art:**
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/Logic/Encodable/Basic.lean (Encodable.encodek, Encodable.decode₂, mem_decode₂, decode₂_isPartialInv, decidableRangeEncode) and Mathlib/Computability/Encoding.lean (Encoding.encode_injective).
- **Design question:** When a codec only satisfies DecEnc and wire equality is decidable, can it be systematically upgraded to satisfy both DecEnc and EncDec without changing its encoder?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.canonicalize_decEnc_of_decEnc`, `Toy.Codec.canonicalize_encDec` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `canonicalize_decEnc_of_decEnc`: `propext`; `canonicalize_encDec`: none (`[]`).
- **Basis: derived (modeling bridge)** — For wire types with a computable equality check (such as byte slices `List UInt8`), any `DecEnc`-verified parser can be turned into a canonical (`DecEnc ∧ EncDec`) parser without re-proving parser internals by re-encoding the decoded value and checking byte-for-byte equality—at the runtime cost of an extra encode and comparison per decode call (contrasting with zero-copy parsers that prove `EncDec` directly).

#### Part C: Closure Under Composition, Products, and Tagged Sums

##### Card 11 (`combinator_closure_decEnc_and_encDec`): `Toy.Codec.comp_decEnc`, `Toy.Codec.comp_encDec`, `Toy.Codec.prod_decEnc`, `Toy.Codec.prod_encDec`, `Toy.Codec.sum_decEnc`, `Toy.Codec.sum_encDec`

- **Kind:** `theorem` | **Tier:** `T0` (re-derivation: independent closure of `DecEnc` and `EncDec` under composition, products, and tagged sums) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `comp_decEnc`: none (`[]`); `comp_encDec`: none (`[]`); `prod_decEnc`: `propext`; `prod_encDec`: `propext`; `sum_decEnc`: none (`[]`); `sum_encDec`: none (`[]`)
- **Plain claim:** Each round-trip law (DecEnc and EncDec) is preserved independently of the other under sequential Kleisli composition c₁.comp c₂ (comp_decEnc, comp_encDec), componentwise products c₁.prod c₂ over B₁ × B₂ (prod_decEnc, prod_encDec), and tagged sums c₁.sum c₂ over B₁ ⊕ B₂ (sum_decEnc, sum_encDec); consequently, lawful codecs are closed under all three combinators.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.comp_decEnc.{u, v, w} : ∀ {A : Type u} {B : Type v} {C : Type w} (c₁ : Toy.Codec.Codec A B) (c₂ : Toy.Codec.Codec B C),
    Toy.Codec.DecEnc c₁ → Toy.Codec.DecEnc c₂ → Toy.Codec.DecEnc (Toy.Codec.Codec.comp c₁ c₂)
  Toy.Codec.comp_encDec.{u, v, w} : ∀ {A : Type u} {B : Type v} {C : Type w} (c₁ : Toy.Codec.Codec A B) (c₂ : Toy.Codec.Codec B C),
    Toy.Codec.EncDec c₁ → Toy.Codec.EncDec c₂ → Toy.Codec.EncDec (Toy.Codec.Codec.comp c₁ c₂)
  Toy.Codec.prod_decEnc.{u₁, u₂, v₁, v₂} : ∀ {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂} (c₁ : Toy.Codec.Codec A₁ B₁)
    (c₂ : Toy.Codec.Codec A₂ B₂),
    Toy.Codec.DecEnc c₁ → Toy.Codec.DecEnc c₂ → Toy.Codec.DecEnc (Toy.Codec.Codec.prod c₁ c₂)
  Toy.Codec.prod_encDec.{u₁, u₂, v₁, v₂} : ∀ {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂} (c₁ : Toy.Codec.Codec A₁ B₁)
    (c₂ : Toy.Codec.Codec A₂ B₂),
    Toy.Codec.EncDec c₁ → Toy.Codec.EncDec c₂ → Toy.Codec.EncDec (Toy.Codec.Codec.prod c₁ c₂)
  Toy.Codec.sum_decEnc.{u₁, u₂, v₁, v₂} : ∀ {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂} (c₁ : Toy.Codec.Codec A₁ B₁)
    (c₂ : Toy.Codec.Codec A₂ B₂),
    Toy.Codec.DecEnc c₁ → Toy.Codec.DecEnc c₂ → Toy.Codec.DecEnc (Toy.Codec.Codec.sum c₁ c₂)
  Toy.Codec.sum_encDec.{u₁, u₂, v₁, v₂} : ∀ {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂} (c₁ : Toy.Codec.Codec A₁ B₁)
    (c₂ : Toy.Codec.Codec A₂ B₂),
    Toy.Codec.EncDec c₁ → Toy.Codec.EncDec c₂ → Toy.Codec.EncDec (Toy.Codec.Codec.sum c₁ c₂)
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:254-257
  theorem comp_decEnc {A : Type u} {B : Type v} {C : Type w}
      (c₁ : Codec A B) (c₂ : Codec B C)
      (hde₁ : DecEnc c₁) (hde₂ : DecEnc c₂) :
      DecEnc (c₁.comp c₂)

  -- lean/Toy/Codec/Statements.lean:264-267
  theorem comp_encDec {A : Type u} {B : Type v} {C : Type w}
      (c₁ : Codec A B) (c₂ : Codec B C)
      (hed₁ : EncDec c₁) (hed₂ : EncDec c₂) :
      EncDec (c₁.comp c₂)

  -- lean/Toy/Codec/Statements.lean:279-282
  theorem prod_decEnc {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
      (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
      (hde₁ : DecEnc c₁) (hde₂ : DecEnc c₂) :
      DecEnc (c₁.prod c₂)

  -- lean/Toy/Codec/Statements.lean:289-292
  theorem prod_encDec {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
      (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
      (hed₁ : EncDec c₁) (hed₂ : EncDec c₂) :
      EncDec (c₁.prod c₂)

  -- lean/Toy/Codec/Statements.lean:308-311
  theorem sum_decEnc {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
      (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
      (hde₁ : DecEnc c₁) (hde₂ : DecEnc c₂) :
      DecEnc (c₁.sum c₂)

  -- lean/Toy/Codec/Statements.lean:322-325
  theorem sum_encDec {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
      (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
      (hed₁ : EncDec c₁) (hed₂ : EncDec c₂) :
      EncDec (c₁.sum c₂)
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem comp_decEnc {A : Type u} {B : Type v} {C : Type w}
      (c₁ : Codec A B) (c₂ : Codec B C)
      (hde₁ : ∀ a : A, c₁.dec (c₁.enc a) = some a)
      (hde₂ : ∀ b : B, c₂.dec (c₂.enc b) = some b) :
      ∀ a : A, (c₂.dec (c₂.enc (c₁.enc a))).bind c₁.dec = some a

  theorem comp_encDec {A : Type u} {B : Type v} {C : Type w}
      (c₁ : Codec A B) (c₂ : Codec B C)
      (hed₁ : ∀ (b : B) (a : A), c₁.dec b = some a → c₁.enc a = b)
      (hed₂ : ∀ (c : C) (b : B), c₂.dec c = some b → c₂.enc b = c) :
      ∀ (c : C) (a : A), (c₂.dec c).bind c₁.dec = some a → c₂.enc (c₁.enc a) = c

  theorem prod_decEnc {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
      (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
      (hde₁ : ∀ a₁ : A₁, c₁.dec (c₁.enc a₁) = some a₁)
      (hde₂ : ∀ a₂ : A₂, c₂.dec (c₂.enc a₂) = some a₂) :
      ∀ p : A₁ × A₂, (c₁.prod c₂).dec ((c₁.prod c₂).enc p) = some p

  theorem prod_encDec {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
      (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
      (hed₁ : ∀ (b₁ : B₁) (a₁ : A₁), c₁.dec b₁ = some a₁ → c₁.enc a₁ = b₁)
      (hed₂ : ∀ (b₂ : B₂) (a₂ : A₂), c₂.dec b₂ = some a₂ → c₂.enc a₂ = b₂) :
      ∀ (b : B₁ × B₂) (a : A₁ × A₂), (c₁.prod c₂).dec b = some a → (c₁.prod c₂).enc a = b

  theorem sum_decEnc {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
      (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
      (hde₁ : ∀ a₁ : A₁, c₁.dec (c₁.enc a₁) = some a₁)
      (hde₂ : ∀ a₂ : A₂, c₂.dec (c₂.enc a₂) = some a₂) :
      ∀ a : A₁ ⊕ A₂, (c₁.sum c₂).dec ((c₁.sum c₂).enc a) = some a

  theorem sum_encDec {A₁ : Type u₁} {B₁ : Type v₁} {A₂ : Type u₂} {B₂ : Type v₂}
      (c₁ : Codec A₁ B₁) (c₂ : Codec A₂ B₂)
      (hed₁ : ∀ (b₁ : B₁) (a₁ : A₁), c₁.dec b₁ = some a₁ → c₁.enc a₁ = b₁)
      (hed₂ : ∀ (b₂ : B₂) (a₂ : A₂), c₂.dec b₂ = some a₂ → c₂.enc a₂ = b₂) :
      ∀ (b : B₁ ⊕ B₂) (a : A₁ ⊕ A₂), (c₁.sum c₂).dec b = some a → (c₁.sum c₂).enc a = b
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `comp_decEnc.hde₁` | Recovers a from c₁.enc a after c₂.dec succeeds. | `tight` | `Toy.Codec.ce_comp_decEnc_drop_hde1` |
  | `comp_decEnc.hde₂` | Recovers c₁.enc a from c₂.enc (c₁.enc a). | `tight` | `Toy.Codec.ce_comp_decEnc_drop_hde2` |
  | `comp_encDec.hed₁` | Forces the intermediate b to equal c₁.enc a. | `tight` | `Toy.Codec.ce_comp_encDec_drop_hed1` |
  | `comp_encDec.hed₂` | Forces the outer wire value c to equal c₂.enc b. | `tight` | `Toy.Codec.ce_comp_encDec_drop_hed2` |
  | `prod_decEnc.hde₁` | Round-trips the first component of the pair. | `tight` | `Toy.Codec.ce_prod_decEnc_drop_hde1` |
  | `prod_decEnc.hde₂` | Round-trips the second component of the pair. | `tight` | `Toy.Codec.ce_prod_decEnc_drop_hde2` |
  | `prod_encDec.hed₁` | Enforces canonicality on the first component. | `tight` | `Toy.Codec.ce_prod_encDec_drop_hed1` |
  | `prod_encDec.hed₂` | Enforces canonicality on the second component. | `tight` | `Toy.Codec.ce_prod_encDec_drop_hed2` |
  | `sum_decEnc.hde₁` | Round-trips Sum.inl values. | `tight` | `Toy.Codec.ce_sum_decEnc_drop_hde1` |
  | `sum_decEnc.hde₂` | Round-trips Sum.inr values. | `tight` | `Toy.Codec.ce_sum_decEnc_drop_hde2` |
  | `sum_encDec.hed₁` | Enforces canonicality on Sum.inl wire values. | `tight` | `Toy.Codec.ce_sum_encDec_drop_hed1` |
  | `sum_encDec.hed₂` | Enforces canonicality on Sum.inr wire values. | `tight` | `Toy.Codec.ce_sum_encDec_drop_hed2` |

- **Non-vacuity witness:** `Toy.Codec.nv_comp_decEnc`, `Toy.Codec.nv_comp_encDec`, `Toy.Codec.nv_prod_decEnc`, `Toy.Codec.nv_prod_encDec`, `Toy.Codec.nv_sum_decEnc`, `Toy.Codec.nv_sum_encDec` — boolToNatCodec : Codec Bool Nat and natSuccCodec : Codec Nat Nat satisfy both DecEnc and EncDec across comp, prod, and sum.
- **Non-claims:**
  - For an untagged union of two codecs into a single shared wire type B, DecEnc under any decoder requires the two branch encoders to have disjoint images (untaggedSum_decEnc_imp_disjoint_images), and when both branches are lawful their left-biased untagged union untaggedSum c₁ c₂ is lawful if and only if ∀ a₁ a₂, c₁.enc a₁ ≠ c₂.enc a₂ (untaggedSum_lawful_iff_disjoint_images).
  - Codec.prod encodes into the structured pair type B₁ × B₂ rather than flat wire concatenation List β; for unseparated stream concatenation of two fields see FramedCodec.seq (framed_seq_closure) and lawful_injective_nonEmpty_enc_admits_ambiguous_concat.
  - Does not imply converse decomposition of laws from a composite codec back to its factors (for example, when c₁.enc is non-surjective in comp, when one factor domain is empty in prod_decEnc, or when one factor decoder always returns none in comp_encDec / prod_encDec).
- **Prior art:**
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/Logic/Function/Basic.lean (Function.IsPartialInv, IsPartialInv.injective, injective_of_isPartialInv_right, IsPartialInv.comp, Function.partialInv, Injective.isPartialInv, partialInv_left) and Mathlib/Basic/PEquiv.lean (PEquiv).
  - Rocq Corelib SSReflect, repository rocq-prover/rocq, file theories/Corelib/ssr/ssrfun.v, commit 25f5b18a320e4796f181f938d3b74bebe7db4dc4 (pcancel, ocancel, pcan_inj, pcan_pcomp, ocan_comp) and Mathematical Components, repository math-comp/math-comp, file boot/eqtype.v, commit 1cf23375ae1948bc37a50f153a6fdd2338dacf98 (valK, insubK).
  - Tillmann Rendel and Klaus Ostermann, 'Invertible syntax descriptions: unifying parsing and pretty printing', Proceedings of the Third ACM Haskell Symposium on Haskell (Haskell '10), pp. 1–12, 2010, DOI 10.1145/1863523.1863525 (defines partial isomorphisms as pairs α → Maybe β and β → Maybe α, with Category composition and product combinator (***) in Hackage package partial-isomorphisms-0.2.4.0; Codec specializes this shape to a total encoder).
  - Matthew Pickering, Jeremy Gibbons, and Nicolas Wu, 'Profunctor Optics: Modular Data Accessors', The Art, Science, and Engineering of Programming, vol. 1, no. 2, article 7, 2017, DOI 10.22152/programming-journal.org/2017/1/7 (concrete prisms as match/build pairs formally dual to lenses, and profunctor composition; does not formalize prism laws).
  - Bryce Clarke, Derek Elkins, Jeremy Gibbons, Fosco Loregian, Bartosz Milewski, Emily Pillmore, and Mario Román, 'Profunctor Optics, a Categorical Update', Compositionality, vol. 6, article 1, 2024, DOI 10.32408/compositionality-6-1 (Section 3.1.6 defines prisms as mixed optics for the coproduct action; lawfulness is not treated there).
  - Simon Foster, Christian Pardillo-Laursen, and Frank Zeyda, 'Optics', Archive of Formal Proofs, 2017, https://www.isa-afp.org/entries/Optics.html, official AFP Isabelle2026 release mirror isabelle-prover/mirror-afp-2026, commit 749ee1bd79285aeb2597f31d797d0e55d9af62c9, file thys/Optics/Prisms.thy (locale wb_prism with match_build, build_match, build_match_iff, range_build, inj_build, wb_prim_suml, wb_prim_sumr, and disjoint-range prism_plus_wb).
  - Tillmann Rendel and Klaus Ostermann, Hackage package partial-isomorphisms-0.2.4.0, module Control.Isomorphism.Partial.Prim (the untagged sum combinator (|||) :: Iso alpha gamma -> Iso beta gamma -> Iso (Either alpha beta) gamma is documented as 'not a proper partial isomorphism because of mplus').
- **Design question:** Do DecEnc and EncDec close modularly and independently across sequential pipelines, structured tuple pairs, and tagged sum variants?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.comp_decEnc`, `Toy.Codec.comp_encDec`, `Toy.Codec.prod_decEnc`, `Toy.Codec.prod_encDec`, `Toy.Codec.sum_decEnc`, `Toy.Codec.sum_encDec` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `comp_decEnc`: none (`[]`); `comp_encDec`: none (`[]`); `prod_decEnc`: `propext`; `prod_encDec`: `propext`; `sum_decEnc`: none (`[]`); `sum_encDec`: none (`[]`).
- **Basis: derived (modeling bridge)** — Codec pipelines, structured tuple codecs (`B₁ × B₂`), and explicitly tagged sum codecs (`B₁ ⊕ B₂`) preserve `DecEnc` and `EncDec` modularly and independently, so libraries built from these combinators can verify each law once per combinator. Real flat-byte serializers that concatenate tuple fields without an external boundary or merge sum branches without disjoint tags must additionally satisfy framing (`FramedCodec.seq`) or image-disjointness obligations.

#### Part D: Framed Codecs and Concatenation Over `List β`

##### Card 12 (`framed_lawful_iff_decPrefix_eq_some_iff`): `Toy.Codec.framed_lawful_iff_decPrefix_eq_some_iff`

- **Kind:** `characterization` | **Tier:** `T0` (re-derivation: framed analogue of the partial-inverse graph characterization) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `framed_lawful_iff_decPrefix_eq_some_iff`: none (`[]`)
- **Plain claim:** For any framed codec fc : FramedCodec A β, satisfying both PrefixDecEnc fc and PrefixEncDec fc is equivalent to fc.decPrefix xs = some (a, rest) holding if and only if xs = fc.enc a ++ rest.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.framed_lawful_iff_decPrefix_eq_some_iff.{u, v} : ∀ {A : Type u} {β : Type v} (fc : Toy.Codec.FramedCodec A β),
    Toy.Codec.PrefixDecEnc fc ∧ Toy.Codec.PrefixEncDec fc ↔
      ∀ (xs : List β) (a : A) (rest : List β),
        fc.decPrefix xs = some (a, rest) ↔ xs = fc.enc a ++ rest
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:344-348
  theorem framed_lawful_iff_decPrefix_eq_some_iff {A : Type u} {β : Type v}
      (fc : FramedCodec A β) :
      (PrefixDecEnc fc ∧ PrefixEncDec fc) ↔
        (∀ (xs : List β) (a : A) (rest : List β),
          fc.decPrefix xs = some (a, rest) ↔ xs = fc.enc a ++ rest)
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem framed_lawful_iff_decPrefix_eq_some_iff {A : Type u} {β : Type v}
      (fc : FramedCodec A β) :
      ((∀ (a : A) (rest : List β), fc.decPrefix (fc.enc a ++ rest) = some (a, rest)) ∧
       (∀ (xs : List β) (a : A) (rest : List β),
         fc.decPrefix xs = some (a, rest) → xs = fc.enc a ++ rest)) ↔
      (∀ (xs : List β) (a : A) (rest : List β),
        fc.decPrefix xs = some (a, rest) ↔ xs = fc.enc a ++ rest)
  ```
- **Hypothesis ledger:** None (unconditional statement).
- **Non-vacuity witness:** `Toy.Codec.nv_framed_lawful_iff_decPrefix_eq_some_iff` — varLenBoolFramedCodec : FramedCodec Bool Bool (false ↦ [false], true ↦ [true, true]) satisfies both sides of the equivalence.
- **Non-claims:**
  - A framed codec satisfying `PrefixDecEnc` (even when `PrefixEncDec` also holds) does not become a lawful whole-input codec by discarding the remainder: `firstOnly fc` (`xs ↦ (fc.decPrefix xs).map Prod.fst`) satisfies `DecEnc`, yet whenever `A` and the token type `β` are inhabited it violates both `DecInj` and `EncDec` (proved in general as `firstOnly_decEnc_and_not_decInj`, and instantiated on `varLenBoolFramedCodec` in `framed_lawful_but_firstOnly_not_decInj`). Converting `decPrefix` into a lawful whole-input decoder requires checking `rest = []`.
  - Does not imply NonEmptyEnc fc.enc; emptyUnitFramedCodec satisfies both PrefixDecEnc and PrefixEncDec on Unit while encoding () to [].
- **Prior art:**
  - Dimitrios Vytiniotis and Andrew J. Kennedy, 'Functional pearl: every bit counts', Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming (ICFP '10), pp. 15–26, 2010, DOI 10.1145/1863543.1863548 (Section 3, Coq-checked Lemma 1 for PrefixDecEnc, Corollary 1 for encoder injectivity, Corollary 2 for indexed PrefixFree, and Lemma 3 for PrefixEncDec); journal version: Andrew J. Kennedy and Dimitrios Vytiniotis, 'Every bit counts: The binary representation of typed data and programs', Journal of Functional Programming 22(4–5), pp. 529–573, 2012, DOI 10.1017/S0956796812000263.
  - Benjamin Delaware, Sorawit Suriyakarn, Clément Pit-Claudel, Qianchuan Ye, and Adam Chlipala, 'Narcissus: Correct-by-Construction Derivation of Decoders and Encoders from Binary Formats', Proceedings of the ACM on Programming Languages 3 (ICFP), Article 82, 2019, DOI 10.1145/3341686 (Definition 3.1, decoder-combinator soundness on t · t' returning the decoded view and exact remainder t').
  - Tahina Ramananandro et al., 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 5, Definitions 1–2 on prefix non-malleability and the strong prefix property for sequenced parsers; Section 5.1 on plist[p] rejecting zero-byte steps and consuming all input without itself having the strong prefix property).
- **Design question:** What single relational specification on a streaming prefix decoder decPrefix is equivalent to demanding both PrefixDecEnc and PrefixEncDec?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.framed_lawful_iff_decPrefix_eq_some_iff` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `framed_lawful_iff_decPrefix_eq_some_iff`: none (`[]`).
- **Basis: derived (modeling bridge)** — For streaming / combinator parsers that consume a prefix of a byte buffer and return the unconsumed tail, specifying both `PrefixDecEnc` and `PrefixEncDec` fixes the parser's behavior to match `xs = enc a ++ rest` exactly. Converting a lawful prefix parser into a lawful whole-message parser requires checking that `rest = []`, because discarding trailing bytes violates whole-input non-malleability whenever source and token types are inhabited (`firstOnly_decEnc_and_not_decInj`, `framed_lawful_but_firstOnly_not_decInj`).

##### Card 13 (`prefixDecEnc_imp_prefixFree`): `Toy.Codec.prefixDecEnc_imp_prefixFree`

- **Kind:** `theorem` | **Tier:** `T0` (re-derivation: Vytiniotis–Kennedy Corollary 2 from Lemma 1) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `prefixDecEnc_imp_prefixFree`: `propext`
- **Plain claim:** For any framed codec fc : FramedCodec A β, the prefix round-trip law PrefixDecEnc fc alone implies PrefixFree fc.enc: fc.enc is injective and no codeword is a prefix of another distinct value's codeword.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.prefixDecEnc_imp_prefixFree.{u, v} : ∀ {A : Type u} {β : Type v} (fc : Toy.Codec.FramedCodec A β),
    Toy.Codec.PrefixDecEnc fc → Toy.Codec.PrefixFree fc.enc
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:357-359
  theorem prefixDecEnc_imp_prefixFree {A : Type u} {β : Type v}
      (fc : FramedCodec A β) (hpde : PrefixDecEnc fc) :
      PrefixFree fc.enc
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem prefixDecEnc_imp_prefixFree {A : Type u} {β : Type v}
      (fc : FramedCodec A β)
      (hpde : ∀ (a : A) (rest : List β), fc.decPrefix (fc.enc a ++ rest) = some (a, rest)) :
      ∀ (a₁ a₂ : A) (s : List β), fc.enc a₁ ++ s = fc.enc a₂ → a₁ = a₂
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `hpde` | Evaluates decPrefix on enc a₁ ++ s = enc a₂ ++ [] in two ways, forcing a₁ = a₂. | `tight` | `Toy.Codec.ce_prefixDecEnc_imp_prefixFree_drop_hpde` |

- **Non-vacuity witness:** `Toy.Codec.nv_prefixDecEnc_imp_prefixFree` — varLenBoolFramedCodec : FramedCodec Bool Bool satisfies PrefixDecEnc.
- **Non-claims:**
  - Does not show the converse, that a prefix-free encoder admits a prefix decoder satisfying `PrefixDecEnc`; that converse is neither stated nor proved in this package (not examined).
  - A framed codec satisfying `PrefixDecEnc` (even when `PrefixEncDec` also holds) does not become a lawful whole-input codec by discarding the remainder: `firstOnly fc` (`xs ↦ (fc.decPrefix xs).map Prod.fst`) satisfies `DecEnc`, yet whenever `A` and the token type `β` are inhabited it violates both `DecInj` and `EncDec` (proved in general as `firstOnly_decEnc_and_not_decInj`, and instantiated on `varLenBoolFramedCodec` in `framed_lawful_but_firstOnly_not_decInj`). Converting `decPrefix` into a lawful whole-input decoder requires checking `rest = []`.
  - PrefixFree fc.enc bundles Function.Injective fc.enc with set-level proper-prefix-freeness ImagePrefixFree fc.enc (proved in Witnesses.lean as prefixFree_iff_injective_and_imagePrefixFree; contrast const_imagePrefixFree_not_prefixFree in Counterexamples.lean and Mathlib InformationTheory.IsPrefixFree).
  - Does not imply NonEmptyEnc fc.enc on subsingleton types (emptyUnitFramedCodec), and does not claim PrefixFree is necessary for whole-list unique decodability (suffixEnc_not_prefixFree_yet_concat_lawful).
- **Prior art:**
  - Dimitrios Vytiniotis and Andrew J. Kennedy, 'Functional pearl: every bit counts', Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming (ICFP '10), pp. 15–26, 2010, DOI 10.1145/1863543.1863548 (Section 3, Coq-checked Lemma 1 for PrefixDecEnc, Corollary 1 for encoder injectivity, Corollary 2 for indexed PrefixFree, and Lemma 3 for PrefixEncDec); journal version: Andrew J. Kennedy and Dimitrios Vytiniotis, 'Every bit counts: The binary representation of typed data and programs', Journal of Functional Programming 22(4–5), pp. 529–573, 2012, DOI 10.1017/S0956796812000263.
  - Benjamin Delaware, Sorawit Suriyakarn, Clément Pit-Claudel, Qianchuan Ye, and Adam Chlipala, 'Narcissus: Correct-by-Construction Derivation of Decoders and Encoders from Binary Formats', Proceedings of the ACM on Programming Languages 3 (ICFP), Article 82, 2019, DOI 10.1145/3341686 (Definition 3.1, decoder-combinator soundness on t · t' returning the decoded view and exact remainder t').
  - Tahina Ramananandro et al., 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 5, Definitions 1–2 on prefix non-malleability and the strong prefix property for sequenced parsers; Section 5.1 on plist[p] rejecting zero-byte steps and consuming all input without itself having the strong prefix property).
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/InformationTheory/Coding/PrefixFree.lean and UniquelyDecodable.lean (IsPrefixFree, IsPrefixFree.eq_singleton_empty_of_empty_mem, IsPrefixFree.isUniquelyDecodable, IsPrefixFree.isUniquelyDecodable_of_nontrivial, IsUniquelyDecodable.epsilon_notMem).
- **Design question:** Why does requiring a lookahead-free streaming prefix decoder (PrefixDecEnc) force the encoder to be injective with a prefix-free codeword image?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.prefixDecEnc_imp_prefixFree` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `prefixDecEnc_imp_prefixFree`: `propext`.
- **Basis: derived (modeling bridge)** — Any streaming parser combinator that succeeds independently of trailing bytes (`PrefixDecEnc`, corresponding to EverParse's strong prefix property) forces its serializer's codewords to be injective and prefix-free; formats whose codewords are prefixes of one another cannot be given lookahead-free streaming prefix decoders.

##### Card 14 (`framed_seq_closure`): `Toy.Codec.seq_prefixDecEnc`, `Toy.Codec.seq_prefixEncDec`

- **Kind:** `theorem` | **Tier:** `T0` (re-derivation: closure of framed prefix codecs under heterogeneous concatenation) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `seq_prefixDecEnc`: `propext`; `seq_prefixEncDec`: `propext`
- **Plain claim:** For any framed codecs fc₁ : FramedCodec A₁ β and fc₂ : FramedCodec A₂ β over a shared token type β, their sequential concatenation fc₁.seq fc₂ : FramedCodec (A₁ × A₂) β preserves PrefixDecEnc when both factors satisfy PrefixDecEnc (seq_prefixDecEnc) and preserves PrefixEncDec when both factors satisfy PrefixEncDec (seq_prefixEncDec), requiring neither the opposite law nor NonEmptyEnc.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.seq_prefixDecEnc.{v, u₁, u₂} : ∀ {A₁ : Type u₁} {A₂ : Type u₂} {β : Type v} (fc₁ : Toy.Codec.FramedCodec A₁ β)
    (fc₂ : Toy.Codec.FramedCodec A₂ β),
    Toy.Codec.PrefixDecEnc fc₁ →
      Toy.Codec.PrefixDecEnc fc₂ → Toy.Codec.PrefixDecEnc (Toy.Codec.FramedCodec.seq fc₁ fc₂)
  Toy.Codec.seq_prefixEncDec.{v, u₁, u₂} : ∀ {A₁ : Type u₁} {A₂ : Type u₂} {β : Type v} (fc₁ : Toy.Codec.FramedCodec A₁ β)
    (fc₂ : Toy.Codec.FramedCodec A₂ β),
    Toy.Codec.PrefixEncDec fc₁ →
      Toy.Codec.PrefixEncDec fc₂ → Toy.Codec.PrefixEncDec (Toy.Codec.FramedCodec.seq fc₁ fc₂)
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:368-371
  theorem seq_prefixDecEnc {A₁ : Type u₁} {A₂ : Type u₂} {β : Type v}
      (fc₁ : FramedCodec A₁ β) (fc₂ : FramedCodec A₂ β)
      (hpde₁ : PrefixDecEnc fc₁) (hpde₂ : PrefixDecEnc fc₂) :
      PrefixDecEnc (fc₁.seq fc₂)

  -- lean/Toy/Codec/Statements.lean:381-384
  theorem seq_prefixEncDec {A₁ : Type u₁} {A₂ : Type u₂} {β : Type v}
      (fc₁ : FramedCodec A₁ β) (fc₂ : FramedCodec A₂ β)
      (hped₁ : PrefixEncDec fc₁) (hped₂ : PrefixEncDec fc₂) :
      PrefixEncDec (fc₁.seq fc₂)
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem seq_prefixDecEnc {A₁ : Type u₁} {A₂ : Type u₂} {β : Type v}
      (fc₁ : FramedCodec A₁ β) (fc₂ : FramedCodec A₂ β)
      (hpde₁ : ∀ (a₁ : A₁) (rest : List β), fc₁.decPrefix (fc₁.enc a₁ ++ rest) = some (a₁, rest))
      (hpde₂ : ∀ (a₂ : A₂) (rest : List β), fc₂.decPrefix (fc₂.enc a₂ ++ rest) = some (a₂, rest)) :
      ∀ (p : A₁ × A₂) (rest : List β),
        (fc₁.seq fc₂).decPrefix ((fc₁.seq fc₂).enc p ++ rest) = some (p, rest)

  theorem seq_prefixEncDec {A₁ : Type u₁} {A₂ : Type u₂} {β : Type v}
      (fc₁ : FramedCodec A₁ β) (fc₂ : FramedCodec A₂ β)
      (hped₁ : ∀ (xs : List β) (a₁ : A₁) (rest : List β),
        fc₁.decPrefix xs = some (a₁, rest) → xs = fc₁.enc a₁ ++ rest)
      (hped₂ : ∀ (xs : List β) (a₂ : A₂) (rest : List β),
        fc₂.decPrefix xs = some (a₂, rest) → xs = fc₂.enc a₂ ++ rest) :
      ∀ (xs : List β) (p : A₁ × A₂) (rest : List β),
        (fc₁.seq fc₂).decPrefix xs = some (p, rest) → xs = (fc₁.seq fc₂).enc p ++ rest
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `seq_prefixDecEnc.hpde₁` | Strips fc₁.enc p.1 and passes the exact remainder fc₂.enc p.2 ++ rest to fc₂.decPrefix. | `tight` | `Toy.Codec.ce_seq_prefixDecEnc_drop_h1` |
  | `seq_prefixDecEnc.hpde₂` | Strips fc₂.enc p.2 from the intermediate remainder and preserves rest. | `tight` | `Toy.Codec.ce_seq_prefixDecEnc_drop_h2` |
  | `seq_prefixEncDec.hped₁` | Reconstructs xs = fc₁.enc a₁ ++ rest₁ from the first prefix parse. | `tight` | `Toy.Codec.ce_seq_prefixEncDec_drop_h1` |
  | `seq_prefixEncDec.hped₂` | Reconstructs rest₁ = fc₂.enc a₂ ++ rest from the second prefix parse. | `tight` | `Toy.Codec.ce_seq_prefixEncDec_drop_h2` |

- **Non-vacuity witness:** `Toy.Codec.nv_seq_prefixDecEnc`, `Toy.Codec.nv_seq_prefixEncDec` — varLenBoolFramedCodec sequenced with itself satisfies both PrefixDecEnc and PrefixEncDec.
- **Non-claims:**
  - Unlike uncounted variable-length listCodec, finite fixed-arity record sequencing fc₁.seq fc₂ does not require NonEmptyEnc (zero-width Unit fields compose cleanly in a fixed tuple).
  - Does not apply when fc₁ only satisfies whole-input DecEnc rather than PrefixDecEnc (see lawful_injective_nonEmpty_enc_admits_ambiguous_concat and Narcissus Section 3).
- **Prior art:**
  - Tahina Ramananandro et al., 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 5, Definitions 1–2 on prefix non-malleability and the strong prefix property for sequenced parsers; Section 5.1 on plist[p] rejecting zero-byte steps and consuming all input without itself having the strong prefix property).
  - Benjamin Delaware, Sorawit Suriyakarn, Clément Pit-Claudel, Qianchuan Ye, and Adam Chlipala, 'Narcissus: Correct-by-Construction Derivation of Decoders and Encoders from Binary Formats', Proceedings of the ACM on Programming Languages 3 (ICFP), Article 82, 2019, DOI 10.1145/3341686 (Definition 3.1, decoder-combinator soundness on t · t' returning the decoded view and exact remainder t').
  - Dimitrios Vytiniotis and Andrew J. Kennedy, 'Functional pearl: every bit counts', Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming (ICFP '10), pp. 15–26, 2010, DOI 10.1145/1863543.1863548 (Section 3, Coq-checked Lemma 1 for PrefixDecEnc, Corollary 1 for encoder injectivity, Corollary 2 for indexed PrefixFree, and Lemma 3 for PrefixEncDec); journal version: Andrew J. Kennedy and Dimitrios Vytiniotis, 'Every bit counts: The binary representation of typed data and programs', Journal of Functional Programming 22(4–5), pp. 529–573, 2012, DOI 10.1017/S0956796812000263.
- **Design question:** When two heterogeneous fields are serialized back-to-back onto a single flat token stream without an external separator, which laws make their combined record codec composable?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.seq_prefixDecEnc`, `Toy.Codec.seq_prefixEncDec` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `seq_prefixDecEnc`: `propext`; `seq_prefixEncDec`: `propext`.
- **Basis: derived (modeling bridge)** — Fixed-arity record or struct serialization over a flat byte stream composes cleanly without field separators or non-emptiness constraints (even when some fields are zero-width `Unit` markers) as long as each field parser satisfies the prefix laws (`PrefixDecEnc` / `PrefixEncDec`).

##### Card 15 (`listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc`): `Toy.Codec.listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc`

- **Kind:** `characterization` | **Tier:** `T0` (re-derivation: repeat-until-exhausted list round-trip (LowParse `bare_serialize_list_correct`; Mathlib `IsPrefixFree.isUniquelyDecodable`)) | **Depth:** `shallow`
- **Hashed companion theorem(s) (`lean_names`):** `Toy.Codec.nonEmptyEnc_of_prefixDecEnc_of_ne`
- **Verified axioms (`audit/axioms.json`):** `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc`: `Quot.sound`, `propext`; `nonEmptyEnc_of_prefixDecEnc_of_ne`: `propext`
- **Plain claim:** For any framed codec fc : FramedCodec A β satisfying PrefixDecEnc fc, the induced whole-input list codec listCodec fc satisfies DecEnc if and only if every codeword is non-empty (NonEmptyEnc fc.enc); moreover, when A has two distinct elements, NonEmptyEnc fc.enc follows automatically from PrefixDecEnc fc (nonEmptyEnc_of_prefixDecEnc_of_ne).
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc.{u, v} : ∀ {A : Type u} {β : Type v} (fc : Toy.Codec.FramedCodec A β),
    Toy.Codec.PrefixDecEnc fc →
      (Toy.Codec.DecEnc (Toy.Codec.listCodec fc) ↔ Toy.Codec.NonEmptyEnc fc.enc)
  Toy.Codec.nonEmptyEnc_of_prefixDecEnc_of_ne.{u, v} : ∀ {A : Type u} {β : Type v} (fc : Toy.Codec.FramedCodec A β),
    Toy.Codec.PrefixDecEnc fc → ∀ {x y : A}, x ≠ y → Toy.Codec.NonEmptyEnc fc.enc
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:410-412
  theorem listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc {A : Type u} {β : Type v}
      (fc : FramedCodec A β) (hpde : PrefixDecEnc fc) :
      DecEnc (listCodec fc) ↔ NonEmptyEnc fc.enc

  -- lean/Toy/Codec/Witnesses.lean:158-160
  theorem nonEmptyEnc_of_prefixDecEnc_of_ne {A : Type u} {β : Type v}
      (fc : FramedCodec A β) (hpde : PrefixDecEnc fc) {x y : A} (hxy : x ≠ y) :
      NonEmptyEnc fc.enc
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc {A : Type u} {β : Type v}
      (fc : FramedCodec A β)
      (hpde : ∀ (a : A) (rest : List β), fc.decPrefix (fc.enc a ++ rest) = some (a, rest)) :
      (∀ as : List A, decList fc (encList fc.enc as) = some as) ↔
        (∀ a : A, fc.enc a ≠ [])

  theorem nonEmptyEnc_of_prefixDecEnc_of_ne {A : Type u} {β : Type v}
      (fc : FramedCodec A β)
      (hpde : ∀ (a : A) (rest : List β), fc.decPrefix (fc.enc a ++ rest) = some (a, rest))
      {x y : A} (hxy : x ≠ y) :
      ∀ a : A, fc.enc a ≠ []
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `hpde (in listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc)` | Sufficient (not necessary) framing condition under which decList strips each leading non-empty codeword fc.enc a; the forward direction DecEnc (listCodec fc) → NonEmptyEnc fc.enc holds unconditionally (nonEmptyEnc_of_listCodec_decEnc), while NonEmptyEnc fails under PrefixDecEnc only on subsingleton types (ce_listCodec_decEnc_drop_nonEmptyEnc). | `tight` | `Toy.Codec.ce_listCodec_decEnc_iff_drop_prefixDecEnc` |
  | `hpde (in nonEmptyEnc_of_prefixDecEnc_of_ne)` | Prevents distinct elements x ≠ y from sharing an empty codeword []; without PrefixDecEnc, emptyBoolFailFramedCodec on Bool (false ≠ true) satisfies PrefixEncDec while mapping every value to []. | `tight` | `Toy.Codec.ce_nonEmptyEnc_of_prefixDecEnc_of_ne_drop_hpde` |
  | `hxy (in nonEmptyEnc_of_prefixDecEnc_of_ne)` | Supplies two distinct elements x ≠ y : A so fc.enc cannot map any element to [] under PrefixDecEnc; on the subsingleton type Unit (where no x ≠ y exists), emptyUnitFramedCodec satisfies PrefixDecEnc while violating NonEmptyEnc. | `tight` | `Toy.Codec.ce_listCodec_decEnc_drop_nonEmptyEnc` |

- **Non-vacuity witness:** `Toy.Codec.nv_listCodec_decEnc_iff_nonEmptyEnc`, `Toy.Codec.nv_nonEmptyEnc_of_prefixDecEnc_of_ne` — varLenBoolFramedCodec on Bool (false ≠ true) satisfies PrefixDecEnc with NonEmptyEnc and DecEnc (listCodec _) both true (instantiating both listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc and nonEmptyEnc_of_prefixDecEnc_of_ne), whereas emptyUnitFramedCodec satisfies PrefixDecEnc on Unit with both sides of the iff false.
- **Non-claims:**
  - Under `PrefixDecEnc`, `NonEmptyEnc` can fail only if all values of `A` are equal (`prefixDecEnc_nil_codeword_imp_subsingleton`); for a type with two distinct values it is automatic (`nonEmptyEnc_of_prefixDecEnc_of_ne`).
  - Does not show that `PrefixDecEnc` is necessary for `DecEnc (listCodec fc)`: `lenientFc` violates `PrefixDecEnc` on arbitrary remainders yet satisfies `DecEnc (listCodec lenientFc)` because its prefix decoder succeeds whenever the remainder is itself a concatenation of codewords (`lenient_not_prefixDecEnc_yet_listCodec_decEnc`).
  - `listCodec fc` is a whole-input codec. Its encoder `encList fc.enc` is not prefix-free whenever `A` is inhabited (`encList_not_prefixFree`), so no framed codec with that encoder satisfies `PrefixDecEnc` (`no_prefixDecEnc_for_encList`). Consequently the package's sequencing theorem `seq_prefixDecEnc`, which assumes `PrefixDecEnc` for both fields, does not apply to a `FramedCodec.seq` record that has a list encoded this way as a field (for example as the first field, followed by further data), and `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` does not apply when the list elements are themselves such lists. The package therefore gives no general guarantee that such a layout decodes correctly, but this is not an impossibility result: in general such a layout needs extra framing (such as a length prefix or a terminator) or a separate argument that the following tokens cannot be read as list elements. `bareList_first_field_lawful` proves a lawful `seq` record whose first field is a bare `encList`-encoded list, with no length prefix or terminator, followed by a field whose codewords share no token with the element codewords. Nesting such lists directly inside another bare `encList`-encoded list does make the outer encoder non-injective (derived: for any `a : A`, `encList (encList enc)` maps both `[[a], [a]]` and `[[a, a]]` to `enc a ++ enc a`).
  - A framed codec satisfying `PrefixDecEnc` (even when `PrefixEncDec` also holds) does not become a lawful whole-input codec by discarding the remainder: `firstOnly fc` (`xs ↦ (fc.decPrefix xs).map Prod.fst`) satisfies `DecEnc`, yet whenever `A` and the token type `β` are inhabited it violates both `DecInj` and `EncDec` (proved in general as `firstOnly_decEnc_and_not_decInj`, and instantiated on `varLenBoolFramedCodec` in `framed_lawful_but_firstOnly_not_decInj`). Converting `decPrefix` into a lawful whole-input decoder requires checking `rest = []`.
  - Does not imply EncDec (listCodec fc) unless PrefixEncDec fc also holds (listCodec_encDec_of_prefixEncDec), and does not cover length-prefixed list formats, which transmit element counts explicitly and therefore permit zero-width Unit elements.
- **Prior art:**
  - EverParse / LowParse mechanization, repository project-everest/everparse, commit f3e4ce51d9b68593fd98472cadcdeb8b6abf388f, file lib/everparse/lowparse/LowParse.Spec.List.fsti (parse_list_aux with zero-progress rejection, serialize_list_precond requiring ParserStrong and parser_kind_low > 0, bare_serialize_list_correct, and parse_list_bare_injective).
  - Tahina Ramananandro et al., 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 5, Definitions 1–2 on prefix non-malleability and the strong prefix property for sequenced parsers; Section 5.1 on plist[p] rejecting zero-byte steps and consuming all input without itself having the strong prefix property).
  - Lean Mathlib, repository leanprover-community/mathlib4, commit 5f78f9ce46fc85fa3cb45561d47b489c4c98cd04, Mathlib/InformationTheory/Coding/PrefixFree.lean and UniquelyDecodable.lean (IsPrefixFree, IsPrefixFree.eq_singleton_empty_of_empty_mem, IsPrefixFree.isUniquelyDecodable, IsPrefixFree.isUniquelyDecodable_of_nontrivial, IsUniquelyDecodable.epsilon_notMem).
  - Dimitrios Vytiniotis and Andrew J. Kennedy, 'Functional pearl: every bit counts', Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming (ICFP '10), pp. 15–26, 2010, DOI 10.1145/1863543.1863548 (Section 3, Coq-checked Lemma 1 for PrefixDecEnc, Corollary 1 for encoder injectivity, Corollary 2 for indexed PrefixFree, and Lemma 3 for PrefixEncDec); journal version: Andrew J. Kennedy and Dimitrios Vytiniotis, 'Every bit counts: The binary representation of typed data and programs', Journal of Functional Programming 22(4–5), pp. 529–573, 2012, DOI 10.1017/S0956796812000263.
- **Design question:** Under the sufficient framing condition PrefixDecEnc, when does uncounted concatenation of variable-length elements round-trip through repeated prefix decoding until end-of-input?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc`, `Toy.Codec.nonEmptyEnc_of_prefixDecEnc_of_ne` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc`: `Quot.sound`, `propext`; `nonEmptyEnc_of_prefixDecEnc_of_ne`: `propext`.
- **Basis: derived (modeling bridge)** — Uncounted repeat-until-EOF list formats (such as EverParse `plist[p]`) built from a strong-prefix element parser round-trip iff every element occupies at least one token; on any non-subsingleton element type this non-emptiness holds automatically, while zero-width elements (like `Unit`) break uncounted repetition and require an explicit length prefix or terminator. Because `encList` is not prefix-free on inhabited element types, the package's composition results cover such bare lists only when the list occupies the whole remaining input; a bare list followed by further data needs additional framing or a separate argument that the following tokens cannot be read as list elements (`bareList_first_field_lawful` is one such case).

##### Card 16 (`listCodec_encDec_of_prefixEncDec`): `Toy.Codec.listCodec_encDec_of_prefixEncDec`

- **Kind:** `theorem` | **Tier:** `T0` (re-derivation: list canonicality from element prefix canonicality (LowParse `parse_list_bare_injective`)) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `listCodec_encDec_of_prefixEncDec`: `Quot.sound`, `propext`
- **Plain claim:** For any framed codec fc : FramedCodec A β satisfying the converse prefix law PrefixEncDec fc, the concatenated whole-input list codec listCodec fc satisfies EncDec (requiring neither PrefixDecEnc nor NonEmptyEnc).
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.listCodec_encDec_of_prefixEncDec.{u, v} : ∀ {A : Type u} {β : Type v} (fc : Toy.Codec.FramedCodec A β),
    Toy.Codec.PrefixEncDec fc → Toy.Codec.EncDec (Toy.Codec.listCodec fc)
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:443-445
  theorem listCodec_encDec_of_prefixEncDec {A : Type u} {β : Type v}
      (fc : FramedCodec A β) (hped : PrefixEncDec fc) :
      EncDec (listCodec fc)
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem listCodec_encDec_of_prefixEncDec {A : Type u} {β : Type v}
      (fc : FramedCodec A β)
      (hped : ∀ (xs : List β) (a : A) (rest : List β),
        fc.decPrefix xs = some (a, rest) → xs = fc.enc a ++ rest) :
      ∀ (xs : List β) (as : List A), decList fc xs = some as → encList fc.enc as = xs
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `hped` | Guarantees every step accepted by fc.decPrefix decomposes the current stream as fc.enc a ++ rest, so re-encoding reconstructs xs. | `tight` | `Toy.Codec.ce_listCodec_encDec_drop_prefixEncDec` |

- **Non-vacuity witness:** `Toy.Codec.nv_listCodec_encDec` — varLenBoolFramedCodec : FramedCodec Bool Bool satisfies PrefixEncDec.
- **Non-claims:**
  - `listCodec fc` is a whole-input codec. Its encoder `encList fc.enc` is not prefix-free whenever `A` is inhabited (`encList_not_prefixFree`), so no framed codec with that encoder satisfies `PrefixDecEnc` (`no_prefixDecEnc_for_encList`). Consequently the package's sequencing theorem `seq_prefixDecEnc`, which assumes `PrefixDecEnc` for both fields, does not apply to a `FramedCodec.seq` record that has a list encoded this way as a field (for example as the first field, followed by further data), and `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` does not apply when the list elements are themselves such lists. The package therefore gives no general guarantee that such a layout decodes correctly, but this is not an impossibility result: in general such a layout needs extra framing (such as a length prefix or a terminator) or a separate argument that the following tokens cannot be read as list elements. `bareList_first_field_lawful` proves a lawful `seq` record whose first field is a bare `encList`-encoded list, with no length prefix or terminator, followed by a field whose codewords share no token with the element codewords. Nesting such lists directly inside another bare `encList`-encoded list does make the outer encoder non-injective (derived: for any `a : A`, `encList (encList enc)` maps both `[[a], [a]]` and `[[a, a]]` to `enc a ++ enc a`).
  - A framed codec satisfying `PrefixDecEnc` (even when `PrefixEncDec` also holds) does not become a lawful whole-input codec by discarding the remainder: `firstOnly fc` (`xs ↦ (fc.decPrefix xs).map Prod.fst`) satisfies `DecEnc`, yet whenever `A` and the token type `β` are inhabited it violates both `DecInj` and `EncDec` (proved in general as `firstOnly_decEnc_and_not_decInj`, and instantiated on `varLenBoolFramedCodec` in `framed_lawful_but_firstOnly_not_decInj`). Converting `decPrefix` into a lawful whole-input decoder requires checking `rest = []`.
  - Does not imply DecEnc (listCodec fc) without PrefixDecEnc and NonEmptyEnc, and avoids needing NonEmptyEnc only because decList explicitly rejects non-progressing steps (rest.length ≥ xs.length; exercised by ex_decList_guard_rejects in Examples.lean).
- **Prior art:**
  - EverParse / LowParse mechanization, repository project-everest/everparse, commit f3e4ce51d9b68593fd98472cadcdeb8b6abf388f, file lib/everparse/lowparse/LowParse.Spec.List.fsti (parse_list_aux with zero-progress rejection, serialize_list_precond requiring ParserStrong and parser_kind_low > 0, bare_serialize_list_correct, and parse_list_bare_injective).
  - Tahina Ramananandro et al., 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 5, Definitions 1–2 on prefix non-malleability and the strong prefix property for sequenced parsers; Section 5.1 on plist[p] rejecting zero-byte steps and consuming all input without itself having the strong prefix property).
- **Design question:** Does framed canonicality (PrefixEncDec) lift from a single element parser to whole-stream list decoding without assuming PrefixDecEnc or NonEmptyEnc?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.listCodec_encDec_of_prefixEncDec` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `listCodec_encDec_of_prefixEncDec`: `Quot.sound`, `propext`.
- **Basis: derived (modeling bridge)** — Repeat-until-EOF list decoding preserves canonicality (`EncDec`) from element-level `PrefixEncDec` alone—provided the decoder loop enforces strict progress on every step (`rest.length < xs.length`, matching LowParse `parse_list_aux` and exercised by `ex_decList_guard_rejects`).

##### Card 17 (`lawful_injective_nonEmpty_enc_admits_ambiguous_concat`): `Toy.Codec.lawful_injective_nonEmpty_enc_admits_ambiguous_concat`

- **Kind:** `counterexample` | **Tier:** `T1` (folklore concatenation-ambiguity instance mechanized against single-value `Lawful` and `NonEmptyEnc`) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `lawful_injective_nonEmpty_enc_admits_ambiguous_concat`: `propext`
- **Plain claim:** Single-value lawfulness with an injective, non-empty encoding admits ambiguous concatenation: ambiguousCodec : Codec Bool (List Bool) (false ↦ [false], true ↦ [false, false]) satisfies DecEnc, EncDec, Function.Injective enc, and NonEmptyEnc, yet violates PrefixFree and maps the distinct lists [false, false] and [true] to the same concatenation [false, false], ruling out any DecEnc list decoder.
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.lawful_injective_nonEmpty_enc_admits_ambiguous_concat : Toy.Codec.DecEnc Toy.Codec.ambiguousCodec ∧
    Toy.Codec.EncDec Toy.Codec.ambiguousCodec ∧
      Function.Injective Toy.Codec.ambiguousCodec.enc ∧
        Toy.Codec.NonEmptyEnc Toy.Codec.ambiguousCodec.enc ∧
          ¬Toy.Codec.PrefixFree Toy.Codec.ambiguousCodec.enc ∧
            ([false, false] ≠ [true] ∧
                Toy.Codec.encList Toy.Codec.ambiguousCodec.enc [false, false] =
                  Toy.Codec.encList Toy.Codec.ambiguousCodec.enc [true]) ∧
              ∀ (dec : List Bool → Option (List Bool)),
                ¬Toy.Codec.DecEnc
                    { enc := Toy.Codec.encList Toy.Codec.ambiguousCodec.enc, dec := dec }
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Counterexamples.lean:135-143
  theorem lawful_injective_nonEmpty_enc_admits_ambiguous_concat :
      DecEnc ambiguousCodec ∧
      EncDec ambiguousCodec ∧
      Function.Injective ambiguousCodec.enc ∧
      NonEmptyEnc ambiguousCodec.enc ∧
      ¬ PrefixFree ambiguousCodec.enc ∧
      (([false, false] : List Bool) ≠ [true] ∧
        encList ambiguousCodec.enc [false, false] = encList ambiguousCodec.enc [true]) ∧
      (∀ dec : List Bool → Option (List Bool), ¬ DecEnc ⟨encList ambiguousCodec.enc, dec⟩)
  ```
- **Hypothesis ledger:** None (unconditional statement).
- **Non-vacuity witness:** `Toy.Codec.lawful_injective_nonEmpty_enc_admits_ambiguous_concat` — ambiguousCodec : Codec Bool (List Bool) (false ↦ [false], true ↦ [false, false]).
- **Positive control:** `Toy.Codec.suffixEnc_not_prefixFree_yet_concat_lawful`
- **Non-claims:**
  - This is one instance, not a general implication: an injective encoding that is not prefix-free can still have injective concatenation (`false ↦ [false]`, `true ↦ [false, true]`).
  - Positive control suffixEnc_not_prefixFree_yet_concat_lawful (Counterexamples.lean) proves that suffixEnc (false ↦ [false], true ↦ [false, true]) violates PrefixFree yet has injective concatenation and a computable lawful (DecEnc ∧ EncDec) whole-list decoder decSuffixList.
  - Does not rule out length-prefixed or delimiter-framed list encodings over ambiguousCodec; ambiguity arises specifically from bare concatenation encList.
- **Prior art:**
  - Benjamin Delaware, Sorawit Suriyakarn, Clément Pit-Claudel, Qianchuan Ye, and Adam Chlipala, 'Narcissus: Correct-by-Construction Derivation of Decoders and Encoders from Binary Formats', Proceedings of the ACM on Programming Languages 3 (ICFP), Article 82, 2019, DOI 10.1145/3341686 (Section 3, format_suit example {(♣, 0b11), (♦, 0b0), (♥, 0b1), (♠, 0b10)} illustrating why sequencing a non-prefix-free format confuses (♣, ♦) with (♥, ♠)).
  - Dimitrios Vytiniotis and Andrew J. Kennedy, 'Functional pearl: every bit counts', Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming (ICFP '10), pp. 15–26, 2010, DOI 10.1145/1863543.1863548 (Section 3, Coq-checked Lemma 1 for PrefixDecEnc, Corollary 1 for encoder injectivity, Corollary 2 for indexed PrefixFree, and Lemma 3 for PrefixEncDec); journal version: Andrew J. Kennedy and Dimitrios Vytiniotis, 'Every bit counts: The binary representation of typed data and programs', Journal of Functional Programming 22(4–5), pp. 529–573, 2012, DOI 10.1017/S0956796812000263.
  - Tahina Ramananandro et al., 'EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats', 28th USENIX Security Symposium, 2019, pp. 1465–1482, https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud (Section 5, Definitions 1–2 on prefix non-malleability and the strong prefix property for sequenced parsers; Section 5.1 on plist[p] rejecting zero-byte steps and consuming all input without itself having the strong prefix property).
- **Design question:** Why are whole-input single-value codec laws (DecEnc ∧ EncDec) together with non-empty codewords insufficient to make bare list concatenation unambiguous?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.lawful_injective_nonEmpty_enc_admits_ambiguous_concat` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `lawful_injective_nonEmpty_enc_admits_ambiguous_concat`: `propext`.
- **Basis: derived (modeling bridge)** — Verifying single-message `DecEnc` and `EncDec` (even with non-empty encodings) does not make bare concatenation of messages unambiguous; designers concatenating variable-length fields must either use prefix-free framing (`PrefixDecEnc`), a uniquely decodable lookahead scheme (`suffixEnc`), or explicit length prefixes/delimiters.

#### Part E: Coproduct Complement Decompositions (`B ≃ A ⊕ C`)

##### Card 18 (`decomp_isEquiv_iff_lawful`): `Toy.Codec.decomp_isEquiv_iff_lawful`, `Toy.Codec.leftInv_decomp_iff_encDec`, `Toy.Codec.rightInv_decomp_iff_decEnc`

- **Kind:** `characterization` | **Tier:** `T1` (categorical coproduct-complement observation (Riley Prop. 4.2.2 proof) made precise as a constructive law-by-law equivalence) | **Depth:** `shallow`
- **Hashed companion theorem(s) (`lean_names`):** `Toy.Codec.nonCanonicalBoolCodec_not_encDec_yet_admits_equiv`
- **Verified axioms (`audit/axioms.json`):** `decomp_isEquiv_iff_lawful`: none (`[]`); `leftInv_decomp_iff_encDec`: none (`[]`); `rightInv_decomp_iff_decEnc`: none (`[]`); `nonCanonicalBoolCodec_not_encDec_yet_admits_equiv`: `propext`
- **Plain claim:** For any codec c : Codec A B, the specific canonical split maps decompToFun c : B → A ⊕ Junk c and decompInvFun c : A ⊕ Junk c → B satisfy LeftInv if and only if EncDec c holds (leftInv_decomp_iff_encDec), satisfy RightInv if and only if DecEnc c holds (rightInv_decomp_iff_decEnc), and therefore form mutual two-sided inverses (IsEquiv (decompToFun c) (decompInvFun c)) if and only if DecEnc c ∧ EncDec c holds (decomp_isEquiv_iff_lawful, without Classical.choice; by contrast, the bare existence of some non-canonical equivalence Equiv B (A ⊕ Junk c) does not make c lawful, as proved for nonCanonicalBoolCodec by nonCanonicalBoolCodec_not_encDec_yet_admits_equiv; axiom qualifiers established by the kernel axiom record: no axioms for decomp_isEquiv_iff_lawful, leftInv_decomp_iff_encDec, and rightInv_decomp_iff_decEnc, and [propext] without Classical.choice for nonCanonicalBoolCodec_not_encDec_yet_admits_equiv).
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.decomp_isEquiv_iff_lawful.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    Toy.Codec.IsEquiv (Toy.Codec.decompToFun c) (Toy.Codec.decompInvFun c) ↔
      Toy.Codec.DecEnc c ∧ Toy.Codec.EncDec c
  Toy.Codec.leftInv_decomp_iff_encDec.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    Toy.Codec.LeftInv (Toy.Codec.decompToFun c) (Toy.Codec.decompInvFun c) ↔ Toy.Codec.EncDec c
  Toy.Codec.rightInv_decomp_iff_decEnc.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
    Toy.Codec.RightInv (Toy.Codec.decompToFun c) (Toy.Codec.decompInvFun c) ↔ Toy.Codec.DecEnc c
  Toy.Codec.nonCanonicalBoolCodec_not_encDec_yet_admits_equiv : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
    ¬Toy.Codec.EncDec Toy.Codec.nonCanonicalBoolCodec ∧
      ¬Toy.Codec.IsEquiv (Toy.Codec.decompToFun Toy.Codec.nonCanonicalBoolCodec)
            (Toy.Codec.decompInvFun Toy.Codec.nonCanonicalBoolCodec) ∧
        Nonempty (Toy.Codec.Equiv Nat (Bool ⊕ Toy.Codec.Junk Toy.Codec.nonCanonicalBoolCodec))
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:486-487
  theorem decomp_isEquiv_iff_lawful {A : Type u} {B : Type v} (c : Codec A B) :
      IsEquiv (decompToFun c) (decompInvFun c) ↔ (DecEnc c ∧ EncDec c)

  -- lean/Toy/Codec/Statements.lean:453-454
  theorem leftInv_decomp_iff_encDec {A : Type u} {B : Type v} (c : Codec A B) :
      LeftInv (decompToFun c) (decompInvFun c) ↔ EncDec c

  -- lean/Toy/Codec/Statements.lean:467-468
  theorem rightInv_decomp_iff_decEnc {A : Type u} {B : Type v} (c : Codec A B) :
      RightInv (decompToFun c) (decompInvFun c) ↔ DecEnc c

  -- lean/Toy/Codec/Counterexamples.lean:1058-1062
  theorem nonCanonicalBoolCodec_not_encDec_yet_admits_equiv :
      DecEnc nonCanonicalBoolCodec ∧
      ¬ EncDec nonCanonicalBoolCodec ∧
      ¬ IsEquiv (decompToFun nonCanonicalBoolCodec) (decompInvFun nonCanonicalBoolCodec) ∧
      Nonempty (Equiv Nat (Bool ⊕ Junk nonCanonicalBoolCodec))
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem decomp_isEquiv_iff_lawful {A : Type u} {B : Type v} (c : Codec A B) :
      ((∀ b : B, decompInvFun c (decompToFun c b) = b) ∧
       (∀ x : A ⊕ { b : B // c.dec b = none }, decompToFun c (decompInvFun c x) = x)) ↔
      ((∀ a : A, c.dec (c.enc a) = some a) ∧
       (∀ (b : B) (a : A), c.dec b = some a → c.enc a = b))

  theorem leftInv_decomp_iff_encDec {A : Type u} {B : Type v} (c : Codec A B) :
      (∀ b : B, decompInvFun c (decompToFun c b) = b) ↔
      (∀ (b : B) (a : A), c.dec b = some a → c.enc a = b)

  theorem rightInv_decomp_iff_decEnc {A : Type u} {B : Type v} (c : Codec A B) :
      (∀ x : A ⊕ { b : B // c.dec b = none }, decompToFun c (decompInvFun c x) = x) ↔
      (∀ a : A, c.dec (c.enc a) = some a)

  theorem nonCanonicalBoolCodec_not_encDec_yet_admits_equiv :
      (∀ a : Bool, nonCanonicalBoolCodec.dec (nonCanonicalBoolCodec.enc a) = some a) ∧
      ¬ (∀ (b : Nat) (a : Bool),
          nonCanonicalBoolCodec.dec b = some a → nonCanonicalBoolCodec.enc a = b) ∧
      ¬ ((∀ b : Nat, decompInvFun nonCanonicalBoolCodec (decompToFun nonCanonicalBoolCodec b) = b) ∧
         (∀ x : Bool ⊕ { b : Nat // nonCanonicalBoolCodec.dec b = none },
           decompToFun nonCanonicalBoolCodec (decompInvFun nonCanonicalBoolCodec x) = x)) ∧
      Nonempty (Equiv Nat (Bool ⊕ { b : Nat // nonCanonicalBoolCodec.dec b = none }))
  ```
- **Hypothesis ledger:** None (unconditional statements).
- **Non-vacuity witness:** `Toy.Codec.nv_decomp_isEquiv_iff_lawful` — boolToNatCodec satisfies both sides of decomp_isEquiv_iff_lawful, while nonCanonicalBoolCodec fails LeftInv and EncDec (even though a non-canonical bijection Equiv Nat (Bool ⊕ Junk nonCanonicalBoolCodec) exists via nonCanonicalBoolJunkEquiv; see nonCanonicalBoolCodec_not_encDec_yet_admits_equiv) and alwaysFailUnitCodec fails RightInv and DecEnc (admitting no Equiv Unit (Unit ⊕ Junk alwaysFailUnitCodec); see ce_lawful_decomp_drop_decEnc, alongside malleableUnitBoolCodec in ce_lawful_decomp_drop_encDec, which fails LeftInv and EncDec and admits no Equiv Bool (Unit ⊕ Junk malleableUnitBoolCodec)).
- **Non-claims:**
  - Concerns only whether the canonical maps `decompToFun c` and `decompInvFun c` are mutual inverses: the bare existence of some equivalence `Equiv B (A ⊕ Junk c)` does not imply `EncDec c` or lawfulness. In particular, `nonCanonicalBoolCodec` violates `EncDec` (and its canonical maps fail `IsEquiv`), yet `nonCanonicalBoolJunkEquiv` constructs an explicit bijection `Equiv Nat (Bool ⊕ Junk nonCanonicalBoolCodec)` because `Junk nonCanonicalBoolCodec = { b : Nat // nonCanonicalBoolCodec.dec b = none }` (`b ≥ 3`) is countably infinite (`nonCanonicalBoolCodec_not_encDec_yet_admits_equiv`).
  - For a codec satisfying only one law the canonical maps are not mutually inverse: `LeftInv` holds exactly when `EncDec` does (`leftInv_decomp_iff_encDec`), `RightInv` exactly when `DecEnc` does (`rightInv_decomp_iff_decEnc`).
  - No statement about lenses is proved in this package. 'Dual to lenses' describes the shape of the result; the lens-side decomposition needs extra assumptions (for instance an inhabited view type).
  - Does not imply that Junk c is the unique type C with B ≃ A ⊕ C; any C related by an intertwining equivalence yields the same codec (codecOfSplit_eq_iff_exists_intertwining_equiv), while decompToFun c (c.enc a) = Sum.inl a follows directly from RightInv (decompToFun_enc_of_rightInv) and c.dec b = inlMatcher (decompToFun c b) holds unconditionally (dec_eq_inlMatcher_decompToFun).
- **Prior art:**
  - Mitchell Riley, 'Categories of Optics', arXiv:1809.00738v2 [math.CT], 2018 (Section 4.2 states concrete prism laws and observes in the proof of Proposition 4.2.2 that the first law makes Review injective so S ≅ C ⊔ A for some complement C in Set; Proposition 4.1.3, generalizing Johnson, Rosebrugh, and Wood, J.UCS 16(5):729–748, 2010, treats the lens-side complement under pullbacks and a global element of the view).
  - Matthew Pickering, Jeremy Gibbons, and Nicolas Wu, 'Profunctor Optics: Modular Data Accessors', The Art, Science, and Engineering of Programming, vol. 1, no. 2, article 7, 2017, DOI 10.22152/programming-journal.org/2017/1/7 (concrete prisms as match/build pairs formally dual to lenses, and profunctor composition; does not formalize prism laws).
  - Bryce Clarke, Derek Elkins, Jeremy Gibbons, Fosco Loregian, Bartosz Milewski, Emily Pillmore, and Mario Román, 'Profunctor Optics, a Categorical Update', Compositionality, vol. 6, article 1, 2024, DOI 10.32408/compositionality-6-1 (Section 3.1.6 defines prisms as mixed optics for the coproduct action; lawfulness is not treated there).
  - J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore, Benjamin C. Pierce, and Alan Schmitt, 'Combinators for bi-directional tree transformations: a linguistic approach to the view update problem', POPL '05, pp. 233–246, 2005, DOI 10.1145/1040305.1040325; journal version: 'Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem', ACM Transactions on Programming Languages and Systems 29(3), article 17, 2007, DOI 10.1145/1232420.1232424 (defines the GetPut, PutGet, and PutPut lens laws).
- **Design question:** How do the individual codec laws DecEnc and EncDec correspond to the two inverse laws of the canonical split maps decompToFun c : B → A ⊕ Junk c and decompInvFun c : A ⊕ Junk c → B?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.decomp_isEquiv_iff_lawful`, `Toy.Codec.leftInv_decomp_iff_encDec`, `Toy.Codec.rightInv_decomp_iff_decEnc`, `Toy.Codec.nonCanonicalBoolCodec_not_encDec_yet_admits_equiv` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `decomp_isEquiv_iff_lawful`: none (`[]`); `leftInv_decomp_iff_encDec`: none (`[]`); `rightInv_decomp_iff_decEnc`: none (`[]`); `nonCanonicalBoolCodec_not_encDec_yet_admits_equiv`: `propext`.
- **Basis: derived (modeling bridge)** — In monomorphic optics and serialization architecture, the two codec laws `DecEnc` and `EncDec` correspond one-to-one with the right- and left-inverse laws of the *canonical* split maps `(decompToFun c, decompInvFun c)` between `B` and `A ⊕ Junk c` (whereas non-canonical bijections `B ≃ A ⊕ Junk c` can exist even for malleable codecs on infinite wire types, as shown by `nonCanonicalBoolCodec_not_encDec_yet_admits_equiv`). This bridge applies only to monomorphic codecs; polymorphic prisms and constant-complement lenses are not modeled here.

##### Card 19 (`decomp_induces_lawful_and_complement`): `Toy.Codec.decomp_induces_lawful_and_complement`

- **Kind:** `theorem` | **Tier:** `T0` (re-derivation: a coproduct decomposition `B ≃ A ⊕ C` induces a lawful codec with `C ≃ Junk`) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `decomp_induces_lawful_and_complement`: none (`[]`)
- **Plain claim:** For any mutual inverses f : B → A ⊕ C and g : A ⊕ C → B (LeftInv f g and RightInv f g), the induced codec codecOfSplit f g satisfies DecEnc and EncDec, g ∘ Sum.inr maps C into Junk (codecOfSplit f g) as a two-sided inverse to junkToC f g, and f agrees with decompToFun (codecOfSplit f g) under this identification (without Classical.choice; established by the kernel axiom record: no axioms).
- **Lean statement(s) (`#check` output):**
  ```lean
  Toy.Codec.decomp_induces_lawful_and_complement.{u, v, w} : ∀ {A : Type u} {B : Type v} {C : Type w} (f : B → A ⊕ C) (g : A ⊕ C → B),
    Toy.Codec.LeftInv f g →
      Toy.Codec.RightInv f g →
        Toy.Codec.DecEnc (Toy.Codec.codecOfSplit f g) ∧
          Toy.Codec.EncDec (Toy.Codec.codecOfSplit f g) ∧
            (∀ (k : C), (Toy.Codec.codecOfSplit f g).dec (g (Sum.inr k)) = none) ∧
              (∀ (j : Toy.Codec.Junk (Toy.Codec.codecOfSplit f g)),
                  g (Sum.inr (Toy.Codec.junkToC f g j)) = j.val) ∧
                (∀ (k : C) (hj : (Toy.Codec.codecOfSplit f g).dec (g (Sum.inr k)) = none),
                    Toy.Codec.junkToC f g ⟨g (Sum.inr k), hj⟩ = k) ∧
                  ∀ (b : B),
                    Sum.map id Subtype.val
                        (Toy.Codec.decompToFun (Toy.Codec.codecOfSplit f g) b) =
                      Sum.map id (fun k => g (Sum.inr k)) (f b)
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:498-509
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
        Sum.map id (fun k => g (Sum.inr k)) (f b))
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem decomp_induces_lawful_and_complement
      {A : Type u} {B : Type v} {C : Type w}
      (f : B → A ⊕ C) (g : A ⊕ C → B)
      (hl : ∀ b : B, g (f b) = b)
      (hr : ∀ x : A ⊕ C, f (g x) = x) :
      (∀ a : A, inlMatcher (f (g (Sum.inl a))) = some a) ∧
      (∀ (b : B) (a : A), inlMatcher (f b) = some a → g (Sum.inl a) = b) ∧
      (∀ k : C, inlMatcher (f (g (Sum.inr k))) = none) ∧
      (∀ j : Junk (codecOfSplit f g), g (Sum.inr (junkToC f g j)) = j.1) ∧
      (∀ (k : C) (hj : (codecOfSplit f g).dec (g (Sum.inr k)) = none),
        junkToC f g ⟨g (Sum.inr k), hj⟩ = k) ∧
      (∀ b : B,
        Sum.map id Subtype.val (decompToFun (codecOfSplit f g) b) =
        Sum.map id (fun k => g (Sum.inr k)) (f b))
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `hl` | Establishes EncDec (codecOfSplit f g), the Junk → C → Junk round-trip, and agreement with decompToFun. | `tight` | `Toy.Codec.ce_decomp_induces_drop_leftInv` |
  | `hr` | Establishes DecEnc on Sum.inl and well-definedness plus the C → Junk → C round-trip on Sum.inr (see also ce_decomp_induces_drop_rightInv_inr). | `tight` | `Toy.Codec.ce_decomp_induces_drop_rightInv` |

- **Non-vacuity witness:** `Toy.Codec.nv_decomp_induces_lawful_and_complement` — natBoolSplitToFun and natBoolSplitInvFun witness Nat ≃ Bool ⊕ Nat matching boolToNatCodec.
- **Non-claims:**
  - No statement about lenses is proved in this package. 'Dual to lenses' describes the shape of the result; the lens-side decomposition needs extra assumptions (for instance an inhabited view type).
  - RightInv on Sum.inr is not required if one only wants DecEnc ∧ EncDec of codecOfSplit f g: LeftInv f g together with ∀ a, f (g (Sum.inl a)) = Sum.inl a already implies both DecEnc and EncDec for every f and g (codecOfSplit_lawful_of_leftInv_and_rightInv_inl), whereas RightInv on Sum.inr is specifically needed to identify C with Junk (codecOfSplit f g) (ce_decomp_induces_drop_rightInv_inr).
  - Distinct decompositions (C₁, f₁, g₁) and (C₂, f₂, g₂) need not produce distinct codecs (codecOfSplit_eq_iff_exists_intertwining_equiv).
- **Prior art:**
  - Mitchell Riley, 'Categories of Optics', arXiv:1809.00738v2 [math.CT], 2018 (Section 4.2 states concrete prism laws and observes in the proof of Proposition 4.2.2 that the first law makes Review injective so S ≅ C ⊔ A for some complement C in Set; Proposition 4.1.3, generalizing Johnson, Rosebrugh, and Wood, J.UCS 16(5):729–748, 2010, treats the lens-side complement under pullbacks and a global element of the view).
  - Matthew Pickering, Jeremy Gibbons, and Nicolas Wu, 'Profunctor Optics: Modular Data Accessors', The Art, Science, and Engineering of Programming, vol. 1, no. 2, article 7, 2017, DOI 10.22152/programming-journal.org/2017/1/7 (concrete prisms as match/build pairs formally dual to lenses, and profunctor composition; does not formalize prism laws).
  - Bryce Clarke, Derek Elkins, Jeremy Gibbons, Fosco Loregian, Bartosz Milewski, Emily Pillmore, and Mario Román, 'Profunctor Optics, a Categorical Update', Compositionality, vol. 6, article 1, 2024, DOI 10.32408/compositionality-6-1 (Section 3.1.6 defines prisms as mixed optics for the coproduct action; lawfulness is not treated there).
- **Design question:** Given an arbitrary coproduct decomposition B ≃ A ⊕ C, does it always induce a lawful codec A ⇄ B, and what does the residual type C represent?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.decomp_induces_lawful_and_complement` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `decomp_induces_lawful_and_complement`: none (`[]`).
- **Basis: derived (modeling bridge)** — Any explicit bijection splitting a wire representation `B` into a typed payload `A` and a residual error/other-variant type `C` (`B ≃ A ⊕ C`) automatically yields a lawful codec whose rejected inputs `Junk` are bijective with `C`, giving a clean specification pattern for codecs derived from sum-type representations.

##### Card 20 (`codecOfSplit_eq_iff_exists_intertwining_equiv`): `Toy.Codec.codecOfSplit_eq_iff_exists_intertwining_equiv`, `Toy.Codec.complementEquivOfCodecEq_intertwines`

- **Kind:** `characterization` | **Tier:** `T1` (concrete characterization of when two mutually inverse coproduct decompositions induce the same codec (not stated in Riley, Clarke et al., Isabelle AFP `Optics`, or Mathlib)) | **Depth:** `shallow`
- **Verified axioms (`audit/axioms.json`):** `codecOfSplit_eq_iff_exists_intertwining_equiv`: `Quot.sound`; `complementEquivOfCodecEq_intertwines`: none (`[]`); `complementEquivOfCodecEq`: none (`[]`)
- **Plain claim:** Given two mutually inverse coproduct decompositions (f₁, g₁) of B as A ⊕ C₁ and (f₂, g₂) of B as A ⊕ C₂, they induce the same codec (codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂) if and only if there exists an equivalence φ : Equiv C₁ C₂ intertwining them (∀ b, f₂ b = Sum.map id φ.toFun (f₁ b)); moreover, when the codecs are equal, complementEquivOfCodecEq constructs that Equiv C₁ C₂ in Type with zero axioms and complementEquivOfCodecEq_intertwines proves the intertwining equation (axiom qualifiers established by the kernel axiom record: [Quot.sound] for codecOfSplit_eq_iff_exists_intertwining_equiv, and no axioms for complementEquivOfCodecEq and complementEquivOfCodecEq_intertwines).
- **Lean statement(s) (`#check` output; `codecOfSplit_eq_iff_exists_intertwining_equiv` printed with `set_option pp.funBinderTypes true`):**
  ```lean
  Toy.Codec.codecOfSplit_eq_iff_exists_intertwining_equiv.{u, v, w₁, w₂} : ∀ {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂} (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B) (f₂ : B → A ⊕ C₂)
    (g₂ : A ⊕ C₂ → B),
    Toy.Codec.LeftInv f₁ g₁ →
      Toy.Codec.RightInv f₁ g₁ →
        Toy.Codec.LeftInv f₂ g₂ →
          Toy.Codec.RightInv f₂ g₂ →
            (Toy.Codec.codecOfSplit f₁ g₁ = Toy.Codec.codecOfSplit f₂ g₂ ↔
              ∃ (φ : Toy.Codec.Equiv C₁ C₂), ∀ (b : B), f₂ b = Sum.map id φ.toFun (f₁ b))
  Toy.Codec.complementEquivOfCodecEq_intertwines.{u, v, w₁, w₂} : ∀ {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂} (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B)
    (f₂ : B → A ⊕ C₂) (g₂ : A ⊕ C₂ → B) (hl₁ : Toy.Codec.LeftInv f₁ g₁)
    (hr₁ : Toy.Codec.RightInv f₁ g₁) (hl₂ : Toy.Codec.LeftInv f₂ g₂)
    (hr₂ : Toy.Codec.RightInv f₂ g₂)
    (heq : Toy.Codec.codecOfSplit f₁ g₁ = Toy.Codec.codecOfSplit f₂ g₂) (b : B),
    f₂ b =
      Sum.map id (Toy.Codec.complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq).toFun
        (f₁ b)
  ```
- **Lean source (verbatim from the cited lines; proof omitted):**
  ```lean
  -- lean/Toy/Codec/Statements.lean:582-589
  theorem codecOfSplit_eq_iff_exists_intertwining_equiv
      {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂}
      (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B)
      (f₂ : B → A ⊕ C₂) (g₂ : A ⊕ C₂ → B)
      (hl₁ : LeftInv f₁ g₁) (hr₁ : RightInv f₁ g₁)
      (hl₂ : LeftInv f₂ g₂) (hr₂ : RightInv f₂ g₂) :
      codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂ ↔
        ∃ (φ : Equiv C₁ C₂), ∀ b : B, f₂ b = Sum.map id φ.toFun (f₁ b)

  -- lean/Toy/Codec/Statements.lean:548-556
  theorem complementEquivOfCodecEq_intertwines
      {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂}
      (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B)
      (f₂ : B → A ⊕ C₂) (g₂ : A ⊕ C₂ → B)
      (hl₁ : LeftInv f₁ g₁) (hr₁ : RightInv f₁ g₁)
      (hl₂ : LeftInv f₂ g₂) (hr₂ : RightInv f₂ g₂)
      (heq : codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂) :
      ∀ b : B, f₂ b =
        Sum.map id (complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq).toFun (f₁ b)
  ```
- **Unfolded statement(s) (prose; definitionally equal to the Lean statements):**
  ```text
  theorem codecOfSplit_eq_iff_exists_intertwining_equiv
      {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂}
      (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B)
      (f₂ : B → A ⊕ C₂) (g₂ : A ⊕ C₂ → B)
      (hl₁ : ∀ b : B, g₁ (f₁ b) = b) (hr₁ : ∀ x : A ⊕ C₁, f₁ (g₁ x) = x)
      (hl₂ : ∀ b : B, g₂ (f₂ b) = b) (hr₂ : ∀ x : A ⊕ C₂, f₂ (g₂ x) = x) :
      (⟨fun a => g₁ (Sum.inl a), fun b => inlMatcher (f₁ b)⟩ : Codec A B) =
      ⟨fun a => g₂ (Sum.inl a), fun b => inlMatcher (f₂ b)⟩ ↔
        ∃ (φ : Equiv C₁ C₂), ∀ b : B, f₂ b = Sum.map id φ.toFun (f₁ b)

  theorem complementEquivOfCodecEq_intertwines
      {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂}
      (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B)
      (f₂ : B → A ⊕ C₂) (g₂ : A ⊕ C₂ → B)
      (hl₁ : ∀ b : B, g₁ (f₁ b) = b) (hr₁ : ∀ x : A ⊕ C₁, f₁ (g₁ x) = x)
      (hl₂ : ∀ b : B, g₂ (f₂ b) = b) (hr₂ : ∀ x : A ⊕ C₂, f₂ (g₂ x) = x)
      (heq : (⟨fun a => g₁ (Sum.inl a), fun b => inlMatcher (f₁ b)⟩ : Codec A B) =
             ⟨fun a => g₂ (Sum.inl a), fun b => inlMatcher (f₂ b)⟩) :
      ∀ b : B, f₂ b =
        Sum.map id (complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq).toFun (f₁ b)
  ```
- **Hypothesis ledger:**

  | Hypothesis | Purpose | Tightness | Counterexample |
  | :--- | :--- | :--- | :--- |
  | `hl₁ (in codecOfSplit_eq_iff_exists_intertwining_equiv)` | Ensures g₁ ∘ Sum.inr surjects onto Junk of the first split and recovers b from f₁ b = Sum.inr k₁. | `tight` | `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hl1` |
  | `hr₁ (in codecOfSplit_eq_iff_exists_intertwining_equiv)` | Ensures g₁ maps Sum.inl to valid values and Sum.inr into Junk of the first split. | `tight` | `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hr1` |
  | `hl₂ (in codecOfSplit_eq_iff_exists_intertwining_equiv)` | Ensures g₂ ∘ Sum.inr surjects onto Junk of the second split and aligns encoders under intertwining. | `tight` | `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hl2` |
  | `hr₂ (in codecOfSplit_eq_iff_exists_intertwining_equiv)` | Ensures g₂ maps Sum.inl to valid values and Sum.inr into Junk of the second split. | `tight` | `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hr2` |
  | `hl₁ (in complementEquivOfCodecEq_intertwines)` | Structurally required to form the conclusion's term complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq (so a literal drop-hl₁ instance of the conclusion cannot be typed); aligns g₁ (Sum.inr k) = b on the complement branch. Surrogate counterexample ce_codecOfSplit_eq_iff_drop_hl1 exports, for one concrete instance (B = Bool, C₁ = Unit, C₂ = Bool), exactly the three remaining laws hr₁, hl₂, hr₂ and the negation ¬ (codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂ ↔ ∃ φ : Equiv C₁ C₂, ∀ b, f₂ b = Sum.map id φ.toFun (f₁ b)) of the iff in codecOfSplit_eq_iff_exists_intertwining_equiv; it does not export heq or the emptiness of Equiv C₁ C₂ as separate conclusions (both are established only inside its proof). | `tight` (structural term dependency; surrogate counterexample) | `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hl1` |
  | `hr₁ (in complementEquivOfCodecEq_intertwines)` | Structurally required to form the conclusion's term complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq; ensures g₁ (Sum.inr k) lies in Junk of the first split. Surrogate counterexample ce_codecOfSplit_eq_iff_drop_hr1 exports, for one concrete instance (B = Unit, C₁ = Bool, C₂ = Empty), exactly the three remaining laws hl₁, hl₂, hr₂ and the negation ¬ (codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂ ↔ ∃ φ : Equiv C₁ C₂, ∀ b, f₂ b = Sum.map id φ.toFun (f₁ b)) of the iff in codecOfSplit_eq_iff_exists_intertwining_equiv; it does not export heq or the emptiness of Equiv C₁ C₂ as separate conclusions (both are established only inside its proof). | `tight` (structural term dependency; surrogate counterexample) | `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hr1` |
  | `hl₂ (in complementEquivOfCodecEq_intertwines)` | Structurally required to form the conclusion's term complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq (used in complementEquivOfCodecEq.left_inv). Surrogate counterexample ce_codecOfSplit_eq_iff_drop_hl2 exports, for one concrete instance (B = Bool, C₁ = Bool, C₂ = Unit), exactly the three remaining laws hl₁, hr₁, hr₂ and the negation ¬ (codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂ ↔ ∃ φ : Equiv C₁ C₂, ∀ b, f₂ b = Sum.map id φ.toFun (f₁ b)) of the iff in codecOfSplit_eq_iff_exists_intertwining_equiv; it does not export heq or the emptiness of Equiv C₁ C₂ as separate conclusions (both are established only inside its proof). | `tight` (structural term dependency; surrogate counterexample) | `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hl2` |
  | `hr₂ (in complementEquivOfCodecEq_intertwines)` | Structurally required to form the conclusion's term complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq (used in complementEquivOfCodecEq.right_inv). Surrogate counterexample ce_codecOfSplit_eq_iff_drop_hr2 exports, for one concrete instance (B = Unit, C₁ = Empty, C₂ = Bool), exactly the three remaining laws hl₁, hr₁, hl₂ and the negation ¬ (codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂ ↔ ∃ φ : Equiv C₁ C₂, ∀ b, f₂ b = Sum.map id φ.toFun (f₁ b)) of the iff in codecOfSplit_eq_iff_exists_intertwining_equiv; it does not export heq or the emptiness of Equiv C₁ C₂ as separate conclusions (both are established only inside its proof). | `tight` (structural term dependency; surrogate counterexample) | `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hr2` |
  | `heq (in complementEquivOfCodecEq_intertwines)` | Structurally required to form the conclusion's term complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq (so a literal drop-heq instance of the conclusion cannot be typed); supplies equality of the two induced codecs so C₁ elements map into Junk of the second split. Surrogate counterexample ce_intertwines_drop_heq shows that when all four inverse hypotheses hold and the induced codecs differ, no candidate function φ : C₁ → C₂ at all intertwines f₁ and f₂ (it exports the four laws and the non-existence of φ; the inequality of the two induced codecs for the same instance is exported by same_complement_different_codec). | `tight` (structural term dependency; surrogate counterexample) | `Toy.Codec.ce_intertwines_drop_heq` |

- **Non-vacuity witness:** `Toy.Codec.nv_codecOfSplit_eq_iff_exists_intertwining_equiv` — Positive pair: (natBoolSplitToFun, natBoolSplitInvFun) on Nat ≃ Bool ⊕ Nat and (natBoolSubSplitToFun, natBoolSubSplitInvFun) on Nat ≃ Bool ⊕ { n // 2 ≤ n } satisfy all four inverse laws, induce equal codecs, and are intertwined by natBoolSubEquiv; negative pair: (splitBoolFalseToFun, splitBoolFalseInvFun) and (splitBoolTrueToFun, splitBoolTrueInvFun) on Bool ≃ Unit ⊕ Unit satisfy all four inverse laws, induce unequal codecs, and admit no intertwining equivalence.
- **Non-claims:**
  - Does not say that two decompositions induce the same codec whenever their complement types are equivalent. The equivalence must intertwine the decompositions: two decompositions of `Bool` as `Unit ⊕ Unit`, one with `enc () = false` and one with `enc () = true`, have the same complement and different codecs.
  - No statement about lenses is proved in this package. 'Dual to lenses' describes the shape of the result; the lens-side decomposition needs extra assumptions (for instance an inhabited view type).
  - In the reverse direction (intertwining ⇒ equal codecs), bijectivity of φ and hypotheses hl₁ and hr₂ are not needed: any intertwining function φ : C₁ → C₂ with hr₁ and hl₂ suffices (proved in Witnesses.lean as codecOfSplit_eq_of_intertwining_fun).
- **Prior art:**
  - Mitchell Riley, 'Categories of Optics', arXiv:1809.00738v2 [math.CT], 2018 (Section 4.2 states concrete prism laws and observes in the proof of Proposition 4.2.2 that the first law makes Review injective so S ≅ C ⊔ A for some complement C in Set; Proposition 4.1.3, generalizing Johnson, Rosebrugh, and Wood, J.UCS 16(5):729–748, 2010, treats the lens-side complement under pullbacks and a global element of the view). Note: Riley's coend relation (Section 3, Definition 4.2.1) is generated by arbitrary residual maps rather than isomorphisms of mutually inverse decompositions; this intertwining-equivalence statement for two-sided decompositions was not found in Riley, Clarke et al., Isabelle AFP Optics, or Mathlib.
  - Bryce Clarke, Derek Elkins, Jeremy Gibbons, Fosco Loregian, Bartosz Milewski, Emily Pillmore, and Mario Román, 'Profunctor Optics, a Categorical Update', Compositionality, vol. 6, article 1, 2024, DOI 10.32408/compositionality-6-1 (Section 3.1.6 defines prisms as mixed optics for the coproduct action; lawfulness is not treated there).
  - J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore, Benjamin C. Pierce, and Alan Schmitt, 'Combinators for bi-directional tree transformations: a linguistic approach to the view update problem', POPL '05, pp. 233–246, 2005, DOI 10.1145/1040305.1040325; journal version: 'Combinators for bidirectional tree transformations: A linguistic approach to the view-update problem', ACM Transactions on Programming Languages and Systems 29(3), article 17, 2007, DOI 10.1145/1232420.1232424 (defines the GetPut, PutGet, and PutPut lens laws).
- **Design question:** When do two mutually inverse coproduct decompositions B ≃ A ⊕ C₁ and B ≃ A ⊕ C₂ induce the exact same lawful codec A ⇄ B, and how can the complement equivalence C₁ ≃ C₂ be extracted as explicit data?
- **Basis: execution (Lean kernel check)** — `Toy.Codec.codecOfSplit_eq_iff_exists_intertwining_equiv`, `Toy.Codec.complementEquivOfCodecEq_intertwines` (plus all linked witness and counterexample theorems) elaborated and checked by Lean `v4.34.1` with verified axioms `codecOfSplit_eq_iff_exists_intertwining_equiv`: `Quot.sound`; `complementEquivOfCodecEq_intertwines`: none (`[]`); `complementEquivOfCodecEq`: none (`[]`).
- **Basis: derived (modeling bridge)** — Two different residual/error representations `C₁` and `C₂` in decompositions `B ≃ A ⊕ C₁` and `B ≃ A ⊕ C₂` specify the exact same codec iff their residuals are related by a bijection `C₁ ≃ C₂` that commutes with the two splits (`f₂ = Sum.map id φ.toFun ∘ f₁`). Merely having isomorphic (or even identical) residual types does not imply equal codecs (`same_complement_different_codec`).

### Witness Definitions and Supporting / Counterexample Declarations

To keep this report self-contained without requiring external source lookup, every concrete witness codec, helper map, fiber split, and equivalence defined outside `Defs.lean` is reproduced verbatim below, followed by the kernel-elaborated `#check` signatures of all supporting lemmas, positive controls, definition examples, tightness counterexamples, and non-vacuity witnesses.

#### Witness codecs, fiber splits, and decomposition maps (`Examples.lean`, `Counterexamples.lean`, `Witnesses.lean`)

```lean
namespace Toy.Codec

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

/-- Positive example of `Equiv`: Boolean negation `Bool ≃ Bool`. -/
def boolNotEquiv : Equiv Bool Bool where
  toFun b := !b
  invFun b := !b
  left_inv := ex_leftInv_pos
  right_inv := ex_rightInv_pos

/-- Computable `FiberSplit` for `boolToNatCodec.enc`. -/
def boolToNatFiberSplit : FiberSplit boolToNatCodec.enc
  | 0 => PSum.inl ⟨false, rfl⟩
  | 1 => PSum.inl ⟨true, rfl⟩
  | _ + 2 => PSum.inr (fun a h => by cases a <;> cases h)

/-- A `FiberSplit` for the non-injective function `fun _ : Bool => ()`. -/
def constUnitFiberSplit : FiberSplit (fun _ : Bool => ())
  | () => PSum.inl ⟨false, rfl⟩

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

/-- Split maps `Unit ↔ Empty ⊕ Bool` satisfying `LeftInv` and `RightInv` on `Sum.inl`,
    but failing `RightInv` on `Sum.inr true`. -/
def collidingJunkToFun : Unit → Empty ⊕ Bool := fun _ => Sum.inr false

def collidingJunkInvFun : Empty ⊕ Bool → Unit
  | Sum.inl e => Empty.elim e
  | Sum.inr _ => ()

/-- Boolean negation codec `Bool → Bool` (lawful, with encoder distinct from `id`). -/
def boolNotCodec : Codec Bool Bool where
  enc b := !b
  dec b := some (!b)

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

/-- A framed codec that violates `PrefixDecEnc` on arbitrary remainders, yet whose
    induced `listCodec` satisfies `DecEnc` (`PrefixDecEnc` is sufficient, not necessary). -/
def lenientFc : FramedCodec Unit Bool where
  enc _ := [true]
  decPrefix
    | true :: rest => if rest.all id = true then some ((), rest) else none
    | _ => none

/-- Whole-input codec obtained by discarding the unconsumed remainder of `fc.decPrefix`. -/
def firstOnly {A : Type u} {β : Type v} (fc : FramedCodec A β) : Codec A (List β) where
  enc := fc.enc
  dec xs := (fc.decPrefix xs).map Prod.fst

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

/-- Computable `FiberSplit` for the identity map on `Bool`. -/
def idBoolFiberSplit : FiberSplit (fun b : Bool => b) := fun b => PSum.inl ⟨b, rfl⟩

/-- Computable `FiberSplit` for `nonCanonicalBoolCodec.enc` (which equals `boolToNatCodec.enc`). -/
def nonCanonicalBoolFiberSplit : FiberSplit nonCanonicalBoolCodec.enc
  | 0 => PSum.inl ⟨false, rfl⟩
  | 1 => PSum.inl ⟨true, rfl⟩
  | _ + 2 => PSum.inr (fun a h => by cases a <;> cases h)

/-- Split maps satisfying `RightInv` but failing `LeftInv` (`Bool` ↔ `Unit ⊕ Empty`). -/
def badLeftSplitToFun : Bool → Unit ⊕ Empty := fun _ => Sum.inl ()

def badLeftSplitInvFun : Unit ⊕ Empty → Bool
  | Sum.inl () => false
  | Sum.inr e => Empty.elim e

/-- Split maps satisfying `LeftInv` but failing `RightInv` on `Sum.inl` (`Unit` ↔ `Unit ⊕ Unit`). -/
def badRightInlSplitToFun : Unit → Unit ⊕ Unit := fun _ => Sum.inr ()

def badRightInlSplitInvFun : Unit ⊕ Unit → Unit := fun _ => ()

/-- Split maps satisfying `LeftInv` and `RightInv` on `Sum.inl`, but failing `RightInv` on `Sum.inr`:
    shows `RightInv` on `Sum.inr` is specifically needed for the complement characterization. -/
def badRightInrSplitToFun : Unit → Unit ⊕ Bool := fun _ => Sum.inl ()

def badRightInrSplitInvFun : Unit ⊕ Bool → Unit := fun _ => ()

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

/-- Always-failing framed codec on `Bool` with empty codewords `enc _ = []`:
    has two distinct source values (`false ≠ true`) and satisfies `PrefixEncDec`,
    yet violates `PrefixDecEnc` and `NonEmptyEnc`. -/
def emptyBoolFailFramedCodec : FramedCodec Bool Bool where
  enc _ := []
  decPrefix _ := none

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

open Classical in
/-- Classical fiber split of an arbitrary function, built with `Classical.choice`. -/
noncomputable def classicalFiberSplit {A : Type u} {B : Type v} (f : A → B) : FiberSplit f :=
  fun b => if h : ∃ a, f a = b then PSum.inl ⟨Classical.choose h, Classical.choose_spec h⟩
    else PSum.inr (fun a ha => h ⟨a, ha⟩)

end Toy.Codec
```

#### Supporting lemma and boundary-witness signatures (`Witnesses.lean` and `Counterexamples.lean`)

Printed with `set_option pp.funBinderTypes true` (see **How to read this section**): `const_imagePrefixFree_not_prefixFree`, `same_complement_different_codec`.

```lean
Toy.Codec.classicalCodec_enc.{u, v} : ∀ {A : Type u} {B : Type v} (f : A → B), (Toy.Codec.classicalCodec f).enc = f
Toy.Codec.codecOfFiberSplit_encDec.{u, v} : ∀ {A : Type u} {B : Type v} (f : A → B) (s : Toy.Codec.FiberSplit f),
  Toy.Codec.EncDec (Toy.Codec.codecOfFiberSplit f s)
Toy.Codec.canonicalize_encDec.{u, v} : ∀ {A : Type u} {B : Type v} [inst : DecidableEq B] (c : Toy.Codec.Codec A B),
  Toy.Codec.EncDec (Toy.Codec.canonicalize c)
Toy.Codec.encDec_imp_decInj.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B), Toy.Codec.EncDec c → Toy.Codec.DecInj c
Toy.Codec.lawful_iff_decEnc_and_accepts_only_range.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
  Toy.Codec.DecEnc c ∧ Toy.Codec.EncDec c ↔
    Toy.Codec.DecEnc c ∧ ∀ (b : B), (c.dec b).isSome = true → ∃ a, c.enc a = b
Toy.Codec.enc_unique_of_dec_eq.{u, v} : ∀ {A : Type u} {B : Type v} (c₁ c₂ : Toy.Codec.Codec A B),
  c₁.dec = c₂.dec → Toy.Codec.DecEnc c₁ → Toy.Codec.EncDec c₂ → c₁.enc = c₂.enc
Toy.Codec.isSome_imp_mem_range_of_encDec.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
  Toy.Codec.EncDec c → ∀ (b : B), (c.dec b).isSome = true → ∃ a, c.enc a = b
Toy.Codec.mem_range_imp_isSome_of_decEnc.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
  Toy.Codec.DecEnc c → ∀ (b : B), (∃ a, c.enc a = b) → (c.dec b).isSome = true
Toy.Codec.eq_none_iff_of_isSome_iff.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B) (b : B),
  ((c.dec b).isSome = true ↔ ∃ a, c.enc a = b) → (c.dec b = none ↔ ∀ (a : A), c.enc a ≠ b)
Toy.Codec.prefixFree_iff_injective_and_imagePrefixFree.{u, v} : ∀ {A : Type u} {β : Type v} (enc : A → List β),
  Toy.Codec.PrefixFree enc ↔ Function.Injective enc ∧ Toy.Codec.ImagePrefixFree enc
Toy.Codec.prefixDecEnc_nil_codeword_imp_subsingleton.{u, v} : ∀ {A : Type u} {β : Type v} (fc : Toy.Codec.FramedCodec A β),
  Toy.Codec.PrefixDecEnc fc → ∀ (a₀ : A), fc.enc a₀ = [] → ∀ (a : A), a = a₀
Toy.Codec.prefixFree_nil_codeword_imp_subsingleton.{u, v} : ∀ {A : Type u} {β : Type v} (enc : A → List β),
  Toy.Codec.PrefixFree enc → ∀ (a₀ : A), enc a₀ = [] → ∀ (a : A), a = a₀
Toy.Codec.nonEmptyEnc_of_prefixDecEnc_of_ne.{u, v} : ∀ {A : Type u} {β : Type v} (fc : Toy.Codec.FramedCodec A β),
  Toy.Codec.PrefixDecEnc fc → ∀ {x y : A}, x ≠ y → Toy.Codec.NonEmptyEnc fc.enc
Toy.Codec.nonEmptyEnc_of_listCodec_decEnc.{u, v} : ∀ {A : Type u} {β : Type v} (fc : Toy.Codec.FramedCodec A β),
  Toy.Codec.DecEnc (Toy.Codec.listCodec fc) → Toy.Codec.NonEmptyEnc fc.enc
Toy.Codec.dec_eq_inlMatcher_decompToFun.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B) (b : B),
  c.dec b = Toy.Codec.inlMatcher (Toy.Codec.decompToFun c b)
Toy.Codec.codecOfSplit_decomp_eq.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
  Toy.Codec.codecOfSplit (Toy.Codec.decompToFun c) (Toy.Codec.decompInvFun c) = c
Toy.Codec.decompToFun_enc_of_rightInv.{u, v} : ∀ {A : Type u} {B : Type v} (c : Toy.Codec.Codec A B),
  Toy.Codec.RightInv (Toy.Codec.decompToFun c) (Toy.Codec.decompInvFun c) →
    ∀ (a : A), Toy.Codec.decompToFun c (c.enc a) = Sum.inl a
Toy.Codec.codecOfSplit_eq_of_intertwining_fun.{u, v, w₁, w₂} : ∀ {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂} (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B)
  (f₂ : B → A ⊕ C₂) (g₂ : A ⊕ C₂ → B),
  Toy.Codec.RightInv f₁ g₁ →
    Toy.Codec.LeftInv f₂ g₂ →
      ∀ (φ : C₁ → C₂),
        (∀ (b : B), f₂ b = Sum.map id φ (f₁ b)) →
          Toy.Codec.codecOfSplit f₁ g₁ = Toy.Codec.codecOfSplit f₂ g₂
Toy.Codec.boolToNat_enc_injective : Function.Injective Toy.Codec.boolToNatCodec.enc
Toy.Codec.codecOfSplit_lawful_of_leftInv_and_rightInv_inl.{u, v, w} : ∀ {A : Type u} {B : Type v} {C : Type w} (f : B → A ⊕ C) (g : A ⊕ C → B),
  Toy.Codec.LeftInv f g →
    (∀ (a : A), f (g (Sum.inl a)) = Sum.inl a) →
      Toy.Codec.DecEnc (Toy.Codec.codecOfSplit f g) ∧ Toy.Codec.EncDec (Toy.Codec.codecOfSplit f g)
Toy.Codec.untaggedSum_decEnc_imp_disjoint_images.{u₁, u₂, v} : ∀ {A₁ : Type u₁} {A₂ : Type u₂} {B : Type v} (enc₁ : A₁ → B) (enc₂ : A₂ → B)
  (dec : B → Option (A₁ ⊕ A₂)),
  Toy.Codec.DecEnc
      {
        enc := fun s =>
          match s with
          | Sum.inl a₁ => enc₁ a₁
          | Sum.inr a₂ => enc₂ a₂,
        dec := dec } →
    ∀ (a₁ : A₁) (a₂ : A₂), enc₁ a₁ ≠ enc₂ a₂
Toy.Codec.untaggedSum_lawful_iff_disjoint_images.{u₁, u₂, v} : ∀ {A₁ : Type u₁} {A₂ : Type u₂} {B : Type v} (c₁ : Toy.Codec.Codec A₁ B)
  (c₂ : Toy.Codec.Codec A₂ B),
  Toy.Codec.DecEnc c₁ →
    Toy.Codec.EncDec c₁ →
      Toy.Codec.DecEnc c₂ →
        Toy.Codec.EncDec c₂ →
          (Toy.Codec.Lawful (Toy.Codec.untaggedSum c₁ c₂) ↔
            ∀ (a₁ : A₁) (a₂ : A₂), c₁.enc a₁ ≠ c₂.enc a₂)
Toy.Codec.boolNotCodec_decEnc : Toy.Codec.DecEnc Toy.Codec.boolNotCodec
Toy.Codec.boolNotCodec_encDec : Toy.Codec.EncDec Toy.Codec.boolNotCodec
Toy.Codec.nonCanonicalBoolCodec_decEnc : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec
Toy.Codec.alwaysFailBoolCodec_encDec : Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec
Toy.Codec.alwaysFailConstCodec_encDec : Toy.Codec.EncDec Toy.Codec.alwaysFailConstCodec
Toy.Codec.shiftedBoolCodec_decInj : Toy.Codec.DecInj Toy.Codec.shiftedBoolCodec
Toy.Codec.malleableUnitBoolCodec_decEnc : Toy.Codec.DecEnc Toy.Codec.malleableUnitBoolCodec
Toy.Codec.alwaysFailUnitCodec_encDec : Toy.Codec.EncDec Toy.Codec.alwaysFailUnitCodec
Toy.Codec.ambiguousCodec_decEnc : Toy.Codec.DecEnc Toy.Codec.ambiguousCodec
Toy.Codec.ambiguousCodec_encDec : Toy.Codec.EncDec Toy.Codec.ambiguousCodec
Toy.Codec.ambiguousEnc_injective : Function.Injective Toy.Codec.ambiguousEnc
Toy.Codec.ambiguousEnc_nonEmpty : Toy.Codec.NonEmptyEnc Toy.Codec.ambiguousEnc
Toy.Codec.alwaysFailFramedCodec_prefixEncDec : Toy.Codec.PrefixEncDec Toy.Codec.alwaysFailFramedCodec
Toy.Codec.alwaysFailFramedCodec_nonEmptyEnc : Toy.Codec.NonEmptyEnc Toy.Codec.alwaysFailFramedCodec.enc
Toy.Codec.malleableFramedCodec_prefixDecEnc : Toy.Codec.PrefixDecEnc Toy.Codec.malleableFramedCodec
Toy.Codec.malleableFramedCodec_nonEmptyEnc : Toy.Codec.NonEmptyEnc Toy.Codec.malleableFramedCodec.enc
Toy.Codec.emptyUnitFramedCodec_prefixDecEnc : Toy.Codec.PrefixDecEnc Toy.Codec.emptyUnitFramedCodec
Toy.Codec.emptyUnitFramedCodec_prefixEncDec : Toy.Codec.PrefixEncDec Toy.Codec.emptyUnitFramedCodec
Toy.Codec.emptyUnitFramedCodec_prefixFree : Toy.Codec.PrefixFree Toy.Codec.emptyUnitFramedCodec.enc
Toy.Codec.ambiguousFailFramedCodec_prefixEncDec : Toy.Codec.PrefixEncDec Toy.Codec.ambiguousFailFramedCodec
Toy.Codec.suffixEnc_not_prefixFree_yet_concat_lawful : Function.Injective Toy.Codec.suffixEnc ∧
  Toy.Codec.NonEmptyEnc Toy.Codec.suffixEnc ∧
    ¬Toy.Codec.PrefixFree Toy.Codec.suffixEnc ∧
      Function.Injective (Toy.Codec.encList Toy.Codec.suffixEnc) ∧
        Toy.Codec.DecEnc
            { enc := Toy.Codec.encList Toy.Codec.suffixEnc, dec := Toy.Codec.decSuffixList } ∧
          Toy.Codec.EncDec
            { enc := Toy.Codec.encList Toy.Codec.suffixEnc, dec := Toy.Codec.decSuffixList }
Toy.Codec.decInj_and_surjective_dec_not_lawful : Toy.Codec.DecInj Toy.Codec.shiftedBoolCodec ∧
  (∀ (a : Bool), ∃ b, Toy.Codec.shiftedBoolCodec.dec b = some a) ∧
    ¬Toy.Codec.DecEnc Toy.Codec.shiftedBoolCodec ∧ ¬Toy.Codec.EncDec Toy.Codec.shiftedBoolCodec
Toy.Codec.const_imagePrefixFree_not_prefixFree : (Toy.Codec.ImagePrefixFree fun (x : Bool) => [true]) ∧ ¬Toy.Codec.PrefixFree fun (x : Bool) => [true]
Toy.Codec.lenient_not_prefixDecEnc_yet_listCodec_decEnc : ¬Toy.Codec.PrefixDecEnc Toy.Codec.lenientFc ∧
  Toy.Codec.NonEmptyEnc Toy.Codec.lenientFc.enc ∧
    Toy.Codec.DecEnc (Toy.Codec.listCodec Toy.Codec.lenientFc)
Toy.Codec.encList_not_prefixFree.{u, v} : ∀ {A : Type u} {β : Type v} (enc : A → List β) (a : A),
  ¬Toy.Codec.PrefixFree (Toy.Codec.encList enc)
Toy.Codec.no_prefixDecEnc_for_encList.{u, v} : ∀ {A : Type u} {β : Type v} (enc : A → List β) (a : A) (decP : List β → Option (List A × List β)),
  ¬Toy.Codec.PrefixDecEnc { enc := Toy.Codec.encList enc, decPrefix := decP }
Toy.Codec.framed_lawful_but_firstOnly_not_decInj : Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec ∧
  Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec ∧
    Toy.Codec.DecEnc (Toy.Codec.firstOnly Toy.Codec.varLenBoolFramedCodec) ∧
      ¬Toy.Codec.DecInj (Toy.Codec.firstOnly Toy.Codec.varLenBoolFramedCodec)
Toy.Codec.same_complement_different_codec : Toy.Codec.LeftInv Toy.Codec.splitBoolFalseToFun Toy.Codec.splitBoolFalseInvFun ∧
  Toy.Codec.RightInv Toy.Codec.splitBoolFalseToFun Toy.Codec.splitBoolFalseInvFun ∧
    Toy.Codec.LeftInv Toy.Codec.splitBoolTrueToFun Toy.Codec.splitBoolTrueInvFun ∧
      Toy.Codec.RightInv Toy.Codec.splitBoolTrueToFun Toy.Codec.splitBoolTrueInvFun ∧
        Nonempty (Toy.Codec.Equiv Unit Unit) ∧
          Toy.Codec.codecOfSplit Toy.Codec.splitBoolFalseToFun Toy.Codec.splitBoolFalseInvFun ≠
              Toy.Codec.codecOfSplit Toy.Codec.splitBoolTrueToFun Toy.Codec.splitBoolTrueInvFun ∧
            ¬∃ (φ : Toy.Codec.Equiv Unit Unit),
                ∀ (b : Bool), Toy.Codec.splitBoolTrueToFun b = Sum.map id φ.toFun (Toy.Codec.splitBoolFalseToFun b)
Toy.Codec.badLeftSplit_rightInv : Toy.Codec.RightInv Toy.Codec.badLeftSplitToFun Toy.Codec.badLeftSplitInvFun
Toy.Codec.badRightInlSplit_leftInv : Toy.Codec.LeftInv Toy.Codec.badRightInlSplitToFun Toy.Codec.badRightInlSplitInvFun
Toy.Codec.emptyBoolSplit_leftInv : Toy.Codec.LeftInv Toy.Codec.emptyBoolSplitToFun Toy.Codec.emptyBoolSplitInvFun
Toy.Codec.emptyBoolSplit_rightInv : Toy.Codec.RightInv Toy.Codec.emptyBoolSplitToFun Toy.Codec.emptyBoolSplitInvFun
Toy.Codec.badEmptyUnitSplit_rightInv : Toy.Codec.RightInv Toy.Codec.badEmptyUnitSplitToFun Toy.Codec.badEmptyUnitSplitInvFun
Toy.Codec.unitEmptySplit_leftInv : Toy.Codec.LeftInv Toy.Codec.unitEmptySplitToFun Toy.Codec.unitEmptySplitInvFun
Toy.Codec.unitEmptySplit_rightInv : Toy.Codec.RightInv Toy.Codec.unitEmptySplitToFun Toy.Codec.unitEmptySplitInvFun
Toy.Codec.nonCanonicalBoolCodec_not_encDec_yet_admits_equiv : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
  ¬Toy.Codec.EncDec Toy.Codec.nonCanonicalBoolCodec ∧
    ¬Toy.Codec.IsEquiv (Toy.Codec.decompToFun Toy.Codec.nonCanonicalBoolCodec)
          (Toy.Codec.decompInvFun Toy.Codec.nonCanonicalBoolCodec) ∧
      Nonempty (Toy.Codec.Equiv Nat (Bool ⊕ Toy.Codec.Junk Toy.Codec.nonCanonicalBoolCodec))
Toy.Codec.firstOnly_decEnc_and_not_decInj.{u, v} : ∀ {A : Type u} {β : Type v} (fc : Toy.Codec.FramedCodec A β),
  Toy.Codec.PrefixDecEnc fc →
    ∀ (a : A) (t : β),
      Toy.Codec.DecEnc (Toy.Codec.firstOnly fc) ∧
        ¬Toy.Codec.DecInj (Toy.Codec.firstOnly fc) ∧ ¬Toy.Codec.EncDec (Toy.Codec.firstOnly fc)
Toy.Codec.bareListGreedy_encList : ∀ (xs : List Bool) (n : Nat) (rest : List Nat),
  Toy.Codec.bareListGreedy (Toy.Codec.encList Toy.Codec.bareListElemEnc xs ++ (n + 2) :: rest) = (xs, (n + 2) :: rest)
Toy.Codec.bareListGreedy_sound : ∀ (ys : List Nat),
  ys =
    Toy.Codec.encList Toy.Codec.bareListElemEnc (Toy.Codec.bareListGreedy ys).fst ++ (Toy.Codec.bareListGreedy ys).snd
Toy.Codec.bareListSeq_decPrefix_eq : ∀ (ys : List Nat),
  (Toy.Codec.bareListFc.seq Toy.Codec.natFieldFc).decPrefix ys =
    Option.map (fun p => (((Toy.Codec.bareListGreedy ys).fst, p.fst), p.snd))
      (Toy.Codec.natFieldFc.decPrefix (Toy.Codec.bareListGreedy ys).snd)
Toy.Codec.bareList_first_field_lawful : ¬Toy.Codec.PrefixDecEnc Toy.Codec.bareListFc ∧
  Toy.Codec.PrefixDecEnc (Toy.Codec.bareListFc.seq Toy.Codec.natFieldFc) ∧
    Toy.Codec.PrefixEncDec (Toy.Codec.bareListFc.seq Toy.Codec.natFieldFc)
Toy.Codec.fiberSplit_exists_for_every_function.{u, v} : ∀ {A : Type u} {B : Type v} (f : A → B),
  Nonempty (Toy.Codec.FiberSplit f)
```

#### Definition example signatures (`Examples.lean` and `Counterexamples.lean`)

Printed with an added option (see **How to read this section**): `pp.funBinderTypes true` for `ex_classicalCodec_neg`, `ex_codecOfSplit_neg` and `ex_complementEquivOfCodecEq_neg`; `pp.proofs true` for `ex_fiberSplitOfLawful_pos`, `ex_junkToC_pos`, `ex_junkToC_neg_nonRightInv` and `ex_complementEquivOfCodecEq_pos`; `pp.analyze true` for `ex_inlMatcher_pos` and `ex_inlMatcher_neg`.

```lean
Toy.Codec.ex_leftInv_pos : Toy.Codec.LeftInv (fun b => !b) fun b => !b
Toy.Codec.ex_leftInv_neg : ¬Toy.Codec.LeftInv (fun x => ()) fun x => false
Toy.Codec.ex_rightInv_pos : Toy.Codec.RightInv (fun b => !b) fun b => !b
Toy.Codec.ex_rightInv_neg : ¬Toy.Codec.RightInv (fun x => false) fun x => ()
Toy.Codec.ex_isEquiv_pos : Toy.Codec.IsEquiv (fun b => !b) fun b => !b
Toy.Codec.ex_isEquiv_neg : ¬Toy.Codec.IsEquiv (fun x => ()) fun x => false
Toy.Codec.ex_equiv_pos : Nonempty (Toy.Codec.Equiv Bool Bool)
Toy.Codec.ex_equiv_neg : ¬Nonempty (Toy.Codec.Equiv Bool Unit)
Toy.Codec.boolToNatCodec_decEnc : Toy.Codec.DecEnc Toy.Codec.boolToNatCodec
Toy.Codec.boolToNatCodec_encDec : Toy.Codec.EncDec Toy.Codec.boolToNatCodec
Toy.Codec.boolToNatCodec_decInj : Toy.Codec.DecInj Toy.Codec.boolToNatCodec
Toy.Codec.boolToNatCodec_lawful : Toy.Codec.Lawful Toy.Codec.boolToNatCodec
Toy.Codec.natSuccCodec_decEnc : Toy.Codec.DecEnc Toy.Codec.natSuccCodec
Toy.Codec.natSuccCodec_encDec : Toy.Codec.EncDec Toy.Codec.natSuccCodec
Toy.Codec.natSuccCodec_lawful : Toy.Codec.Lawful Toy.Codec.natSuccCodec
Toy.Codec.ex_decEnc_pos : Toy.Codec.DecEnc Toy.Codec.boolToNatCodec
Toy.Codec.ex_decEnc_neg : ¬Toy.Codec.DecEnc Toy.Codec.alwaysFailBoolCodec
Toy.Codec.ex_encDec_pos : Toy.Codec.EncDec Toy.Codec.boolToNatCodec
Toy.Codec.ex_encDec_neg : ¬Toy.Codec.EncDec Toy.Codec.nonCanonicalBoolCodec
Toy.Codec.ex_decInj_pos : Toy.Codec.DecInj Toy.Codec.boolToNatCodec
Toy.Codec.ex_decInj_neg : ¬Toy.Codec.DecInj Toy.Codec.nonCanonicalBoolCodec
Toy.Codec.ex_lawful_pos : Toy.Codec.Lawful Toy.Codec.boolToNatCodec
Toy.Codec.ex_lawful_neg_malleable : ¬Toy.Codec.Lawful Toy.Codec.nonCanonicalBoolCodec
Toy.Codec.ex_lawful_neg_failing : ¬Toy.Codec.Lawful Toy.Codec.alwaysFailBoolCodec
Toy.Codec.ex_canonicalize_pos : Toy.Codec.Lawful (Toy.Codec.canonicalize Toy.Codec.nonCanonicalBoolCodec) ∧
  (Toy.Codec.canonicalize Toy.Codec.nonCanonicalBoolCodec).dec 1 = some true ∧
    (Toy.Codec.canonicalize Toy.Codec.nonCanonicalBoolCodec).dec 2 = none
Toy.Codec.ex_canonicalize_neg : ¬Toy.Codec.DecEnc (Toy.Codec.canonicalize Toy.Codec.alwaysFailBoolCodec)
Toy.Codec.ex_classicalCodec_pos : (Toy.Codec.classicalCodec Toy.Codec.boolToNatCodec.enc).dec 1 = some true ∧
  (Toy.Codec.classicalCodec Toy.Codec.boolToNatCodec.enc).dec 2 = none
Toy.Codec.ex_classicalCodec_neg : ¬Toy.Codec.DecEnc (Toy.Codec.classicalCodec fun (x : Bool) => ())
Toy.Codec.ex_fiberSplit_pos : Toy.Codec.Lawful
  (Toy.Codec.codecOfFiberSplit Toy.Codec.boolToNatCodec.enc Toy.Codec.boolToNatFiberSplit)
Toy.Codec.ex_fiberSplit_neg_nonInjective : ¬Toy.Codec.DecEnc (Toy.Codec.codecOfFiberSplit (fun x => ()) Toy.Codec.constUnitFiberSplit)
Toy.Codec.ex_fiberSplitOfLawful_pos : Toy.Codec.fiberSplitOfLawful Toy.Codec.boolToNatCodec Toy.Codec.boolToNatCodec_decEnc Toy.Codec.boolToNatCodec_encDec
      1 =
    PSum.inl ⟨true, rfl⟩ ∧
  (match
      Toy.Codec.fiberSplitOfLawful Toy.Codec.boolToNatCodec Toy.Codec.boolToNatCodec_decEnc
        Toy.Codec.boolToNatCodec_encDec 2 with
    | PSum.inl val => false
    | PSum.inr val => true) =
    true
Toy.Codec.ex_fiberSplitOfLawful_neg : ¬∃ s,
    (Toy.Codec.codecOfFiberSplit Toy.Codec.alwaysFailBoolCodec.enc s).dec false =
      Toy.Codec.alwaysFailBoolCodec.dec false
Toy.Codec.codecId_decEnc.{u} : ∀ (A : Type u), Toy.Codec.DecEnc (Toy.Codec.Codec.id A)
Toy.Codec.codecId_encDec.{u} : ∀ (A : Type u), Toy.Codec.EncDec (Toy.Codec.Codec.id A)
Toy.Codec.codecId_lawful.{u} : ∀ (A : Type u), Toy.Codec.Lawful (Toy.Codec.Codec.id A)
Toy.Codec.ex_comp_pos : Toy.Codec.Lawful (Toy.Codec.boolToNatCodec.comp Toy.Codec.natSuccCodec)
Toy.Codec.ex_comp_neg : ¬Toy.Codec.DecEnc (Toy.Codec.alwaysFailBoolCodec.comp (Toy.Codec.Codec.id Bool))
Toy.Codec.ex_prod_pos : Toy.Codec.Lawful (Toy.Codec.boolToNatCodec.prod (Toy.Codec.Codec.id Bool))
Toy.Codec.ex_prod_neg : ¬Toy.Codec.EncDec (Toy.Codec.nonCanonicalBoolCodec.prod (Toy.Codec.Codec.id Bool))
Toy.Codec.ex_sum_pos : Toy.Codec.Lawful (Toy.Codec.boolToNatCodec.sum (Toy.Codec.Codec.id Bool))
Toy.Codec.ex_sum_neg : ¬Toy.Codec.DecEnc (Toy.Codec.alwaysFailBoolCodec.sum (Toy.Codec.Codec.id Bool))
Toy.Codec.varLenBoolFramedCodec_prefixDecEnc : Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec
Toy.Codec.varLenBoolFramedCodec_prefixEncDec : Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec
Toy.Codec.varLenBoolFramedCodec_prefixFree : Toy.Codec.PrefixFree Toy.Codec.varLenBoolFramedCodec.enc
Toy.Codec.varLenBoolFramedCodec_imagePrefixFree : Toy.Codec.ImagePrefixFree Toy.Codec.varLenBoolFramedCodec.enc
Toy.Codec.varLenBoolFramedCodec_nonEmptyEnc : Toy.Codec.NonEmptyEnc Toy.Codec.varLenBoolFramedCodec.enc
Toy.Codec.ex_prefixDecEnc_pos : Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec
Toy.Codec.ex_prefixDecEnc_neg : ¬Toy.Codec.PrefixDecEnc Toy.Codec.alwaysFailFramedCodec
Toy.Codec.ex_prefixEncDec_pos : Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec
Toy.Codec.ex_prefixEncDec_neg : ¬Toy.Codec.PrefixEncDec Toy.Codec.malleableFramedCodec
Toy.Codec.ex_seq_pos : Toy.Codec.PrefixDecEnc (Toy.Codec.varLenBoolFramedCodec.seq Toy.Codec.varLenBoolFramedCodec) ∧
  Toy.Codec.PrefixEncDec (Toy.Codec.varLenBoolFramedCodec.seq Toy.Codec.varLenBoolFramedCodec)
Toy.Codec.ex_seq_neg : ¬Toy.Codec.PrefixDecEnc (Toy.Codec.alwaysFailFramedCodec.seq Toy.Codec.varLenBoolFramedCodec)
Toy.Codec.ex_prefixFree_pos : Toy.Codec.PrefixFree Toy.Codec.varLenBoolFramedCodec.enc
Toy.Codec.ex_prefixFree_neg : ¬Toy.Codec.PrefixFree Toy.Codec.ambiguousEnc
Toy.Codec.ex_imagePrefixFree_pos : Toy.Codec.ImagePrefixFree Toy.Codec.varLenBoolFramedCodec.enc
Toy.Codec.ex_imagePrefixFree_neg : ¬Toy.Codec.ImagePrefixFree Toy.Codec.ambiguousEnc
Toy.Codec.ex_nonEmptyEnc_pos : Toy.Codec.NonEmptyEnc Toy.Codec.varLenBoolFramedCodec.enc
Toy.Codec.ex_nonEmptyEnc_neg : ¬Toy.Codec.NonEmptyEnc Toy.Codec.emptyUnitFramedCodec.enc
Toy.Codec.ex_listCodec_pos : (Toy.Codec.listCodec Toy.Codec.varLenBoolFramedCodec).dec
    ((Toy.Codec.listCodec Toy.Codec.varLenBoolFramedCodec).enc [false, true, false]) =
  some [false, true, false]
Toy.Codec.ex_listCodec_neg : ¬Toy.Codec.DecEnc (Toy.Codec.listCodec Toy.Codec.emptyUnitFramedCodec)
Toy.Codec.ex_decList_guard_rejects : Toy.Codec.decList Toy.Codec.emptyUnitFramedCodec [true] = none
Toy.Codec.ex_junk_pos : Nonempty (Toy.Codec.Junk Toy.Codec.boolToNatCodec)
Toy.Codec.ex_junk_neg : Toy.Codec.boolToNatCodec.dec 0 ≠ none
Toy.Codec.ex_inlMatcher_pos : Toy.Codec.inlMatcher (C := Nat) (Sum.inl true) = some true
Toy.Codec.ex_inlMatcher_neg : Eq (α := Option Bool) (Toy.Codec.inlMatcher (Sum.inr 0)) none
Toy.Codec.ex_decomp_pos : Toy.Codec.IsEquiv (Toy.Codec.decompToFun Toy.Codec.boolToNatCodec)
  (Toy.Codec.decompInvFun Toy.Codec.boolToNatCodec)
Toy.Codec.ex_decomp_neg_malleable : ¬Toy.Codec.IsEquiv (Toy.Codec.decompToFun Toy.Codec.nonCanonicalBoolCodec)
    (Toy.Codec.decompInvFun Toy.Codec.nonCanonicalBoolCodec)
Toy.Codec.ex_decomp_neg_failing : ¬Toy.Codec.IsEquiv (Toy.Codec.decompToFun Toy.Codec.alwaysFailUnitCodec)
    (Toy.Codec.decompInvFun Toy.Codec.alwaysFailUnitCodec)
Toy.Codec.natBoolSplit_leftInv : Toy.Codec.LeftInv Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun
Toy.Codec.natBoolSplit_rightInv : Toy.Codec.RightInv Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun
Toy.Codec.natBoolSubSplit_leftInv : Toy.Codec.LeftInv Toy.Codec.natBoolSubSplitToFun Toy.Codec.natBoolSubSplitInvFun
Toy.Codec.natBoolSubSplit_rightInv : Toy.Codec.RightInv Toy.Codec.natBoolSubSplitToFun Toy.Codec.natBoolSubSplitInvFun
Toy.Codec.natBoolSplit_eq_subSplit : Toy.Codec.codecOfSplit Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun =
  Toy.Codec.codecOfSplit Toy.Codec.natBoolSubSplitToFun Toy.Codec.natBoolSubSplitInvFun
Toy.Codec.ex_codecOfSplit_pos : Toy.Codec.codecOfSplit Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun =
  Toy.Codec.boolToNatCodec
Toy.Codec.ex_codecOfSplit_neg : ¬Toy.Codec.EncDec
    (Toy.Codec.codecOfSplit (fun (x : Bool) => Sum.inl ()) fun (x : Unit ⊕ Empty) =>
      match x with
      | Sum.inl PUnit.unit => false
      | Sum.inr e => e.elim)
Toy.Codec.ex_junkToC_pos : Toy.Codec.junkToC Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun ⟨2, rfl⟩ = 0 ∧
  Toy.Codec.junkToC Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun ⟨5, rfl⟩ = 3
Toy.Codec.ex_junkToC_neg_nonRightInv : Toy.Codec.LeftInv Toy.Codec.collidingJunkToFun Toy.Codec.collidingJunkInvFun ∧
  (∀ (a : Empty), Toy.Codec.collidingJunkToFun (Toy.Codec.collidingJunkInvFun (Sum.inl a)) = Sum.inl a) ∧
    Toy.Codec.junkToC Toy.Codec.collidingJunkToFun Toy.Codec.collidingJunkInvFun
        ⟨Toy.Codec.collidingJunkInvFun (Sum.inr true), rfl⟩ ≠
      true
Toy.Codec.ex_complementEquivOfCodecEq_pos : (Toy.Codec.complementEquivOfCodecEq Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun
        Toy.Codec.natBoolSubSplitToFun Toy.Codec.natBoolSubSplitInvFun Toy.Codec.natBoolSplit_leftInv
        Toy.Codec.natBoolSplit_rightInv Toy.Codec.natBoolSubSplit_leftInv Toy.Codec.natBoolSubSplit_rightInv
        Toy.Codec.natBoolSplit_eq_subSplit).toFun
    3 =
  ⟨5, Nat.le_add_left 2 3⟩
Toy.Codec.ex_complementEquivOfCodecEq_neg : ((Toy.Codec.codecOfSplit (fun (x : Bool) => Sum.inr ()) fun (x : Empty ⊕ Unit) =>
      match x with
      | Sum.inl e => e.elim
      | Sum.inr PUnit.unit => false) =
    Toy.Codec.codecOfSplit Sum.inr fun (x : Empty ⊕ Bool) =>
      match x with
      | Sum.inl e => e.elim
      | Sum.inr b => b) ∧
  ¬Nonempty (Toy.Codec.Equiv Unit Bool)
Toy.Codec.ex_codecId_ne_boolNot : Toy.Codec.Codec.id Bool ≠ Toy.Codec.boolNotCodec ∧
  Toy.Codec.Codec.id Bool ≠ Toy.Codec.alwaysFailBoolCodec
```

#### Canonical hypothesis-tightness counterexample signatures (`Counterexamples.lean`)

Printed with `set_option pp.funBinderTypes true` (see **How to read this section**): `ce_classicalCodec_decEnc_drop_inj`, `ce_codecOfSplit_eq_iff_drop_hl1`, `ce_codecOfSplit_eq_iff_drop_hr1`, `ce_codecOfSplit_eq_iff_drop_hl2`, `ce_codecOfSplit_eq_iff_drop_hr2`.

```lean
Toy.Codec.ce_decEnc_imp_enc_injective_drop_decEnc : Toy.Codec.EncDec Toy.Codec.alwaysFailConstCodec ∧
  ¬Function.Injective Toy.Codec.alwaysFailConstCodec.enc
Toy.Codec.ce_decEqSomeIff_imp_enc_injective_drop_hconv : Toy.Codec.EncDec Toy.Codec.alwaysFailConstCodec ∧
  (¬∀ (b : Unit) (a : Bool),
        Toy.Codec.alwaysFailConstCodec.dec b = some a ↔ Toy.Codec.alwaysFailConstCodec.enc a = b) ∧
    ¬Function.Injective Toy.Codec.alwaysFailConstCodec.enc
Toy.Codec.ce_decInj_not_implies_encDec : Toy.Codec.DecInj Toy.Codec.shiftedBoolCodec ∧
  ¬Toy.Codec.DecEnc Toy.Codec.shiftedBoolCodec ∧ ¬Toy.Codec.EncDec Toy.Codec.shiftedBoolCodec
Toy.Codec.ce_dec_unique_drop_henc : Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
  Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.DecEnc Toy.Codec.boolNotCodec ∧
      Toy.Codec.EncDec Toy.Codec.boolNotCodec ∧
        (Toy.Codec.Codec.id Bool).dec ≠ Toy.Codec.boolNotCodec.dec
Toy.Codec.ce_dec_unique_drop_hde1 : Toy.Codec.alwaysFailBoolCodec.enc = (Toy.Codec.Codec.id Bool).enc ∧
  Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
    Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
      Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
        Toy.Codec.alwaysFailBoolCodec.dec ≠ (Toy.Codec.Codec.id Bool).dec
Toy.Codec.ce_dec_unique_drop_hed1 : Toy.Codec.nonCanonicalBoolCodec.enc = Toy.Codec.boolToNatCodec.enc ∧
  Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
    Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧
      Toy.Codec.EncDec Toy.Codec.boolToNatCodec ∧
        Toy.Codec.nonCanonicalBoolCodec.dec ≠ Toy.Codec.boolToNatCodec.dec
Toy.Codec.ce_dec_unique_drop_hde2 : (Toy.Codec.Codec.id Bool).enc = Toy.Codec.alwaysFailBoolCodec.enc ∧
  Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
      Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
        (Toy.Codec.Codec.id Bool).dec ≠ Toy.Codec.alwaysFailBoolCodec.dec
Toy.Codec.ce_dec_unique_drop_hed2 : Toy.Codec.boolToNatCodec.enc = Toy.Codec.nonCanonicalBoolCodec.enc ∧
  Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧
    Toy.Codec.EncDec Toy.Codec.boolToNatCodec ∧
      Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
        Toy.Codec.boolToNatCodec.dec ≠ Toy.Codec.nonCanonicalBoolCodec.dec
Toy.Codec.ce_classicalCodec_decEnc_drop_inj : (¬Function.Injective fun (x : Bool) => ()) ∧ ¬Toy.Codec.DecEnc (Toy.Codec.classicalCodec fun (x : Bool) => ())
Toy.Codec.ce_classicalCodec_recover_drop_decEnc : Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
  Toy.Codec.classicalCodec Toy.Codec.alwaysFailBoolCodec.enc ≠ Toy.Codec.alwaysFailBoolCodec
Toy.Codec.ce_classicalCodec_recover_drop_encDec : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
  Toy.Codec.classicalCodec Toy.Codec.nonCanonicalBoolCodec.enc ≠ Toy.Codec.nonCanonicalBoolCodec
Toy.Codec.ce_codecOfFiberSplit_decEnc_drop_inj : Toy.Codec.EncDec (Toy.Codec.codecOfFiberSplit (fun x => ()) Toy.Codec.constUnitFiberSplit) ∧
  ¬Toy.Codec.DecEnc (Toy.Codec.codecOfFiberSplit (fun x => ()) Toy.Codec.constUnitFiberSplit)
Toy.Codec.ce_codecOfFiberSplit_eq_drop_decEnc : Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
  Toy.Codec.codecOfFiberSplit Toy.Codec.alwaysFailBoolCodec.enc Toy.Codec.idBoolFiberSplit ≠
    Toy.Codec.alwaysFailBoolCodec
Toy.Codec.ce_codecOfFiberSplit_eq_drop_encDec : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
  Toy.Codec.codecOfFiberSplit Toy.Codec.nonCanonicalBoolCodec.enc
      Toy.Codec.nonCanonicalBoolFiberSplit ≠
    Toy.Codec.nonCanonicalBoolCodec
Toy.Codec.ce_lawful_dec_isSome_drop_decEnc : Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
  ¬∀ (b : Bool),
      (Toy.Codec.alwaysFailBoolCodec.dec b).isSome = true ↔
        ∃ a, Toy.Codec.alwaysFailBoolCodec.enc a = b
Toy.Codec.ce_lawful_dec_isSome_drop_encDec : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
  ¬∀ (b : Nat),
      (Toy.Codec.nonCanonicalBoolCodec.dec b).isSome = true ↔
        ∃ a, Toy.Codec.nonCanonicalBoolCodec.enc a = b
Toy.Codec.ce_junk_iff_not_in_image_of_lawful_drop_decEnc : Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
  ¬∀ (b : Bool),
      Toy.Codec.alwaysFailBoolCodec.dec b = none ↔
        ∀ (a : Bool), Toy.Codec.alwaysFailBoolCodec.enc a ≠ b
Toy.Codec.ce_junk_iff_not_in_image_of_lawful_drop_encDec : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
  ¬∀ (b : Nat),
      Toy.Codec.nonCanonicalBoolCodec.dec b = none ↔
        ∀ (a : Bool), Toy.Codec.nonCanonicalBoolCodec.enc a ≠ b
Toy.Codec.ce_canonicalize_decEnc_drop_decEnc : Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
  ¬Toy.Codec.DecEnc (Toy.Codec.canonicalize Toy.Codec.alwaysFailBoolCodec)
Toy.Codec.ce_comp_decEnc_drop_hde1 : Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
  Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
      ¬Toy.Codec.DecEnc (Toy.Codec.alwaysFailBoolCodec.comp (Toy.Codec.Codec.id Bool))
Toy.Codec.ce_comp_decEnc_drop_hde2 : Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
  Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
      ¬Toy.Codec.DecEnc ((Toy.Codec.Codec.id Bool).comp Toy.Codec.alwaysFailBoolCodec)
Toy.Codec.ce_comp_encDec_drop_hed1 : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
  Toy.Codec.DecEnc (Toy.Codec.Codec.id Nat) ∧
    Toy.Codec.EncDec (Toy.Codec.Codec.id Nat) ∧
      ¬Toy.Codec.EncDec (Toy.Codec.nonCanonicalBoolCodec.comp (Toy.Codec.Codec.id Nat))
Toy.Codec.ce_comp_encDec_drop_hed2 : Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
  Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
      ¬Toy.Codec.EncDec ((Toy.Codec.Codec.id Bool).comp Toy.Codec.nonCanonicalBoolCodec)
Toy.Codec.ce_prod_decEnc_drop_hde1 : Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
  Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
      ¬Toy.Codec.DecEnc (Toy.Codec.alwaysFailBoolCodec.prod (Toy.Codec.Codec.id Bool))
Toy.Codec.ce_prod_decEnc_drop_hde2 : Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
  Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
      ¬Toy.Codec.DecEnc ((Toy.Codec.Codec.id Bool).prod Toy.Codec.alwaysFailBoolCodec)
Toy.Codec.ce_prod_encDec_drop_hed1 : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
  Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
      ¬Toy.Codec.EncDec (Toy.Codec.nonCanonicalBoolCodec.prod (Toy.Codec.Codec.id Bool))
Toy.Codec.ce_prod_encDec_drop_hed2 : Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
  Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
      ¬Toy.Codec.EncDec ((Toy.Codec.Codec.id Bool).prod Toy.Codec.nonCanonicalBoolCodec)
Toy.Codec.ce_sum_decEnc_drop_hde1 : Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
  Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
      ¬Toy.Codec.DecEnc (Toy.Codec.alwaysFailBoolCodec.sum (Toy.Codec.Codec.id Bool))
Toy.Codec.ce_sum_decEnc_drop_hde2 : Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
  Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.EncDec Toy.Codec.alwaysFailBoolCodec ∧
      ¬Toy.Codec.DecEnc ((Toy.Codec.Codec.id Bool).sum Toy.Codec.alwaysFailBoolCodec)
Toy.Codec.ce_sum_encDec_drop_hed1 : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
  Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
      ¬Toy.Codec.EncDec (Toy.Codec.nonCanonicalBoolCodec.sum (Toy.Codec.Codec.id Bool))
Toy.Codec.ce_sum_encDec_drop_hed2 : Toy.Codec.DecEnc (Toy.Codec.Codec.id Bool) ∧
  Toy.Codec.EncDec (Toy.Codec.Codec.id Bool) ∧
    Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
      ¬Toy.Codec.EncDec ((Toy.Codec.Codec.id Bool).sum Toy.Codec.nonCanonicalBoolCodec)
Toy.Codec.ce_prefixDecEnc_imp_prefixFree_drop_hpde : Toy.Codec.PrefixEncDec Toy.Codec.ambiguousFailFramedCodec ∧
  Toy.Codec.NonEmptyEnc Toy.Codec.ambiguousFailFramedCodec.enc ∧
    ¬Toy.Codec.PrefixFree Toy.Codec.ambiguousFailFramedCodec.enc
Toy.Codec.ce_seq_prefixDecEnc_drop_h1 : Toy.Codec.PrefixEncDec Toy.Codec.alwaysFailFramedCodec ∧
  Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec ∧
    Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec ∧
      ¬Toy.Codec.PrefixDecEnc (Toy.Codec.alwaysFailFramedCodec.seq Toy.Codec.varLenBoolFramedCodec)
Toy.Codec.ce_seq_prefixDecEnc_drop_h2 : Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec ∧
  Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec ∧
    Toy.Codec.PrefixEncDec Toy.Codec.alwaysFailFramedCodec ∧
      ¬Toy.Codec.PrefixDecEnc (Toy.Codec.varLenBoolFramedCodec.seq Toy.Codec.alwaysFailFramedCodec)
Toy.Codec.ce_seq_prefixEncDec_drop_h1 : Toy.Codec.PrefixDecEnc Toy.Codec.malleableFramedCodec ∧
  Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec ∧
    Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec ∧
      ¬Toy.Codec.PrefixEncDec (Toy.Codec.malleableFramedCodec.seq Toy.Codec.varLenBoolFramedCodec)
Toy.Codec.ce_seq_prefixEncDec_drop_h2 : Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec ∧
  Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec ∧
    Toy.Codec.PrefixDecEnc Toy.Codec.malleableFramedCodec ∧
      ¬Toy.Codec.PrefixEncDec (Toy.Codec.varLenBoolFramedCodec.seq Toy.Codec.malleableFramedCodec)
Toy.Codec.ce_listCodec_decEnc_iff_drop_prefixDecEnc : Toy.Codec.NonEmptyEnc Toy.Codec.alwaysFailFramedCodec.enc ∧
  Toy.Codec.PrefixEncDec Toy.Codec.alwaysFailFramedCodec ∧
    ¬(Toy.Codec.DecEnc (Toy.Codec.listCodec Toy.Codec.alwaysFailFramedCodec) ↔
        Toy.Codec.NonEmptyEnc Toy.Codec.alwaysFailFramedCodec.enc)
Toy.Codec.ce_listCodec_decEnc_drop_nonEmptyEnc : Toy.Codec.PrefixDecEnc Toy.Codec.emptyUnitFramedCodec ∧
  Toy.Codec.PrefixEncDec Toy.Codec.emptyUnitFramedCodec ∧
    Toy.Codec.PrefixFree Toy.Codec.emptyUnitFramedCodec.enc ∧
      ¬Toy.Codec.NonEmptyEnc Toy.Codec.emptyUnitFramedCodec.enc ∧
        ¬Toy.Codec.DecEnc (Toy.Codec.listCodec Toy.Codec.emptyUnitFramedCodec)
Toy.Codec.ce_listCodec_encDec_drop_prefixEncDec : Toy.Codec.PrefixDecEnc Toy.Codec.malleableFramedCodec ∧
  Toy.Codec.NonEmptyEnc Toy.Codec.malleableFramedCodec.enc ∧
    ¬Toy.Codec.EncDec (Toy.Codec.listCodec Toy.Codec.malleableFramedCodec)
Toy.Codec.ce_lawful_decomp_drop_decEnc : Toy.Codec.EncDec Toy.Codec.alwaysFailUnitCodec ∧
  Toy.Codec.LeftInv (Toy.Codec.decompToFun Toy.Codec.alwaysFailUnitCodec)
      (Toy.Codec.decompInvFun Toy.Codec.alwaysFailUnitCodec) ∧
    ¬Toy.Codec.RightInv (Toy.Codec.decompToFun Toy.Codec.alwaysFailUnitCodec)
          (Toy.Codec.decompInvFun Toy.Codec.alwaysFailUnitCodec) ∧
      ¬Toy.Codec.IsEquiv (Toy.Codec.decompToFun Toy.Codec.alwaysFailUnitCodec)
            (Toy.Codec.decompInvFun Toy.Codec.alwaysFailUnitCodec) ∧
        ¬Nonempty (Toy.Codec.Equiv Unit (Unit ⊕ Toy.Codec.Junk Toy.Codec.alwaysFailUnitCodec))
Toy.Codec.ce_lawful_decomp_drop_encDec : Toy.Codec.DecEnc Toy.Codec.malleableUnitBoolCodec ∧
  Toy.Codec.RightInv (Toy.Codec.decompToFun Toy.Codec.malleableUnitBoolCodec)
      (Toy.Codec.decompInvFun Toy.Codec.malleableUnitBoolCodec) ∧
    ¬Toy.Codec.LeftInv (Toy.Codec.decompToFun Toy.Codec.malleableUnitBoolCodec)
          (Toy.Codec.decompInvFun Toy.Codec.malleableUnitBoolCodec) ∧
      ¬Toy.Codec.IsEquiv (Toy.Codec.decompToFun Toy.Codec.malleableUnitBoolCodec)
            (Toy.Codec.decompInvFun Toy.Codec.malleableUnitBoolCodec) ∧
        ¬Nonempty (Toy.Codec.Equiv Bool (Unit ⊕ Toy.Codec.Junk Toy.Codec.malleableUnitBoolCodec))
Toy.Codec.ce_decomp_induces_drop_leftInv : Toy.Codec.RightInv Toy.Codec.badLeftSplitToFun Toy.Codec.badLeftSplitInvFun ∧
  ¬(Toy.Codec.DecEnc
        (Toy.Codec.codecOfSplit Toy.Codec.badLeftSplitToFun Toy.Codec.badLeftSplitInvFun) ∧
      Toy.Codec.EncDec
          (Toy.Codec.codecOfSplit Toy.Codec.badLeftSplitToFun Toy.Codec.badLeftSplitInvFun) ∧
        (∀ (k : Empty),
            (Toy.Codec.codecOfSplit Toy.Codec.badLeftSplitToFun Toy.Codec.badLeftSplitInvFun).dec
                (Toy.Codec.badLeftSplitInvFun (Sum.inr k)) =
              none) ∧
          (∀
              (j :
                Toy.Codec.Junk
                  (Toy.Codec.codecOfSplit Toy.Codec.badLeftSplitToFun
                    Toy.Codec.badLeftSplitInvFun)),
              Toy.Codec.badLeftSplitInvFun
                  (Sum.inr
                    (Toy.Codec.junkToC Toy.Codec.badLeftSplitToFun Toy.Codec.badLeftSplitInvFun
                      j)) =
                j.val) ∧
            (∀ (k : Empty)
                (hj :
                  (Toy.Codec.codecOfSplit Toy.Codec.badLeftSplitToFun
                          Toy.Codec.badLeftSplitInvFun).dec
                      (Toy.Codec.badLeftSplitInvFun (Sum.inr k)) =
                    none),
                Toy.Codec.junkToC Toy.Codec.badLeftSplitToFun Toy.Codec.badLeftSplitInvFun
                    ⟨Toy.Codec.badLeftSplitInvFun (Sum.inr k), hj⟩ =
                  k) ∧
              ∀ (b : Bool),
                Sum.map id Subtype.val
                    (Toy.Codec.decompToFun
                      (Toy.Codec.codecOfSplit Toy.Codec.badLeftSplitToFun
                        Toy.Codec.badLeftSplitInvFun)
                      b) =
                  Sum.map id (fun k => Toy.Codec.badLeftSplitInvFun (Sum.inr k))
                    (Toy.Codec.badLeftSplitToFun b))
Toy.Codec.ce_decomp_induces_drop_rightInv : Toy.Codec.LeftInv Toy.Codec.badRightInlSplitToFun Toy.Codec.badRightInlSplitInvFun ∧
  ¬(Toy.Codec.DecEnc
        (Toy.Codec.codecOfSplit Toy.Codec.badRightInlSplitToFun Toy.Codec.badRightInlSplitInvFun) ∧
      Toy.Codec.EncDec
          (Toy.Codec.codecOfSplit Toy.Codec.badRightInlSplitToFun
            Toy.Codec.badRightInlSplitInvFun) ∧
        (∀ (k : Unit),
            (Toy.Codec.codecOfSplit Toy.Codec.badRightInlSplitToFun
                    Toy.Codec.badRightInlSplitInvFun).dec
                (Toy.Codec.badRightInlSplitInvFun (Sum.inr k)) =
              none) ∧
          (∀
              (j :
                Toy.Codec.Junk
                  (Toy.Codec.codecOfSplit Toy.Codec.badRightInlSplitToFun
                    Toy.Codec.badRightInlSplitInvFun)),
              Toy.Codec.badRightInlSplitInvFun
                  (Sum.inr
                    (Toy.Codec.junkToC Toy.Codec.badRightInlSplitToFun
                      Toy.Codec.badRightInlSplitInvFun j)) =
                j.val) ∧
            (∀ (k : Unit)
                (hj :
                  (Toy.Codec.codecOfSplit Toy.Codec.badRightInlSplitToFun
                          Toy.Codec.badRightInlSplitInvFun).dec
                      (Toy.Codec.badRightInlSplitInvFun (Sum.inr k)) =
                    none),
                Toy.Codec.junkToC Toy.Codec.badRightInlSplitToFun Toy.Codec.badRightInlSplitInvFun
                    ⟨Toy.Codec.badRightInlSplitInvFun (Sum.inr k), hj⟩ =
                  k) ∧
              ∀ (b : Unit),
                Sum.map id Subtype.val
                    (Toy.Codec.decompToFun
                      (Toy.Codec.codecOfSplit Toy.Codec.badRightInlSplitToFun
                        Toy.Codec.badRightInlSplitInvFun)
                      b) =
                  Sum.map id (fun k => Toy.Codec.badRightInlSplitInvFun (Sum.inr k))
                    (Toy.Codec.badRightInlSplitToFun b))
Toy.Codec.ce_decomp_induces_drop_rightInv_inr : Toy.Codec.LeftInv Toy.Codec.badRightInrSplitToFun Toy.Codec.badRightInrSplitInvFun ∧
  (∀ (a : Unit),
      Toy.Codec.badRightInrSplitToFun (Toy.Codec.badRightInrSplitInvFun (Sum.inl a)) = Sum.inl a) ∧
    Toy.Codec.DecEnc
        (Toy.Codec.codecOfSplit Toy.Codec.badRightInrSplitToFun Toy.Codec.badRightInrSplitInvFun) ∧
      Toy.Codec.EncDec
          (Toy.Codec.codecOfSplit Toy.Codec.badRightInrSplitToFun
            Toy.Codec.badRightInrSplitInvFun) ∧
        ¬∀ (k : Bool),
            (Toy.Codec.codecOfSplit Toy.Codec.badRightInrSplitToFun
                    Toy.Codec.badRightInrSplitInvFun).dec
                (Toy.Codec.badRightInrSplitInvFun (Sum.inr k)) =
              none
Toy.Codec.ce_codecOfSplit_eq_iff_drop_hl1 : Toy.Codec.RightInv Toy.Codec.badEmptyUnitSplitToFun Toy.Codec.badEmptyUnitSplitInvFun ∧
  Toy.Codec.LeftInv Toy.Codec.emptyBoolSplitToFun Toy.Codec.emptyBoolSplitInvFun ∧
    Toy.Codec.RightInv Toy.Codec.emptyBoolSplitToFun Toy.Codec.emptyBoolSplitInvFun ∧
      ¬(Toy.Codec.codecOfSplit Toy.Codec.badEmptyUnitSplitToFun Toy.Codec.badEmptyUnitSplitInvFun =
            Toy.Codec.codecOfSplit Toy.Codec.emptyBoolSplitToFun Toy.Codec.emptyBoolSplitInvFun ↔
          ∃ (φ : Toy.Codec.Equiv Unit Bool),
            ∀ (b : Bool), Toy.Codec.emptyBoolSplitToFun b = Sum.map id φ.toFun (Toy.Codec.badEmptyUnitSplitToFun b))
Toy.Codec.ce_codecOfSplit_eq_iff_drop_hr1 : Toy.Codec.LeftInv Toy.Codec.badRightInrSplitToFun Toy.Codec.badRightInrSplitInvFun ∧
  Toy.Codec.LeftInv Toy.Codec.unitEmptySplitToFun Toy.Codec.unitEmptySplitInvFun ∧
    Toy.Codec.RightInv Toy.Codec.unitEmptySplitToFun Toy.Codec.unitEmptySplitInvFun ∧
      ¬(Toy.Codec.codecOfSplit Toy.Codec.badRightInrSplitToFun Toy.Codec.badRightInrSplitInvFun =
            Toy.Codec.codecOfSplit Toy.Codec.unitEmptySplitToFun Toy.Codec.unitEmptySplitInvFun ↔
          ∃ (φ : Toy.Codec.Equiv Bool Empty),
            ∀ (b : Unit), Toy.Codec.unitEmptySplitToFun b = Sum.map id φ.toFun (Toy.Codec.badRightInrSplitToFun b))
Toy.Codec.ce_codecOfSplit_eq_iff_drop_hl2 : Toy.Codec.LeftInv Toy.Codec.emptyBoolSplitToFun Toy.Codec.emptyBoolSplitInvFun ∧
  Toy.Codec.RightInv Toy.Codec.emptyBoolSplitToFun Toy.Codec.emptyBoolSplitInvFun ∧
    Toy.Codec.RightInv Toy.Codec.badEmptyUnitSplitToFun Toy.Codec.badEmptyUnitSplitInvFun ∧
      ¬(Toy.Codec.codecOfSplit Toy.Codec.emptyBoolSplitToFun Toy.Codec.emptyBoolSplitInvFun =
            Toy.Codec.codecOfSplit Toy.Codec.badEmptyUnitSplitToFun Toy.Codec.badEmptyUnitSplitInvFun ↔
          ∃ (φ : Toy.Codec.Equiv Bool Unit),
            ∀ (b : Bool), Toy.Codec.badEmptyUnitSplitToFun b = Sum.map id φ.toFun (Toy.Codec.emptyBoolSplitToFun b))
Toy.Codec.ce_codecOfSplit_eq_iff_drop_hr2 : Toy.Codec.LeftInv Toy.Codec.unitEmptySplitToFun Toy.Codec.unitEmptySplitInvFun ∧
  Toy.Codec.RightInv Toy.Codec.unitEmptySplitToFun Toy.Codec.unitEmptySplitInvFun ∧
    Toy.Codec.LeftInv Toy.Codec.badRightInrSplitToFun Toy.Codec.badRightInrSplitInvFun ∧
      ¬(Toy.Codec.codecOfSplit Toy.Codec.unitEmptySplitToFun Toy.Codec.unitEmptySplitInvFun =
            Toy.Codec.codecOfSplit Toy.Codec.badRightInrSplitToFun Toy.Codec.badRightInrSplitInvFun ↔
          ∃ (φ : Toy.Codec.Equiv Empty Bool),
            ∀ (b : Unit), Toy.Codec.badRightInrSplitToFun b = Sum.map id φ.toFun (Toy.Codec.unitEmptySplitToFun b))
Toy.Codec.ce_intertwines_drop_heq : Toy.Codec.LeftInv Toy.Codec.splitBoolFalseToFun Toy.Codec.splitBoolFalseInvFun ∧
  Toy.Codec.RightInv Toy.Codec.splitBoolFalseToFun Toy.Codec.splitBoolFalseInvFun ∧
    Toy.Codec.LeftInv Toy.Codec.splitBoolTrueToFun Toy.Codec.splitBoolTrueInvFun ∧
      Toy.Codec.RightInv Toy.Codec.splitBoolTrueToFun Toy.Codec.splitBoolTrueInvFun ∧
        ¬∃ φ,
            ∀ (b : Bool),
              Toy.Codec.splitBoolTrueToFun b = Sum.map id φ (Toy.Codec.splitBoolFalseToFun b)
Toy.Codec.ce_nonEmptyEnc_of_prefixDecEnc_of_ne_drop_hpde : false ≠ true ∧
  Toy.Codec.PrefixEncDec Toy.Codec.emptyBoolFailFramedCodec ∧
    ¬Toy.Codec.PrefixDecEnc Toy.Codec.emptyBoolFailFramedCodec ∧
      ¬Toy.Codec.NonEmptyEnc Toy.Codec.emptyBoolFailFramedCodec.enc
```

#### Non-vacuity witness signatures (`Witnesses.lean`)

Printed with `set_option pp.funBinderTypes true` (see **How to read this section**): `nv_classicalCodec_encDec`, `nv_codecOfSplit_eq_iff_exists_intertwining_equiv`.

```lean
Toy.Codec.nv_decEnc_imp_enc_injective : Toy.Codec.DecEnc Toy.Codec.boolToNatCodec
Toy.Codec.nv_lawful_iff_dec_eq_some_iff : (Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧ Toy.Codec.EncDec Toy.Codec.boolToNatCodec) ∧
  ∀ (b : Nat) (a : Bool),
    Toy.Codec.boolToNatCodec.dec b = some a ↔ Toy.Codec.boolToNatCodec.enc a = b
Toy.Codec.nv_decEqSomeIff_imp_enc_injective : ∀ (b : Nat) (a : Bool), Toy.Codec.boolToNatCodec.dec b = some a ↔ Toy.Codec.boolToNatCodec.enc a = b
Toy.Codec.nv_lawful_iff_decEnc_and_decInj : (Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧ Toy.Codec.EncDec Toy.Codec.boolToNatCodec) ∧
  Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧ Toy.Codec.DecInj Toy.Codec.boolToNatCodec
Toy.Codec.nv_dec_unique_of_lawful : Toy.Codec.boolToNatCodec.enc =
    (Toy.Codec.codecOfFiberSplit Toy.Codec.boolToNatCodec.enc Toy.Codec.boolToNatFiberSplit).enc ∧
  Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧
    Toy.Codec.EncDec Toy.Codec.boolToNatCodec ∧
      Toy.Codec.DecEnc
          (Toy.Codec.codecOfFiberSplit Toy.Codec.boolToNatCodec.enc Toy.Codec.boolToNatFiberSplit) ∧
        Toy.Codec.EncDec
          (Toy.Codec.codecOfFiberSplit Toy.Codec.boolToNatCodec.enc Toy.Codec.boolToNatFiberSplit)
Toy.Codec.nv_classicalCodec_decEnc_of_injective : Function.Injective Toy.Codec.boolToNatCodec.enc
Toy.Codec.nv_classicalCodec_encDec : Toy.Codec.EncDec (Toy.Codec.classicalCodec Toy.Codec.boolToNatCodec.enc) ∧
  Toy.Codec.EncDec (Toy.Codec.classicalCodec fun (x : Bool) => ())
Toy.Codec.nv_classicalCodec_recover_of_lawful : Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧ Toy.Codec.EncDec Toy.Codec.boolToNatCodec
Toy.Codec.nv_codecOfFiberSplit_decEnc_of_injective : Function.Injective Toy.Codec.boolToNatCodec.enc ∧
  Nonempty (Toy.Codec.FiberSplit Toy.Codec.boolToNatCodec.enc)
Toy.Codec.nv_codecOfFiberSplit_eq_of_lawful : Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧
  Toy.Codec.EncDec Toy.Codec.boolToNatCodec ∧
    Toy.Codec.codecOfFiberSplit Toy.Codec.boolToNatCodec.enc Toy.Codec.boolToNatFiberSplit =
      Toy.Codec.boolToNatCodec
Toy.Codec.nv_lawful_dec_isSome_iff_mem_range : Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧ Toy.Codec.EncDec Toy.Codec.boolToNatCodec
Toy.Codec.nv_junk_iff_not_in_image_of_lawful : Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧ Toy.Codec.EncDec Toy.Codec.boolToNatCodec
Toy.Codec.nv_canonicalize_decEnc_of_decEnc : Toy.Codec.DecEnc Toy.Codec.nonCanonicalBoolCodec ∧
  ¬Toy.Codec.EncDec Toy.Codec.nonCanonicalBoolCodec ∧
    Toy.Codec.DecEnc (Toy.Codec.canonicalize Toy.Codec.nonCanonicalBoolCodec) ∧
      Toy.Codec.EncDec (Toy.Codec.canonicalize Toy.Codec.nonCanonicalBoolCodec)
Toy.Codec.nv_comp_decEnc : Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧ Toy.Codec.DecEnc Toy.Codec.natSuccCodec
Toy.Codec.nv_comp_encDec : Toy.Codec.EncDec Toy.Codec.boolToNatCodec ∧ Toy.Codec.EncDec Toy.Codec.natSuccCodec
Toy.Codec.nv_prod_decEnc : Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧ Toy.Codec.DecEnc Toy.Codec.natSuccCodec
Toy.Codec.nv_prod_encDec : Toy.Codec.EncDec Toy.Codec.boolToNatCodec ∧ Toy.Codec.EncDec Toy.Codec.natSuccCodec
Toy.Codec.nv_sum_decEnc : Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧ Toy.Codec.DecEnc Toy.Codec.natSuccCodec
Toy.Codec.nv_sum_encDec : Toy.Codec.EncDec Toy.Codec.boolToNatCodec ∧ Toy.Codec.EncDec Toy.Codec.natSuccCodec
Toy.Codec.nv_framed_lawful_iff_decPrefix_eq_some_iff : (Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec ∧
    Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec) ∧
  ∀ (xs : List Bool) (a : Bool) (rest : List Bool),
    Toy.Codec.varLenBoolFramedCodec.decPrefix xs = some (a, rest) ↔
      xs = Toy.Codec.varLenBoolFramedCodec.enc a ++ rest
Toy.Codec.nv_prefixDecEnc_imp_prefixFree : Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec
Toy.Codec.nv_seq_prefixDecEnc : Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec ∧
  Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec
Toy.Codec.nv_seq_prefixEncDec : Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec ∧
  Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec
Toy.Codec.nv_listCodec_decEnc_iff_nonEmptyEnc : (Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec ∧
    Toy.Codec.NonEmptyEnc Toy.Codec.varLenBoolFramedCodec.enc) ∧
  Toy.Codec.PrefixDecEnc Toy.Codec.emptyUnitFramedCodec ∧
    ¬Toy.Codec.NonEmptyEnc Toy.Codec.emptyUnitFramedCodec.enc ∧
      ¬Toy.Codec.DecEnc (Toy.Codec.listCodec Toy.Codec.emptyUnitFramedCodec)
Toy.Codec.nv_listCodec_encDec : Toy.Codec.PrefixEncDec Toy.Codec.varLenBoolFramedCodec
Toy.Codec.nv_decomp_isEquiv_iff_lawful : (Toy.Codec.IsEquiv (Toy.Codec.decompToFun Toy.Codec.boolToNatCodec)
      (Toy.Codec.decompInvFun Toy.Codec.boolToNatCodec) ∧
    Toy.Codec.DecEnc Toy.Codec.boolToNatCodec ∧ Toy.Codec.EncDec Toy.Codec.boolToNatCodec) ∧
  (¬Toy.Codec.IsEquiv (Toy.Codec.decompToFun Toy.Codec.nonCanonicalBoolCodec)
          (Toy.Codec.decompInvFun Toy.Codec.nonCanonicalBoolCodec) ∧
      ¬Toy.Codec.EncDec Toy.Codec.nonCanonicalBoolCodec) ∧
    ¬Toy.Codec.IsEquiv (Toy.Codec.decompToFun Toy.Codec.alwaysFailUnitCodec)
          (Toy.Codec.decompInvFun Toy.Codec.alwaysFailUnitCodec) ∧
      ¬Toy.Codec.DecEnc Toy.Codec.alwaysFailUnitCodec
Toy.Codec.nv_decomp_induces_lawful_and_complement : Toy.Codec.LeftInv Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun ∧
  Toy.Codec.RightInv Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun
Toy.Codec.nv_codecOfSplit_eq_iff_exists_intertwining_equiv : (Toy.Codec.LeftInv Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun ∧
    Toy.Codec.RightInv Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun ∧
      Toy.Codec.LeftInv Toy.Codec.natBoolSubSplitToFun Toy.Codec.natBoolSubSplitInvFun ∧
        Toy.Codec.RightInv Toy.Codec.natBoolSubSplitToFun Toy.Codec.natBoolSubSplitInvFun ∧
          Toy.Codec.codecOfSplit Toy.Codec.natBoolSplitToFun Toy.Codec.natBoolSplitInvFun =
              Toy.Codec.codecOfSplit Toy.Codec.natBoolSubSplitToFun Toy.Codec.natBoolSubSplitInvFun ∧
            ∀ (b : Nat),
              Toy.Codec.natBoolSubSplitToFun b =
                Sum.map id Toy.Codec.natBoolSubEquiv.toFun (Toy.Codec.natBoolSplitToFun b)) ∧
  Toy.Codec.LeftInv Toy.Codec.splitBoolFalseToFun Toy.Codec.splitBoolFalseInvFun ∧
    Toy.Codec.RightInv Toy.Codec.splitBoolFalseToFun Toy.Codec.splitBoolFalseInvFun ∧
      Toy.Codec.LeftInv Toy.Codec.splitBoolTrueToFun Toy.Codec.splitBoolTrueInvFun ∧
        Toy.Codec.RightInv Toy.Codec.splitBoolTrueToFun Toy.Codec.splitBoolTrueInvFun ∧
          Toy.Codec.codecOfSplit Toy.Codec.splitBoolFalseToFun Toy.Codec.splitBoolFalseInvFun ≠
              Toy.Codec.codecOfSplit Toy.Codec.splitBoolTrueToFun Toy.Codec.splitBoolTrueInvFun ∧
            ¬∃ (φ : Toy.Codec.Equiv Unit Unit),
                ∀ (b : Bool), Toy.Codec.splitBoolTrueToFun b = Sum.map id φ.toFun (Toy.Codec.splitBoolFalseToFun b)
Toy.Codec.nv_nonEmptyEnc_of_prefixDecEnc_of_ne : Toy.Codec.PrefixDecEnc Toy.Codec.varLenBoolFramedCodec ∧
  false ≠ true ∧ Toy.Codec.NonEmptyEnc Toy.Codec.varLenBoolFramedCodec.enc
```

## Boundaries

### Non-claims (read first)

**Package-wide non-claims:**

- The laws are stated for one encoder function. A format that permits several encodings of one value cannot satisfy `EncDec` for any single encoder; for such formats the corresponding requirement is that the decoder accepts exactly the strings the format relates to the decoded value. Failing `EncDec` for a chosen encoder is therefore not by itself evidence that malformed input is accepted.
- The model has no byte layouts, lengths, state, or error reporting. Nothing here is a security property of an implemented parser.
- No statement about lenses is proved in this package. 'Dual to lenses' describes the shape of the result; the lens-side decomposition needs extra assumptions (for instance an inhabited view type).
- Proof-level axiom qualifiers (*without `Classical.choice`*, *zero axioms*) are properties of the checked proof terms recorded in `audit/axioms.json` (**Evidence**), not consequences of the theorem types alone.

**Per-result non-claims:**

- **Card 1 (`decEnc_imp_enc_injective`):**
  - Does not show that DecEnc c implies EncDec c or whole-input decoder injectivity (DecInj c); see decEnc_admits_malleable_codec.
  - Does not show that EncDec c implies Function.Injective c.enc; alwaysFailConstCodec satisfies EncDec with a constant encoder Bool → Unit.
  - Does not construct an executable decoder for an arbitrary injective function without FiberSplit or Classical.choice.
- **Card 2 (`lawful_iff_dec_eq_some_iff`):**
  - Does not show that the encoder implements any intended format. Classically, every injective function `A → B` is the encoder of a codec satisfying both laws; the laws constrain the decoder relative to the encoder and nothing else.
  - The model has no byte layouts, lengths, state, or error reporting. Nothing here is a security property of an implemented parser.
  - Does not require listing Function.Injective c.enc on the right-hand side of lawful_iff_dec_eq_some_iff because injectivity is derivable from either side (decEnc_imp_enc_injective, decEqSomeIff_imp_enc_injective); a third equivalent formulation matching EverParse's 'correct and exact' is proved in Witnesses.lean as lawful_iff_decEnc_and_accepts_only_range.
  - Does not imply c.enc is surjective or c.dec is total, and does not guarantee unambiguous list concatenation when B = List β (see lawful_injective_nonEmpty_enc_admits_ambiguous_concat).
- **Card 3 (`lawful_iff_decEnc_and_decInj`):**
  - `EncDec c` implies `DecInj c` with no other hypothesis; only the converse needs `DecEnc c`. A decoder that is injective on accepted inputs and surjective does not make a codec with a given encoder satisfy either law (`shiftedBoolCodec`).
  - Does not show that DecInj c implies DecEnc c; alwaysFailBoolCodec satisfies DecInj vacuously while rejecting every input (encDec_imp_decInj is proved unconditionally in Witnesses.lean, whereas DecInj → EncDec fails on shiftedBoolCodec via decInj_and_surjective_dec_not_lawful).
- **Card 4 (`dec_unique_of_lawful`):**
  - Does not assert that a computable lawful decoder exists for an arbitrary injection without FiberSplit.
  - Does not assert uniqueness when only DecEnc holds (decoders may accept different non-canonical inputs) or when only EncDec holds (decoders may reject different valid encodings); by contrast, the dual encoder-uniqueness fact enc_unique_of_dec_eq (proved in Witnesses.lean) needs only DecEnc c₁ and EncDec c₂.
  - Does not assert algorithmic or complexity equivalence of the two decoders—only extensional function equality B → Option A.
- **Card 5 (`classicalCodec_bijection`):**
  - Does not produce an executable decoder; classicalDec uses Classical.propDecidable and Classical.choose (Classical.choice).
  - Does not imply DecEnc (classicalCodec f) when f is not injective (ce_classicalCodec_decEnc_drop_inj), nor does it recover single-law codecs from their encoder.
- **Card 6 (`codecOfFiberSplit_correspondence`):**
  - Does not construct, without Classical.choice, a FiberSplit f for an arbitrary injection f without a lawful decoder (classically every function f has one: fiberSplit_exists_for_every_function, via the noncomputable classicalFiberSplit f); rather, together with fiberSplitOfLawful (Defs.lean), it establishes that FiberSplit f (decidable fibers) is both necessary and sufficient constructive data for a lawful decoder.
  - Does not imply that FiberSplit f alone forces Function.Injective f or DecEnc; constUnitFiberSplit splits fibers for the non-injective constant map Bool → Unit.
- **Card 7 (`lawful_dec_isSome_iff_mem_range`):**
  - Says nothing about computability. In Lean, `classicalCodec f` satisfies both laws for every injective `f`, including encoders whose image is undecidable. The reading 'a computable lawful decoder yields a computable membership test for the image' is a modeling remark, not part of the statement.
  - Does not assert that Junk c is inhabited (for bijective codecs such as Codec.id, Junk c is empty), nor does it constrain the runtime complexity of evaluating (c.dec b).isSome.
- **Card 8 (`decEnc_admits_malleable_codec`):**
  - Does not show that `EncDec` has to be established by a separate argument for each codec. When the wire type has decidable equality, wrapping a `DecEnc` decoder with a re-encode-and-compare check (`dec' b := match dec b with | some a => if enc a = b then some a else none | none => none`) gives a codec with the same encoder that satisfies both laws.
  - The laws are stated for one encoder function. A format that permits several encodings of one value cannot satisfy `EncDec` for any single encoder; for such formats the corresponding requirement is that the decoder accepts exactly the strings the format relates to the decoded value. Failing `EncDec` for a chosen encoder is therefore not by itself evidence that malformed input is accepted.
  - Does not show that every DecEnc-only codec is malleable; lawful codecs satisfy DecEnc without malleability.
- **Card 9 (`encDec_admits_always_failing_codec`):**
  - Does not show that violating DecEnc forces total failure on every input; a partially failing decoder can accept some valid encodings and reject others while still satisfying EncDec.
  - Does not show that EncDec alone implies injectivity of enc (ce_decEnc_imp_enc_injective_drop_decEnc), nor that adding 'every encoding is accepted' without encoder injectivity rescues DecEnc (ce_codecOfFiberSplit_decEnc_drop_inj).
- **Card 10 (`canonicalize_decEnc_of_decEnc`):**
  - Does not eliminate the runtime cost of re-encoding and comparing wire representations on every decode call (unlike zero-copy parsers that prove EncDec directly on the parser).
  - Classically every type B has decidable equality (via Classical.propDecidable), so canonicalize applies to every wire type B in logic; a computable DecidableEq B instance is needed only to obtain an executable wrapper. Moreover, canonicalize cannot repair a codec that violates DecEnc (ce_canonicalize_decEnc_drop_decEnc).
- **Card 11 (`combinator_closure_decEnc_and_encDec`):**
  - For an untagged union of two codecs into a single shared wire type B, DecEnc under any decoder requires the two branch encoders to have disjoint images (untaggedSum_decEnc_imp_disjoint_images), and when both branches are lawful their left-biased untagged union untaggedSum c₁ c₂ is lawful if and only if ∀ a₁ a₂, c₁.enc a₁ ≠ c₂.enc a₂ (untaggedSum_lawful_iff_disjoint_images).
  - Codec.prod encodes into the structured pair type B₁ × B₂ rather than flat wire concatenation List β; for unseparated stream concatenation of two fields see FramedCodec.seq (framed_seq_closure) and lawful_injective_nonEmpty_enc_admits_ambiguous_concat.
  - Does not imply converse decomposition of laws from a composite codec back to its factors (for example, when c₁.enc is non-surjective in comp, when one factor domain is empty in prod_decEnc, or when one factor decoder always returns none in comp_encDec / prod_encDec).
- **Card 12 (`framed_lawful_iff_decPrefix_eq_some_iff`):**
  - A framed codec satisfying `PrefixDecEnc` (even when `PrefixEncDec` also holds) does not become a lawful whole-input codec by discarding the remainder: `firstOnly fc` (`xs ↦ (fc.decPrefix xs).map Prod.fst`) satisfies `DecEnc`, yet whenever `A` and the token type `β` are inhabited it violates both `DecInj` and `EncDec` (proved in general as `firstOnly_decEnc_and_not_decInj`, and instantiated on `varLenBoolFramedCodec` in `framed_lawful_but_firstOnly_not_decInj`). Converting `decPrefix` into a lawful whole-input decoder requires checking `rest = []`.
  - Does not imply NonEmptyEnc fc.enc; emptyUnitFramedCodec satisfies both PrefixDecEnc and PrefixEncDec on Unit while encoding () to [].
- **Card 13 (`prefixDecEnc_imp_prefixFree`):**
  - Does not show the converse, that a prefix-free encoder admits a prefix decoder satisfying `PrefixDecEnc`; that converse is neither stated nor proved in this package (not examined).
  - A framed codec satisfying `PrefixDecEnc` (even when `PrefixEncDec` also holds) does not become a lawful whole-input codec by discarding the remainder: `firstOnly fc` (`xs ↦ (fc.decPrefix xs).map Prod.fst`) satisfies `DecEnc`, yet whenever `A` and the token type `β` are inhabited it violates both `DecInj` and `EncDec` (proved in general as `firstOnly_decEnc_and_not_decInj`, and instantiated on `varLenBoolFramedCodec` in `framed_lawful_but_firstOnly_not_decInj`). Converting `decPrefix` into a lawful whole-input decoder requires checking `rest = []`.
  - PrefixFree fc.enc bundles Function.Injective fc.enc with set-level proper-prefix-freeness ImagePrefixFree fc.enc (proved in Witnesses.lean as prefixFree_iff_injective_and_imagePrefixFree; contrast const_imagePrefixFree_not_prefixFree in Counterexamples.lean and Mathlib InformationTheory.IsPrefixFree).
  - Does not imply NonEmptyEnc fc.enc on subsingleton types (emptyUnitFramedCodec), and does not claim PrefixFree is necessary for whole-list unique decodability (suffixEnc_not_prefixFree_yet_concat_lawful).
- **Card 14 (`framed_seq_closure`):**
  - Unlike uncounted variable-length listCodec, finite fixed-arity record sequencing fc₁.seq fc₂ does not require NonEmptyEnc (zero-width Unit fields compose cleanly in a fixed tuple).
  - Does not apply when fc₁ only satisfies whole-input DecEnc rather than PrefixDecEnc (see lawful_injective_nonEmpty_enc_admits_ambiguous_concat and Narcissus Section 3).
- **Card 15 (`listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc`):**
  - Under `PrefixDecEnc`, `NonEmptyEnc` can fail only if all values of `A` are equal (`prefixDecEnc_nil_codeword_imp_subsingleton`); for a type with two distinct values it is automatic (`nonEmptyEnc_of_prefixDecEnc_of_ne`).
  - Does not show that `PrefixDecEnc` is necessary for `DecEnc (listCodec fc)`: `lenientFc` violates `PrefixDecEnc` on arbitrary remainders yet satisfies `DecEnc (listCodec lenientFc)` because its prefix decoder succeeds whenever the remainder is itself a concatenation of codewords (`lenient_not_prefixDecEnc_yet_listCodec_decEnc`).
  - `listCodec fc` is a whole-input codec. Its encoder `encList fc.enc` is not prefix-free whenever `A` is inhabited (`encList_not_prefixFree`), so no framed codec with that encoder satisfies `PrefixDecEnc` (`no_prefixDecEnc_for_encList`). Consequently the package's sequencing theorem `seq_prefixDecEnc`, which assumes `PrefixDecEnc` for both fields, does not apply to a `FramedCodec.seq` record that has a list encoded this way as a field (for example as the first field, followed by further data), and `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` does not apply when the list elements are themselves such lists. The package therefore gives no general guarantee that such a layout decodes correctly, but this is not an impossibility result: in general such a layout needs extra framing (such as a length prefix or a terminator) or a separate argument that the following tokens cannot be read as list elements. `bareList_first_field_lawful` proves a lawful `seq` record whose first field is a bare `encList`-encoded list, with no length prefix or terminator, followed by a field whose codewords share no token with the element codewords. Nesting such lists directly inside another bare `encList`-encoded list does make the outer encoder non-injective (derived: for any `a : A`, `encList (encList enc)` maps both `[[a], [a]]` and `[[a, a]]` to `enc a ++ enc a`).
  - A framed codec satisfying `PrefixDecEnc` (even when `PrefixEncDec` also holds) does not become a lawful whole-input codec by discarding the remainder: `firstOnly fc` (`xs ↦ (fc.decPrefix xs).map Prod.fst`) satisfies `DecEnc`, yet whenever `A` and the token type `β` are inhabited it violates both `DecInj` and `EncDec` (proved in general as `firstOnly_decEnc_and_not_decInj`, and instantiated on `varLenBoolFramedCodec` in `framed_lawful_but_firstOnly_not_decInj`). Converting `decPrefix` into a lawful whole-input decoder requires checking `rest = []`.
  - Does not imply EncDec (listCodec fc) unless PrefixEncDec fc also holds (listCodec_encDec_of_prefixEncDec), and does not cover length-prefixed list formats, which transmit element counts explicitly and therefore permit zero-width Unit elements.
- **Card 16 (`listCodec_encDec_of_prefixEncDec`):**
  - `listCodec fc` is a whole-input codec. Its encoder `encList fc.enc` is not prefix-free whenever `A` is inhabited (`encList_not_prefixFree`), so no framed codec with that encoder satisfies `PrefixDecEnc` (`no_prefixDecEnc_for_encList`). Consequently the package's sequencing theorem `seq_prefixDecEnc`, which assumes `PrefixDecEnc` for both fields, does not apply to a `FramedCodec.seq` record that has a list encoded this way as a field (for example as the first field, followed by further data), and `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` does not apply when the list elements are themselves such lists. The package therefore gives no general guarantee that such a layout decodes correctly, but this is not an impossibility result: in general such a layout needs extra framing (such as a length prefix or a terminator) or a separate argument that the following tokens cannot be read as list elements. `bareList_first_field_lawful` proves a lawful `seq` record whose first field is a bare `encList`-encoded list, with no length prefix or terminator, followed by a field whose codewords share no token with the element codewords. Nesting such lists directly inside another bare `encList`-encoded list does make the outer encoder non-injective (derived: for any `a : A`, `encList (encList enc)` maps both `[[a], [a]]` and `[[a, a]]` to `enc a ++ enc a`).
  - A framed codec satisfying `PrefixDecEnc` (even when `PrefixEncDec` also holds) does not become a lawful whole-input codec by discarding the remainder: `firstOnly fc` (`xs ↦ (fc.decPrefix xs).map Prod.fst`) satisfies `DecEnc`, yet whenever `A` and the token type `β` are inhabited it violates both `DecInj` and `EncDec` (proved in general as `firstOnly_decEnc_and_not_decInj`, and instantiated on `varLenBoolFramedCodec` in `framed_lawful_but_firstOnly_not_decInj`). Converting `decPrefix` into a lawful whole-input decoder requires checking `rest = []`.
  - Does not imply DecEnc (listCodec fc) without PrefixDecEnc and NonEmptyEnc, and avoids needing NonEmptyEnc only because decList explicitly rejects non-progressing steps (rest.length ≥ xs.length; exercised by ex_decList_guard_rejects in Examples.lean).
- **Card 17 (`lawful_injective_nonEmpty_enc_admits_ambiguous_concat`):**
  - This is one instance, not a general implication: an injective encoding that is not prefix-free can still have injective concatenation (`false ↦ [false]`, `true ↦ [false, true]`).
  - Positive control suffixEnc_not_prefixFree_yet_concat_lawful (Counterexamples.lean) proves that suffixEnc (false ↦ [false], true ↦ [false, true]) violates PrefixFree yet has injective concatenation and a computable lawful (DecEnc ∧ EncDec) whole-list decoder decSuffixList.
  - Does not rule out length-prefixed or delimiter-framed list encodings over ambiguousCodec; ambiguity arises specifically from bare concatenation encList.
- **Card 18 (`decomp_isEquiv_iff_lawful`):**
  - Concerns only whether the canonical maps `decompToFun c` and `decompInvFun c` are mutual inverses: the bare existence of some equivalence `Equiv B (A ⊕ Junk c)` does not imply `EncDec c` or lawfulness. In particular, `nonCanonicalBoolCodec` violates `EncDec` (and its canonical maps fail `IsEquiv`), yet `nonCanonicalBoolJunkEquiv` constructs an explicit bijection `Equiv Nat (Bool ⊕ Junk nonCanonicalBoolCodec)` because `Junk nonCanonicalBoolCodec = { b : Nat // nonCanonicalBoolCodec.dec b = none }` (`b ≥ 3`) is countably infinite (`nonCanonicalBoolCodec_not_encDec_yet_admits_equiv`).
  - For a codec satisfying only one law the canonical maps are not mutually inverse: `LeftInv` holds exactly when `EncDec` does (`leftInv_decomp_iff_encDec`), `RightInv` exactly when `DecEnc` does (`rightInv_decomp_iff_decEnc`).
  - No statement about lenses is proved in this package. 'Dual to lenses' describes the shape of the result; the lens-side decomposition needs extra assumptions (for instance an inhabited view type).
  - Does not imply that Junk c is the unique type C with B ≃ A ⊕ C; any C related by an intertwining equivalence yields the same codec (codecOfSplit_eq_iff_exists_intertwining_equiv), while decompToFun c (c.enc a) = Sum.inl a follows directly from RightInv (decompToFun_enc_of_rightInv) and c.dec b = inlMatcher (decompToFun c b) holds unconditionally (dec_eq_inlMatcher_decompToFun).
- **Card 19 (`decomp_induces_lawful_and_complement`):**
  - No statement about lenses is proved in this package. 'Dual to lenses' describes the shape of the result; the lens-side decomposition needs extra assumptions (for instance an inhabited view type).
  - RightInv on Sum.inr is not required if one only wants DecEnc ∧ EncDec of codecOfSplit f g: LeftInv f g together with ∀ a, f (g (Sum.inl a)) = Sum.inl a already implies both DecEnc and EncDec for every f and g (codecOfSplit_lawful_of_leftInv_and_rightInv_inl), whereas RightInv on Sum.inr is specifically needed to identify C with Junk (codecOfSplit f g) (ce_decomp_induces_drop_rightInv_inr).
  - Distinct decompositions (C₁, f₁, g₁) and (C₂, f₂, g₂) need not produce distinct codecs (codecOfSplit_eq_iff_exists_intertwining_equiv).
- **Card 20 (`codecOfSplit_eq_iff_exists_intertwining_equiv`):**
  - Does not say that two decompositions induce the same codec whenever their complement types are equivalent. The equivalence must intertwine the decompositions: two decompositions of `Bool` as `Unit ⊕ Unit`, one with `enc () = false` and one with `enc () = true`, have the same complement and different codecs.
  - No statement about lenses is proved in this package. 'Dual to lenses' describes the shape of the result; the lens-side decomposition needs extra assumptions (for instance an inhabited view type).
  - In the reverse direction (intertwining ⇒ equal codecs), bijectivity of φ and hypotheses hl₁ and hr₂ are not needed: any intertwining function φ : C₁ → C₂ with hr₁ and hl₂ suffices (proved in Witnesses.lean as codecOfSplit_eq_of_intertwining_fun).

### Escape hatches

- **Upgrading `DecEnc` to `DecEnc ∧ EncDec` (defeating single-law malleability):**
  - *Proved in this package:* enforce `EncDec` directly, enforce whole-input `DecInj` alongside `DecEnc` (`lawful_iff_decEnc_and_decInj`), enforce image-only acceptance alongside `DecEnc` (`lawful_iff_decEnc_and_accepts_only_range`), or wrap the decoder with `canonicalize` (`canonicalize_decEnc_of_decEnc` + `canonicalize_encDec`, which applies classically to every wire type `B` and yields an executable wrapper whenever `B` has a computable `DecidableEq B` instance).
- **Defeating concatenation ambiguity (`lawful_injective_nonEmpty_enc_admits_ambiguous_concat`):**
  - *Proved in this package:* require a framed prefix decoder satisfying `PrefixDecEnc` together with `NonEmptyEnc` (`listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc`, where `NonEmptyEnc` is automatic on non-subsingleton domains via `nonEmptyEnc_of_prefixDecEnc_of_ne`), or use a non-prefix-free uniquely decodable code with lookahead (`suffixEnc_not_prefixFree_yet_concat_lawful`).
  - *Not proved in this package:* fixed-width codewords, explicit length-prefixed framing, or delimiter-terminated list encodings.
- **Bypassing whole-input non-composability of `listCodec`:**
  - *Proved in this package:* fixed-arity heterogeneous tuples compose directly via `FramedCodec.seq` (`seq_prefixDecEnc`, `seq_prefixEncDec`) without `NonEmptyEnc`.
  - *Not proved in this package:* framing variable-length lists with an explicit element count or sentinel terminator so they can be followed by further fields or nested inside outer lists.

### Tightness coverage and structural dependencies

- **Hypotheses with `unknown` tightness:** None. Every hypothesis across all 20 cards (including the arguments `hde` and `hed` of the hashed companion definition `fiberSplitOfLawful`) is either `tight` with a proved Lean counterexample or `harmless` with justification.
- **`harmless` hypotheses:** `[DecidableEq B]` in `canonicalize_decEnc_of_decEnc` and `canonicalize_encDec` (Card 10) is `harmless` for logical applicability because every type classically has decidable equality (`Classical.propDecidable`), so no logical counterexample without `[DecidableEq B]` exists; a computable instance is needed only for an executable wrapper. The arguments `hde` and `hed` of the hashed companion definition `fiberSplitOfLawful` (Card 6) are `harmless` for the same kind of reason: they are used only by its choice-free construction (`hde` in the `none` branch, `hed` in the `some` branch), while classically every function has a `FiberSplit` (`fiberSplit_exists_for_every_function`, axioms `[propext, Classical.choice, Quot.sound]`), so no counterexample to the existence of `FiberSplit c.enc` without either argument can exist.
- **Structural term dependencies (surrogate counterexamples):** In `complementEquivOfCodecEq_intertwines` (Card 20), all five proof hypotheses (`hl₁`, `hr₁`, `hl₂`, `hr₂`, and `heq : codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂`) occur inside the conclusion's term `complementEquivOfCodecEq f₁ g₁ f₂ g₂ hl₁ hr₁ hl₂ hr₂ heq`, so a literal 'drop the hypothesis, keep the rest, negate the conclusion' statement cannot be typed for any of the five. Each is paired with a surrogate counterexample: `ce_codecOfSplit_eq_iff_drop_hl1`, `ce_codecOfSplit_eq_iff_drop_hr1`, `ce_codecOfSplit_eq_iff_drop_hl2`, and `ce_codecOfSplit_eq_iff_drop_hr2` each export, for one concrete instance, exactly the remaining three inverse laws and the negation `¬ (codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂ ↔ ∃ φ : Equiv C₁ C₂, ∀ b, f₂ b = Sum.map id φ.toFun (f₁ b))` of the iff in `codecOfSplit_eq_iff_exists_intertwining_equiv`; they do not export `heq` or the emptiness of `Equiv C₁ C₂` as separate conclusions (both are established only inside their proofs); and `ce_intertwines_drop_heq` exports, for one concrete instance, the four inverse laws and the non-existence of any candidate function `φ : C₁ → C₂` intertwining `f₁` and `f₂`, while `same_complement_different_codec` exports `codecOfSplit f₁ g₁ ≠ codecOfSplit f₂ g₂` for the same instance.

### Disproved or dropped statements

None. Every theorem statement in the package was proved as stated without weakening or dropping any result.

### Not examined

- **Converse of `prefixDecEnc_imp_prefixFree`:** Whether every `PrefixFree` encoder admits a `PrefixDecEnc` decoder (classically or constructively) is not stated or proved in this package.
- **General unique-decodability criteria:** Necessary and sufficient tests such as Sardinas–Patterson and inequalities such as Kraft–McMillan are not formalized (only the concrete positive control `suffixEnc_not_prefixFree_yet_concat_lawful`).
- **Relational formats:** Formats permitting multiple valid representations per value (as in Narcissus Definition 2.2) are contrasted in Applicability and Boundaries but not formalized.
- **Length-prefixed, delimiter-framed, and fixed-width list codecs:** Mentioned only as unproved escape hatches.
- **Polymorphic optics and constant-complement lenses:** Polymorphic `Prism s t a b` (`s ≠ t` or `a ≠ b`) and lens decompositions `B ≃ A × C` (which require extra hypotheses such as an inhabited view type; Riley Proposition 4.1.3) are outside this package.
- **Concrete parser implementations:** Byte layouts, memory safety, streaming I/O, state, error diagnostics, and runtime complexity are outside the model.

## Evidence

**Kernel check.** Built on 2026-11-20 with Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`, core Lean / `Std` only, no Mathlib). `lake build` of `lean/` succeeds with zero errors and zero warnings; static token checks confirm no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `@[extern]`, `unsafe`, `debug.skipKernelTC`, `#exit`, or `Lean.ofReduce*`. `Lean.collectAxioms` audited all 481 non-internal declarations in `Toy.*` and confirmed every declaration uses at most `{propext, Classical.choice, Quot.sound}`; full per-declaration axiom lists are stored in `audit/axioms.json`.

### Proof-level axiom qualifiers verified

The following table directly verifies every 'without `Classical.choice`' and 'zero axioms' qualifier stated in the result cards (from `audit/axioms.json`):

| Declaration | Card | Verified axioms (`audit/axioms.json`) | `Classical.choice` absent? |
| :--- | :--- | :--- | :--- |
| `Toy.Codec.dec_unique_of_lawful` | Card 4 | Quot.sound | yes |
| `Toy.Codec.codecOfFiberSplit_decEnc_of_injective` | Card 6 | none | yes |
| `Toy.Codec.codecOfFiberSplit_encDec` | Card 6 | none | yes |
| `Toy.Codec.fiberSplitOfLawful` | Card 6 (def) | none | yes |
| `Toy.Codec.codecOfFiberSplit_eq_of_lawful` | Card 6 | Quot.sound | yes |
| `Toy.Codec.lawful_dec_isSome_iff_mem_range` | Card 7 | none | yes |
| `Toy.Codec.junk_iff_not_in_image_of_lawful` | Card 7 | none | yes |
| `Toy.Codec.canonicalize_encDec` | Card 10 | none | yes |
| `Toy.Codec.leftInv_decomp_iff_encDec` | Card 18 | none | yes |
| `Toy.Codec.rightInv_decomp_iff_decEnc` | Card 18 | none | yes |
| `Toy.Codec.decomp_isEquiv_iff_lawful` | Card 18 | none | yes |
| `Toy.Codec.nonCanonicalBoolCodec_not_encDec_yet_admits_equiv` | Card 18 (companion) | propext | yes |
| `Toy.Codec.decomp_induces_lawful_and_complement` | Card 19 | none | yes |
| `Toy.Codec.complementEquivOfCodecEq` | Card 20 (def) | none | yes |
| `Toy.Codec.complementEquivOfCodecEq_intertwines` | Card 20 | none | yes |
| `Toy.Codec.codecOfSplit_eq_iff_exists_intertwining_equiv` | Card 20 | Quot.sound | yes |
| `Toy.Codec.ex_decList_guard_rejects` | Examples (`decList` guard) | Quot.sound, propext | yes |

### Statement, closure hash, and axiom record (`audit/statements.json` & `audit/axioms.json`)

**Exact specification of `statement_sha256`, `closure_sha256`, and `closure_size` (implemented verbatim in `support/revalidate.py`).** Every Lean declaration `n` referenced in `results.json` across `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample` fields (116 declarations in total) is hashed in the compiled Lean `Environment` `env` as follows:

1. **Package-constant membership (`inPkg env c`):** A constant `c : Lean.Name` belongs to this package if `env.getModuleIdxFor? c = some idx` and the library root `` `Toy `` (from `[[lean_lib]]` in `lean/lakefile.toml`) is a prefix of `env.header.moduleNames[idx.toNat]!` (excluding core Lean / `Std` constants).
2. **Statement hash (`statement_sha256`):** Look up `ci ← env.find? n`, serialize its elaborated kernel `Expr` type via `toString (repr ci.type)` (UTF-8, no trailing newline), and compute its hexadecimal SHA-256 digest.
3. **Definition closure (`closure`, `closure_size`, `closure_sha256`):** Starting from the seed worklist `ci.type.getUsedConstants.toList` (the constants directly occurring in `n`'s statement type; `n`'s own proof/value body is not seeded), transitively collect every reachable package constant `c` (`inPkg env c = true`) into a `NameSet` by expanding each newly visited constant `cc` with:
   - `cc.type.getUsedConstants.toList` (all constants in `cc`'s type),
   - `v.getUsedConstants.toList` when `cc.isTheorem = false` and `cc.value? (allowOpaque := true) = some v` (**theorem proof bodies are excluded**: when `cc.isTheorem = true`, `cc`'s proof term is ignored), and
   - `iv.ctors` when `cc` is `.inductInfo iv` (inductive and `structure` constructors).
   Format each constant `c` in the resulting `NameSet` as `c.toString ++ " : " ++ toString (repr cc.type)` when `cc.isTheorem = true` or `cc.value? (allowOpaque := true) = none`, and as `c.toString ++ " : " ++ toString (repr cc.type) ++ " := " ++ toString (repr v)` when `cc.isTheorem = false` and `cc.value? (allowOpaque := true) = some v`. Sort the resulting strings in ascending lexicographic order (`Array.qsort (· < ·)`), record the array length as `closure_size`, join the sorted strings with `"\n"`, UTF-8 encode, and compute the hexadecimal SHA-256 digest as `closure_sha256`.

| Lean name | Used by | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Codec.canonicalize_decEnc_of_decEnc` | `canonicalize_decEnc_of_decEnc` result | propext | `a61f979c29449f84b80339b8e6a50a19c09eafb46ea05aab547617f76d9769a7` | `ccd171d74c950af524da18a7cc61ccf3001e79f5eb68a9f4b687055602d7e901` (7) |
| `Toy.Codec.canonicalize_encDec` | `canonicalize_decEnc_of_decEnc` cited companion | none | `1cd129a7bddbb40604ca3208c2bb4cbbad39eed755904148e08f9a20d26d5b65` | `1584eaf2dd875733a52a4923890714d5edb4fa727fccfa0045ef806db49b2784` (7) |
| `Toy.Codec.ce_canonicalize_decEnc_drop_decEnc` | `canonicalize_decEnc_of_decEnc` counterexample (`hde (in canonicalize_decEnc_of_decEnc)`) | none | `d0d06174dfce5a08d5e05e76a8b36822190a8c2003ef2c26d6e3f40b3be5014f` | `75dfd7d7b79648402dbfd0c0a6fee81d10158e4eb657254245dc183b3357b43d` (9) |
| `Toy.Codec.ce_classicalCodec_decEnc_drop_inj` | `classicalCodec_bijection` counterexample (`hf (in classicalCodec_decEnc_of_injective)`) | Classical.choice, Quot.sound, propext | `582dea6632362b74167207e30d4355a1b4e46dc43955de37df32db64b74d1941` | `85e32c638ed79ff9f902e5ea6d0c2138e396a7289e44c8cf46fa2bb2b2b22514` (7) |
| `Toy.Codec.ce_classicalCodec_recover_drop_decEnc` | `classicalCodec_bijection` counterexample (`hde (in classicalCodec_recover_of_lawful)`) | Classical.choice, Quot.sound, propext | `a05fd293bd6cb43443a67c905e0b69a744949b9a18ef7098ab3453644a36003a` | `16f8df8cfe95e1bc05d5082c9930ea4a6ba8a3ab8304b7cd3007904a34026c47` (8) |
| `Toy.Codec.ce_classicalCodec_recover_drop_encDec` | `classicalCodec_bijection` counterexample (`hed (in classicalCodec_recover_of_lawful)`) | Classical.choice, Quot.sound, propext | `c734503278220e992b81e595054ceb54350b96d544eb9bc119fd1ee67b6a89ae` | `495284ae407eb8eb6bc9713d894aa08284548e2ec9e4a441b5c6fbf506019bb8` (10) |
| `Toy.Codec.ce_codecOfFiberSplit_decEnc_drop_inj` | `codecOfFiberSplit_correspondence` counterexample (`hf (in codecOfFiberSplit_decEnc_of_injective)`) | none | `8c9553f247ad735427b9f32a5d93a190ff6ca55d6f8ff3ce150d88b77afa2dae` | `98e4664487fb924d1aa34758b5c988d9c4b013dd166aa3aafe62ae0433dfb30e` (12) |
| `Toy.Codec.ce_codecOfFiberSplit_eq_drop_decEnc` | `codecOfFiberSplit_correspondence` counterexample (`hde (in codecOfFiberSplit_eq_of_lawful)`) | none | `8f2814ef54779cbeed6bc6506e6ea53414d8221f0d218416661cb1b259e19383` | `cf9728e5d0fc2a77d4ec08e04fc416ac8f925ad5d051079657de6e2ecc07b90e` (11) |
| `Toy.Codec.ce_codecOfFiberSplit_eq_drop_encDec` | `codecOfFiberSplit_correspondence` counterexample (`hed (in codecOfFiberSplit_eq_of_lawful)`) | propext | `8d25fbfc16ffb955da0866e60311ff20800421b1de21264aeaa8e08bb83498fd` | `6429cb596a788b2bb2e87bb9f46aa575ec446b87a808109fffbd685692c89741` (16) |
| `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hl1` | `codecOfSplit_eq_iff_exists_intertwining_equiv` counterexample (`hl₁ (in codecOfSplit_eq_iff_exists_intertwining_equiv)`); `codecOfSplit_eq_iff_exists_intertwining_equiv` counterexample (`hl₁ (in complementEquivOfCodecEq_intertwines)`) | Quot.sound | `1b367bd4bcb8f8c67a5afc5c84420790fb9452ed7bd693d8c709d83818ce5ba0` | `b3cc8de8db24b16794669c5a01a66f243753125f19fab6b5dab12d06d13bdd9c` (16) |
| `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hl2` | `codecOfSplit_eq_iff_exists_intertwining_equiv` counterexample (`hl₂ (in codecOfSplit_eq_iff_exists_intertwining_equiv)`); `codecOfSplit_eq_iff_exists_intertwining_equiv` counterexample (`hl₂ (in complementEquivOfCodecEq_intertwines)`) | Quot.sound | `7639d18c19b6d2def14f8a198c17c173d884249525bb90388dcb615c94f93c89` | `b3cc8de8db24b16794669c5a01a66f243753125f19fab6b5dab12d06d13bdd9c` (16) |
| `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hr1` | `codecOfSplit_eq_iff_exists_intertwining_equiv` counterexample (`hr₁ (in codecOfSplit_eq_iff_exists_intertwining_equiv)`); `codecOfSplit_eq_iff_exists_intertwining_equiv` counterexample (`hr₁ (in complementEquivOfCodecEq_intertwines)`) | Quot.sound | `be1f9892cc9ed0751a344f1cbcb0f2c04d1c0a9839a76135e72a5f6369658c72` | `05e2961518f4cf386aa9249843271cd99beda82aea76928b653b0439eda4a1d2` (15) |
| `Toy.Codec.ce_codecOfSplit_eq_iff_drop_hr2` | `codecOfSplit_eq_iff_exists_intertwining_equiv` counterexample (`hr₂ (in codecOfSplit_eq_iff_exists_intertwining_equiv)`); `codecOfSplit_eq_iff_exists_intertwining_equiv` counterexample (`hr₂ (in complementEquivOfCodecEq_intertwines)`) | Quot.sound | `f8d5c28499050c06b56ec2b1348899338a055285b7808dfc7caa6b8a0864f480` | `05e2961518f4cf386aa9249843271cd99beda82aea76928b653b0439eda4a1d2` (15) |
| `Toy.Codec.ce_comp_decEnc_drop_hde1` | `combinator_closure_decEnc_and_encDec` counterexample (`comp_decEnc.hde₁`) | none | `00b87cc0a377c515e5de387ab94003cfdec6d9a3144977ea163f7c1c0ef7338e` | `dd83a4469b493597ac72c4c78981bc1e2d48674bd66a1993f013e2db57b565d8` (9) |
| `Toy.Codec.ce_comp_decEnc_drop_hde2` | `combinator_closure_decEnc_and_encDec` counterexample (`comp_decEnc.hde₂`) | none | `7211c4d34fb09184efe671e9ed6a2e58d5bdcd5e2c363a603370b06cb56570b7` | `dd83a4469b493597ac72c4c78981bc1e2d48674bd66a1993f013e2db57b565d8` (9) |
| `Toy.Codec.ce_comp_encDec_drop_hed1` | `combinator_closure_decEnc_and_encDec` counterexample (`comp_encDec.hed₁`) | propext | `ce064beae85f0588e8e589dbc0f71d78798f06b7f2509bf4f8fb69d8c88509f7` | `b2ec673ac931d86c1bb400478b7446ba9e4755b13ff26dd1c651243e360e0723` (11) |
| `Toy.Codec.ce_comp_encDec_drop_hed2` | `combinator_closure_decEnc_and_encDec` counterexample (`comp_encDec.hed₂`) | propext | `cfca9aa6d9eb5c9c308ed405631d299bbc43ece545cbafced7976fee9c089980` | `b2ec673ac931d86c1bb400478b7446ba9e4755b13ff26dd1c651243e360e0723` (11) |
| `Toy.Codec.ce_decEnc_imp_enc_injective_drop_decEnc` | `decEnc_imp_enc_injective` counterexample (`hde`) | none | `c1ec00483202a5ba2a904e9ced2225aa52bd4f906d48d879abe0e1959050e7d9` | `4a14cf9778972c4eeb9bfde95ffa596bf88cca195dc221f042b14cc47219f43e` (6) |
| `Toy.Codec.ce_decEqSomeIff_imp_enc_injective_drop_hconv` | `lawful_iff_dec_eq_some_iff` counterexample (`hconv (in decEqSomeIff_imp_enc_injective)`) | none | `6a29716aad90e50d2298846f0c725943c143c94590e062af611771560956944f` | `4a14cf9778972c4eeb9bfde95ffa596bf88cca195dc221f042b14cc47219f43e` (6) |
| `Toy.Codec.ce_dec_unique_drop_hde1` | `dec_unique_of_lawful` counterexample (`hde₁`) | none | `8e108ae64e9304e9831903cab264587dd3e1c83beceed4bebe41429a6f398512` | `99a1365233214033e1a97bb3cd412fa1ee564e483d66c181e29e86da725c1aa5` (8) |
| `Toy.Codec.ce_dec_unique_drop_hde2` | `dec_unique_of_lawful` counterexample (`hde₂`) | none | `459f09973d5fcd63266e7e0b9da01e83ff15699317686896a097baea732cf92d` | `99a1365233214033e1a97bb3cd412fa1ee564e483d66c181e29e86da725c1aa5` (8) |
| `Toy.Codec.ce_dec_unique_drop_hed1` | `dec_unique_of_lawful` counterexample (`hed₁`) | Quot.sound | `5951bc74c4bd411feaac89fc5435074d014c92d71a27952da3c70c311dc162c7` | `1c661a634e5df6adcc4db56bad72f108a554e4cc4fb0f6807e10581dd6d67213` (11) |
| `Toy.Codec.ce_dec_unique_drop_hed2` | `dec_unique_of_lawful` counterexample (`hed₂`) | Quot.sound | `d13ba74180431205be5d62f8edbc011469abecf5016eda77e7997a2fbf35b778` | `1c661a634e5df6adcc4db56bad72f108a554e4cc4fb0f6807e10581dd6d67213` (11) |
| `Toy.Codec.ce_dec_unique_drop_henc` | `dec_unique_of_lawful` counterexample (`henc`) | none | `2e00eaa2812f205111f051e8fc0e90095cc10f6369517dfcb3339adae3e623dc` | `4d0a250a42a04ca668b1ea0e986b2c8a94178e5e8125c0855b35257467a7e9cd` (8) |
| `Toy.Codec.ce_decomp_induces_drop_leftInv` | `decomp_induces_lawful_and_complement` counterexample (`hl`) | none | `847f85e3777d50995e86ff814d5921fa2071b85fa6f7e07ed129c152414a447b` | `92f50bd13dd61aa081b378369be48fca5415ae20f329725b44df6d36b8654450` (20) |
| `Toy.Codec.ce_decomp_induces_drop_rightInv` | `decomp_induces_lawful_and_complement` counterexample (`hr`) | none | `7351a2a22dd7f76599e7d08c7e2d007c1acc0881a85cd050c7077f0aee17f2e8` | `8b91dae1462b4ac42176ebc7ece98d8e2ddef62dacb7edf79c79053a8aaeb374` (19) |
| `Toy.Codec.ce_intertwines_drop_heq` | `codecOfSplit_eq_iff_exists_intertwining_equiv` counterexample (`heq (in complementEquivOfCodecEq_intertwines)`) | none | `8efab3e1be8fedd197726ec31c21c750e393d577277a4e3cc0386d67b4a477d4` | `298ea2d1a1f6998888fcd5fd09dcd4ef31602e7f58b4165efad87ebd000bc502` (9) |
| `Toy.Codec.ce_junk_iff_not_in_image_of_lawful_drop_decEnc` | `lawful_dec_isSome_iff_mem_range` counterexample (`hde (in lawful_dec_isSome_iff_mem_range and junk_iff_not_in_image_of_lawful)`) | none | `a21b2693b4450084c4129cffe17a1aedf217e307fd8a4f7d18b4e7988b4568d3` | `f9683279ebbfed7ebf9c68fd0994bc6a65b29673997804c56135bcdfe70b9266` (6) |
| `Toy.Codec.ce_junk_iff_not_in_image_of_lawful_drop_encDec` | `lawful_dec_isSome_iff_mem_range` counterexample (`hed (in lawful_dec_isSome_iff_mem_range and junk_iff_not_in_image_of_lawful)`) | propext | `7e077a63be2afcc89eca6fcf2e0d222ab1c1a94b3d7ffe6ba68ff6679470e93f` | `0c469de78608f2fea6ef3645dab02d5661c42942ffd8a31add8839aedc83b4fb` (8) |
| `Toy.Codec.ce_lawful_dec_isSome_drop_decEnc` | `lawful_dec_isSome_iff_mem_range` counterexample (`hde (in lawful_dec_isSome_iff_mem_range and junk_iff_not_in_image_of_lawful)`) | none | `83e07534194a7fb60ae523140a28831a9b1547b9e6a0b6ab02e14778e5140361` | `f9683279ebbfed7ebf9c68fd0994bc6a65b29673997804c56135bcdfe70b9266` (6) |
| `Toy.Codec.ce_lawful_dec_isSome_drop_encDec` | `lawful_dec_isSome_iff_mem_range` counterexample (`hed (in lawful_dec_isSome_iff_mem_range and junk_iff_not_in_image_of_lawful)`) | propext | `544499bbfdd806fe1866d52eeeab312bc8d5763f886dbd8ac6ac92e7c0fcdfa5` | `0c469de78608f2fea6ef3645dab02d5661c42942ffd8a31add8839aedc83b4fb` (8) |
| `Toy.Codec.ce_listCodec_decEnc_drop_nonEmptyEnc` | `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` counterexample (`hxy (in nonEmptyEnc_of_prefixDecEnc_of_ne)`) | Quot.sound, propext | `233dc119355d6521f1e4313fcd1db330bb4e652620346208af044e1c2d3a6d8d` | `b3ec0e8757404c40ee7d9ecfa501eb09ede9e5ca0725ba01f01fd2fe0ed1167b` (21) |
| `Toy.Codec.ce_listCodec_decEnc_iff_drop_prefixDecEnc` | `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` counterexample (`hpde (in listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc)`) | Quot.sound, propext | `216912e94d2c88a35db97f7dfddf431a307894aecacae211ce3a72cc3786b274` | `0720f53019eddb4e88a61b9400c464ffbff4cc599999aab7dcfbbd76cc8ca71b` (19) |
| `Toy.Codec.ce_listCodec_encDec_drop_prefixEncDec` | `listCodec_encDec_of_prefixEncDec` counterexample (`hped`) | Quot.sound, propext | `e2209cf181a597f340c8ffd0046011e10f9b4710a719984944d5a72df3f819ad` | `4ea21e8bdda8685b7acfb9cf53388d0f909cd3bc33980df79bc05973350dc442` (20) |
| `Toy.Codec.ce_nonEmptyEnc_of_prefixDecEnc_of_ne_drop_hpde` | `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` counterexample (`hpde (in nonEmptyEnc_of_prefixDecEnc_of_ne)`) | none | `ba0007912c74b14197a976a147346f7dc6a7aef1f4ba070eb586281583a0dea1` | `d62eff35c4338bf48b6842dd341e9eae061f3416d36257665ce5b5a80af34013` (8) |
| `Toy.Codec.ce_prefixDecEnc_imp_prefixFree_drop_hpde` | `prefixDecEnc_imp_prefixFree` counterexample (`hpde`) | none | `983cb35a9418a4e82165117ee157dfeecd30e43ff5831cc51f72d667ed858f25` | `9a041ffc4519276ca70f8f5b26748f8ed7caac1938c84cb06792e8ad56cfe3cf` (10) |
| `Toy.Codec.ce_prod_decEnc_drop_hde1` | `combinator_closure_decEnc_and_encDec` counterexample (`prod_decEnc.hde₁`) | propext | `a1b602b043686f119c65bfe8ae18d60cbf014a99d5f288907b0ab0b1296aa8e0` | `db210cfe4ff6be84bdbcee899751945214da7f217d559a62b09156b3615559e7` (11) |
| `Toy.Codec.ce_prod_decEnc_drop_hde2` | `combinator_closure_decEnc_and_encDec` counterexample (`prod_decEnc.hde₂`) | propext | `38728a0a83e6e007fd3d42ad7af239496ed6b33cf49c5a855db68a7f0c34371c` | `db210cfe4ff6be84bdbcee899751945214da7f217d559a62b09156b3615559e7` (11) |
| `Toy.Codec.ce_prod_encDec_drop_hed1` | `combinator_closure_decEnc_and_encDec` counterexample (`prod_encDec.hed₁`) | propext | `e0b60e46fc877a2b37e60b47d448eb35344327abbf80d30a7c91c3dcbdaaec44` | `d613078c1477d5db1a7b3a29a393e2f20ea6c311b1978cbbd429fad7457723ab` (13) |
| `Toy.Codec.ce_prod_encDec_drop_hed2` | `combinator_closure_decEnc_and_encDec` counterexample (`prod_encDec.hed₂`) | propext | `38223cdea88c5ea3e23f09fa9b3d17a6c3b1e6fa03123beff2cf4ea994b443cb` | `d613078c1477d5db1a7b3a29a393e2f20ea6c311b1978cbbd429fad7457723ab` (13) |
| `Toy.Codec.ce_seq_prefixDecEnc_drop_h1` | `framed_seq_closure` counterexample (`seq_prefixDecEnc.hpde₁`) | propext | `cae9347c0a75c12e771b6d60a0f27ecdd48a7290c6d5a02938824407024f863d` | `b1f5ecd4ec902115b082b5f6e3cd5105506d01458cf56f19ef50ddd9d0c0d21f` (14) |
| `Toy.Codec.ce_seq_prefixDecEnc_drop_h2` | `framed_seq_closure` counterexample (`seq_prefixDecEnc.hpde₂`) | propext | `32f994d3c85aa8d9191619569454623b59b23b8e2142920450593396a0ce8700` | `b1f5ecd4ec902115b082b5f6e3cd5105506d01458cf56f19ef50ddd9d0c0d21f` (14) |
| `Toy.Codec.ce_seq_prefixEncDec_drop_h1` | `framed_seq_closure` counterexample (`seq_prefixEncDec.hped₁`) | propext | `2bd11343cb9d892f48a1aed89cfabc0ac3503db565eb866c49bb6bf8d06e63a5` | `3ee6568ab6745d69787ee6a3f48231906f9abd2999e19f8f4444334aea9184c2` (15) |
| `Toy.Codec.ce_seq_prefixEncDec_drop_h2` | `framed_seq_closure` counterexample (`seq_prefixEncDec.hped₂`) | propext | `ff0ec32706c37ac2f112d343931fd3ecb629470ba1d3c38a6ca6fa783ddeff8f` | `3ee6568ab6745d69787ee6a3f48231906f9abd2999e19f8f4444334aea9184c2` (15) |
| `Toy.Codec.ce_sum_decEnc_drop_hde1` | `combinator_closure_decEnc_and_encDec` counterexample (`sum_decEnc.hde₁`) | none | `59542d0652796cb8c1e2195bd93af2f8a6a1c85ef97315d9056ae402db71e9fa` | `a11ad583cbf5acaf20989e7c19de60a4f675309f334eb3c5bd451bdd421bc028` (10) |
| `Toy.Codec.ce_sum_decEnc_drop_hde2` | `combinator_closure_decEnc_and_encDec` counterexample (`sum_decEnc.hde₂`) | none | `f8784bbe5401e25b0a9d4918a69108f6894218be2e75b78f1be963de67620b3b` | `a11ad583cbf5acaf20989e7c19de60a4f675309f334eb3c5bd451bdd421bc028` (10) |
| `Toy.Codec.ce_sum_encDec_drop_hed1` | `combinator_closure_decEnc_and_encDec` counterexample (`sum_encDec.hed₁`) | propext | `34eb723d8302436db3682c71bc82b2e9de7df55fcdee72eecb65d3ad15de7c82` | `ba7d385ad9272827d8d9fff0e82a0dfd1e097c42e0337ac400bef1d60f096e5a` (12) |
| `Toy.Codec.ce_sum_encDec_drop_hed2` | `combinator_closure_decEnc_and_encDec` counterexample (`sum_encDec.hed₂`) | propext | `e6412e4d35c5026ee0aaea40f973516066bea34e7456e9bf4a4f54089d7c43a8` | `ba7d385ad9272827d8d9fff0e82a0dfd1e097c42e0337ac400bef1d60f096e5a` (12) |
| `Toy.Codec.classicalCodec_decEnc_of_injective` | `classicalCodec_bijection` result | Classical.choice, Quot.sound, propext | `7e08916da4c332433f21b42b79348a3df658c1af17c69515d55ea92327e51a1e` | `85e32c638ed79ff9f902e5ea6d0c2138e396a7289e44c8cf46fa2bb2b2b22514` (7) |
| `Toy.Codec.classicalCodec_enc` | `classicalCodec_bijection` cited companion | Classical.choice, Quot.sound, propext | `71dba397279c9b2578a4e8441f6bf1b4b8dc1c20f350785874f68608cdb73cd8` | `05414d0c67301a1889f2abefcd761c0e07542e0a40d8b08b32d6236a010ce739` (5) |
| `Toy.Codec.classicalCodec_encDec` | `classicalCodec_bijection` result | Classical.choice, Quot.sound, propext | `924aea504a619e4a8680bbedbc89210d41ca12a90cf5e3a075e5e523e40948f6` | `3918397fed620808c116e3a989fe35d08d82c039b70d91f7406a13c2847fdb4e` (7) |
| `Toy.Codec.classicalCodec_recover_of_lawful` | `classicalCodec_bijection` result | Classical.choice, Quot.sound, propext | `edaede2b9397b2fc740cd8fac503686c7726809b9367d268c30d47ab19df9cfa` | `aa8b29352d4a265a5937b430b2f8cb30662c7e391e07e48378ac43d305306e70` (8) |
| `Toy.Codec.codecOfFiberSplit_decEnc_of_injective` | `codecOfFiberSplit_correspondence` result | none | `d16aef36e99844fe96b6bf0b5c1cab62900b9675be8804c408f6c58bbf00c9a7` | `0794320d87531c9c050c0cdc3ed0f0201eac9869b5ed19ba023fbdf578ceb010` (8) |
| `Toy.Codec.codecOfFiberSplit_encDec` | `codecOfFiberSplit_correspondence` cited companion | none | `10f10f5cced69e742bbcb111772e87e05e4e69cf86dc438b76acee581d8ec0df` | `4d7f2edb6ef8328a878cf99d7f059516e317c15676b31acda2dd84354852a432` (8) |
| `Toy.Codec.codecOfFiberSplit_eq_of_lawful` | `codecOfFiberSplit_correspondence` result | Quot.sound | `19d037f106aeb8cb9e6f0a6e32bb7767d75a657bce5822316300e35d6f0b215e` | `1c04fa14913ec716022ec59992f190fc4bb3c6feb1ed9abc268fccc8521a92bf` (9) |
| `Toy.Codec.codecOfSplit_eq_iff_exists_intertwining_equiv` | `codecOfSplit_eq_iff_exists_intertwining_equiv` result | Quot.sound | `ded4eb8516a9d787a777e2692f622c7721600ff590a2af2600611b717c1436ad` | `91f2b7e08e852d094db4042ae40c0d85b68aeb8c47941c8bbfa4f601df34ba0c` (10) |
| `Toy.Codec.comp_decEnc` | `combinator_closure_decEnc_and_encDec` result | none | `ec39b42f175f7800dd6b1aaa2318f4fb94ee7c584704d884e43c1dd765ca8a90` | `b92a17732d2e656319600e93d46850052b9e4f9e3ac801b7fc03e69888a0e379` (6) |
| `Toy.Codec.comp_encDec` | `combinator_closure_decEnc_and_encDec` result | none | `092adfcff3c9fefd3e3fbf6cecc2f7acb6b5a213a0e7104c382a85c458641dbf` | `033cfb0a3e872f380a7bf263b8a6aad737cf0daa94d00aa51b823dbe316ad81e` (6) |
| `Toy.Codec.complementEquivOfCodecEq_intertwines` | `codecOfSplit_eq_iff_exists_intertwining_equiv` result | none | `d0261e2551b5b6564de014d162a26a9a6fb6590da4cb2b714ceef4c3d64b87d0` | `92d719a911d4fc7e0aa4fbb7d43eb36772b6b58b7d498da2aacc5da165ddf625` (24) |
| `Toy.Codec.decEnc_admits_malleable_codec` | `decEnc_admits_malleable_codec` result; `decEnc_admits_malleable_codec` non-vacuity | propext | `697d680a141b48f97a21355fd75895b2a996184c8effd010c131bd200a73b829` | `d93e172a1b0f77b73f33cf5dd98d7b90954a16df70cb2881022fb19145e199cf` (10) |
| `Toy.Codec.decEnc_imp_enc_injective` | `decEnc_imp_enc_injective` result | none | `2e4ea935b0055b80d4625c22e5ac36564ade5cf4fc37a49f0e865dd9803829d2` | `91015e1869a4596a0917843276762f7bf12ea671547f19c4b125bcd4386b8c4a` (5) |
| `Toy.Codec.decEqSomeIff_imp_enc_injective` | `lawful_iff_dec_eq_some_iff` result | none | `675754ad5fcc4d33c9431faf70296d707f68ccf15dfde3f4947846b815b1378b` | `3e05ec2beb8cc818d99a0083d98a77f4a050b70e702bf554d3ab35d95badf420` (4) |
| `Toy.Codec.dec_unique_of_lawful` | `dec_unique_of_lawful` result | Quot.sound | `9fb59286ca786fd97cf833ee24444be4e3bd329d5278bc59809f73e404be9022` | `f50dcf31bcc1c94a2a33fc658988d54984df57925334fdfc797f04c2c919af66` (6) |
| `Toy.Codec.decomp_induces_lawful_and_complement` | `decomp_induces_lawful_and_complement` result | none | `2acb0f00ce6341ffaa8db2e6532a190e4589d673a7f4e911405eb3ff194a0b2c` | `3429dcfae2d8a19f7fc3fd50580c1a22f1584e9a12e493fa43fde2b8d99a3c54` (18) |
| `Toy.Codec.decomp_isEquiv_iff_lawful` | `decomp_isEquiv_iff_lawful` result | none | `52e63d2bb3405a77adcc5ad92dfa309d1b307c35b777df09a036d9952642204f` | `35b24b4350eb923e60930a59bf66d6abdf0e31027d817b8ffe9bfce9e38551bf` (14) |
| `Toy.Codec.encDec_admits_always_failing_codec` | `encDec_admits_always_failing_codec` result; `encDec_admits_always_failing_codec` non-vacuity | none | `381ef3990faa0bbd3205665178c8894eaa4cc032f0d694ee8dcc285d418ed8c1` | `5e78f44b6008e8beaad7933529251e7187dee0a5bfbc42a42d9bdf2c2d2df952` (7) |
| `Toy.Codec.fiberSplitOfLawful` | `codecOfFiberSplit_correspondence` cited companion | none | `263ca513135c96629ac69411e2374c3a089ffb3e2465cd22b95bc2d3b8863e45` | `3bbb7e03d5d9ad9f829c6373b6d597cfd7e30ed42cc7bdc27683bb7e6b4ed1a1` (7) |
| `Toy.Codec.framed_lawful_iff_decPrefix_eq_some_iff` | `framed_lawful_iff_decPrefix_eq_some_iff` result | none | `fa4e3e0d46879983448f4e8151d852d72915cd50e0b75ac700743087be323e85` | `6bfc8ca93eaa8d40c36bca3d74223a02ac32b1b2934054e161bc1b94a4fc068e` (6) |
| `Toy.Codec.junk_iff_not_in_image_of_lawful` | `lawful_dec_isSome_iff_mem_range` result | none | `de3ed07be2b4b5940b5c0a9d3368e0025c03f8f17f348fcfb0f6caff4d660363` | `f50dcf31bcc1c94a2a33fc658988d54984df57925334fdfc797f04c2c919af66` (6) |
| `Toy.Codec.lawful_dec_isSome_iff_mem_range` | `lawful_dec_isSome_iff_mem_range` result | none | `065531ccebdf2156f759f25c8593d3605a48da1abbcdee53f147ba5a5baee816` | `f50dcf31bcc1c94a2a33fc658988d54984df57925334fdfc797f04c2c919af66` (6) |
| `Toy.Codec.lawful_iff_decEnc_and_decInj` | `lawful_iff_decEnc_and_decInj` result | none | `53d87a454859ccb03badab0ae007b5f87e604106d33599d19f35a34b8feb799f` | `d98cc25d87385ecf6e3744c2e75cceb1ea44b24e8877b3701a5a3a9760387d2b` (7) |
| `Toy.Codec.lawful_iff_dec_eq_some_iff` | `lawful_iff_dec_eq_some_iff` result | none | `c1eea137b932f8caecb2b6d2ad0c042ddaa5cd2756ea572e90e403ae27ded2bf` | `f50dcf31bcc1c94a2a33fc658988d54984df57925334fdfc797f04c2c919af66` (6) |
| `Toy.Codec.lawful_injective_nonEmpty_enc_admits_ambiguous_concat` | `lawful_injective_nonEmpty_enc_admits_ambiguous_concat` result; `lawful_injective_nonEmpty_enc_admits_ambiguous_concat` non-vacuity | propext | `a3952943361ceb40208c623cdb628a14b5fb97025d8e0b8cd820f8a6b3a97077` | `b20af548dce1f06ce9d4f3f81cbcbdebe10293798fc1ccd11ccc68fd1017ab8a` (18) |
| `Toy.Codec.leftInv_decomp_iff_encDec` | `decomp_isEquiv_iff_lawful` result | none | `c5a8a399b7da92bb02ab12b0c8d0a0b5c249677090d2cb0861a66cc49bedd179` | `c8ba352546976c7aa573658f8964860b319697ab77c261d87ddb06e721e3dff9` (11) |
| `Toy.Codec.listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` | `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` result | Quot.sound, propext | `5d768306c55bfb7d413b6b6a29bad538fbbdc48a3530b7ec728dd872b10afbec` | `c8dc3a38ccacaf30df668eafc9e5f46b21995bfa1437a085ea468d765e883db6` (18) |
| `Toy.Codec.listCodec_encDec_of_prefixEncDec` | `listCodec_encDec_of_prefixEncDec` result | Quot.sound, propext | `efeffda742fa57ba79852ec65605032f37d73c1a49d4d01df08db9cf24ec2db1` | `f0059d69566fcc0254d3e83c70df33cb1690d487d3405c281807daafba2eac4a` (17) |
| `Toy.Codec.nonCanonicalBoolCodec_not_encDec_yet_admits_equiv` | `decomp_isEquiv_iff_lawful` cited companion | propext | `37693e4ff5f916594084729f3eda853b7394246a151be7379e392bd5849974a4` | `dfd679a8e14956f4e3b3155ded3171948372c4828b0bf05e8966800e02be5217` (19) |
| `Toy.Codec.nonEmptyEnc_of_prefixDecEnc_of_ne` | `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` cited companion | propext | `80925cd40124e469b37df980705958cee6cb41dc0b5977c108c7d7efaeda99d9` | `fc4affd4adf6ec5fc1c484325094f9263993126ca365245ec7a3c6757455d216` (6) |
| `Toy.Codec.nv_canonicalize_decEnc_of_decEnc` | `canonicalize_decEnc_of_decEnc` non-vacuity | propext | `468ff25841ea562f82219ef90b8d1c1d70a499142b691f6e34f8d26eaeb83b8d` | `8b27b2b57b9f14e32b01c15d9f7098fe47f866f36f31c2315b77f98e2a6a573f` (11) |
| `Toy.Codec.nv_classicalCodec_decEnc_of_injective` | `classicalCodec_bijection` non-vacuity | none | `e9eb52ab171c3dcd60f59de658889bc3210b2d42957c6fd01fde717e6bc00525` | `ea9a347b5fb2216bd25b0c7a1622a9c0b2bb829abc43db6b4e223a37912e92c3` (6) |
| `Toy.Codec.nv_classicalCodec_encDec` | `classicalCodec_bijection` non-vacuity | Classical.choice, Quot.sound, propext | `2e038f8141f3d1c348d155891a21955cabadf974bfecbd9d88453cf429db19a6` | `3c4674783dadff17f66217ff3317d92ea7a7b890862540a2c097af8c91c32bb1` (10) |
| `Toy.Codec.nv_classicalCodec_recover_of_lawful` | `classicalCodec_bijection` non-vacuity | none | `8bcb06bdecd455437b7dff9e2584ca9efc12c34429033c96055cd60ead03c7a2` | `dbcfd22f288cae7949132a9310b655b54330daf6d89b921e4958b3f446b6ca92` (9) |
| `Toy.Codec.nv_codecOfFiberSplit_decEnc_of_injective` | `codecOfFiberSplit_correspondence` non-vacuity | propext | `828e746d5f1f11c0317be24ec114469c8e848cb646d3b29f1472c0e82eb50aaa` | `ae4ca89a7dbc43eddb94a2954fd2296ab6f5bc7acc6560dcb719122399c4d655` (7) |
| `Toy.Codec.nv_codecOfFiberSplit_eq_of_lawful` | `codecOfFiberSplit_correspondence` non-vacuity | Quot.sound, propext | `0f8d3f760abce51759db2f080306a384bdca0a83b10735f29a78837c7e2294ef` | `6ace277d0e070d7bf36fcb5897d5f22ca30f02ce21575279051c186e71eb2d57` (16) |
| `Toy.Codec.nv_codecOfSplit_eq_iff_exists_intertwining_equiv` | `codecOfSplit_eq_iff_exists_intertwining_equiv` non-vacuity | Quot.sound, propext | `2e83053b9915efb3d1f86034fd14c11ff279aa2199633f2c562c74a3ff67edfc` | `6f133d4e6498853e6a855e0c8691191776cdff75288ac4d3fa5f581eec7fc36d` (30) |
| `Toy.Codec.nv_comp_decEnc` | `combinator_closure_decEnc_and_encDec` non-vacuity | none | `9884453f89fc9d35683b521208fa093d0924cc3b26ca576f61e46ebc94195969` | `ad4342f0b57613b28fd6f5324d6380f363588a1adcddfd92afa968443d7c3ac2` (10) |
| `Toy.Codec.nv_comp_encDec` | `combinator_closure_decEnc_and_encDec` non-vacuity | none | `3955c714bc51ddba26f6877f67d5d0781b7b98ccb88e7339b3ee52a20e375251` | `45eb377e6b9bf65c189a6e9ab6c149a9298344dac8553f13d60664ff20470117` (10) |
| `Toy.Codec.nv_decEnc_imp_enc_injective` | `decEnc_imp_enc_injective` non-vacuity | none | `a6a4166dcf1f031fd5193bf6df807b3f5c062ec73c5304c341a68f0ad7418e43` | `496b50c7c59228b7695d8b888da7e1cdf61744263866c1feead26d6690ad7b9e` (8) |
| `Toy.Codec.nv_decEqSomeIff_imp_enc_injective` | `lawful_iff_dec_eq_some_iff` non-vacuity | none | `26e7f3a3438395b55832a9177804948b0ba12a09cad97303815a327dff2e32cf` | `cd6ad759967673820da2402a5a8fb99637f7ce0c9a98a457b2e81780174328d3` (7) |
| `Toy.Codec.nv_dec_unique_of_lawful` | `dec_unique_of_lawful` non-vacuity | propext | `824b941da5633f0abf37aaf7aceb1a0d951c25f9f7d17f204e168f26b9b8f128` | `6ace277d0e070d7bf36fcb5897d5f22ca30f02ce21575279051c186e71eb2d57` (16) |
| `Toy.Codec.nv_decomp_induces_lawful_and_complement` | `decomp_induces_lawful_and_complement` non-vacuity | none | `7a760128bb6a7befd780cedfb5b3fa9f3ae65cd4796ee8389838809593ee596c` | `284e9624d5cc93bd96d63624484862fb6929ee00eac5addfe124da5919e96457` (6) |
| `Toy.Codec.nv_decomp_isEquiv_iff_lawful` | `decomp_isEquiv_iff_lawful` non-vacuity | propext | `8b4a75f4956ab164d9797c97f6f964a556e1c4ea44a421a5f95ba6988798b991` | `70937a66918c04ddd2a0491afea3b2012c4cef8c4eae0cf9eef56c59287537f6` (20) |
| `Toy.Codec.nv_framed_lawful_iff_decPrefix_eq_some_iff` | `framed_lawful_iff_decPrefix_eq_some_iff` non-vacuity | propext | `e5b0115cc2774e50d3f15f3f51d509c00cd4b44981068e1ef31e9f3a023a8242` | `a53f3806c5e928f1ee920ec6cda273ce704e5b7ae3b4594cbef1b7f9c0c3efc8` (11) |
| `Toy.Codec.nv_junk_iff_not_in_image_of_lawful` | `lawful_dec_isSome_iff_mem_range` non-vacuity | none | `8bcb06bdecd455437b7dff9e2584ca9efc12c34429033c96055cd60ead03c7a2` | `dbcfd22f288cae7949132a9310b655b54330daf6d89b921e4958b3f446b6ca92` (9) |
| `Toy.Codec.nv_lawful_dec_isSome_iff_mem_range` | `lawful_dec_isSome_iff_mem_range` non-vacuity | none | `8bcb06bdecd455437b7dff9e2584ca9efc12c34429033c96055cd60ead03c7a2` | `dbcfd22f288cae7949132a9310b655b54330daf6d89b921e4958b3f446b6ca92` (9) |
| `Toy.Codec.nv_lawful_iff_decEnc_and_decInj` | `lawful_iff_decEnc_and_decInj` non-vacuity | none | `e982deb22c9683793b451184f945c5aa3eb77ec7401584a10e244e8d04efdffb` | `d3ae5d4e38905ea0582deabb57ee335ec43745e25019b13a2579376a2211c67d` (10) |
| `Toy.Codec.nv_lawful_iff_dec_eq_some_iff` | `lawful_iff_dec_eq_some_iff` non-vacuity | none | `ea0d30e8dc8c77e28f4adc3c1e19f4d63373a2eb8aa45bf2727904215bf24b90` | `dbcfd22f288cae7949132a9310b655b54330daf6d89b921e4958b3f446b6ca92` (9) |
| `Toy.Codec.nv_listCodec_decEnc_iff_nonEmptyEnc` | `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` non-vacuity | Quot.sound, propext | `e908f7c0c084c252a05d5c8cdf1bfba74b0af5cad82b09d1fb6c1567740fae42` | `f7afa8c02c22b1fa0fdd6b48170bd25fa34d3f5496e41531c6d03fad61d8eb2d` (24) |
| `Toy.Codec.nv_listCodec_encDec` | `listCodec_encDec_of_prefixEncDec` non-vacuity | propext | `fb35da7f8ac29a1bc4e5982530f90d76e3e8d9870380169adc7749dd40f5495f` | `cea517a99d30fd2870f5cf088a6a21fa034d8fbad89004441c2282ed67538f09` (10) |
| `Toy.Codec.nv_nonEmptyEnc_of_prefixDecEnc_of_ne` | `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` non-vacuity | propext | `17220b0e81eafb58efa4c4f4484ac83416aaee10862822734c87ea0b3d0b3434` | `60b0cfcd2d477390dc0acfd7f0ab36b59e352184a02f995a741cdda522d49b10` (11) |
| `Toy.Codec.nv_prefixDecEnc_imp_prefixFree` | `prefixDecEnc_imp_prefixFree` non-vacuity | propext | `d3c3e58b4bb3dd9171cdd3d55220596414e131b3c020884f288e29265779b072` | `b55177271d6d0737af0be3f055adc63a5f4a22dc77ab90d3f201bf218def6090` (10) |
| `Toy.Codec.nv_prod_decEnc` | `combinator_closure_decEnc_and_encDec` non-vacuity | none | `9884453f89fc9d35683b521208fa093d0924cc3b26ca576f61e46ebc94195969` | `ad4342f0b57613b28fd6f5324d6380f363588a1adcddfd92afa968443d7c3ac2` (10) |
| `Toy.Codec.nv_prod_encDec` | `combinator_closure_decEnc_and_encDec` non-vacuity | none | `3955c714bc51ddba26f6877f67d5d0781b7b98ccb88e7339b3ee52a20e375251` | `45eb377e6b9bf65c189a6e9ab6c149a9298344dac8553f13d60664ff20470117` (10) |
| `Toy.Codec.nv_seq_prefixDecEnc` | `framed_seq_closure` non-vacuity | propext | `8b89de6bdfd6975911ebd41684772f6e3dccb7df0f27a98e6996dc591536a686` | `b55177271d6d0737af0be3f055adc63a5f4a22dc77ab90d3f201bf218def6090` (10) |
| `Toy.Codec.nv_seq_prefixEncDec` | `framed_seq_closure` non-vacuity | propext | `9a999090ca190640752a18e17d1b114e4d5586779c2b1294cb250f48e85b9981` | `cea517a99d30fd2870f5cf088a6a21fa034d8fbad89004441c2282ed67538f09` (10) |
| `Toy.Codec.nv_sum_decEnc` | `combinator_closure_decEnc_and_encDec` non-vacuity | none | `9884453f89fc9d35683b521208fa093d0924cc3b26ca576f61e46ebc94195969` | `ad4342f0b57613b28fd6f5324d6380f363588a1adcddfd92afa968443d7c3ac2` (10) |
| `Toy.Codec.nv_sum_encDec` | `combinator_closure_decEnc_and_encDec` non-vacuity | none | `3955c714bc51ddba26f6877f67d5d0781b7b98ccb88e7339b3ee52a20e375251` | `45eb377e6b9bf65c189a6e9ab6c149a9298344dac8553f13d60664ff20470117` (10) |
| `Toy.Codec.prefixDecEnc_imp_prefixFree` | `prefixDecEnc_imp_prefixFree` result | propext | `5ceb23d500c919e9b992083fa3918441ff9e2248a534ff611b5138374978c5df` | `b7fb8d82a561e225a412dc08ffe66e007459d929675106603f41f2bad58093f1` (6) |
| `Toy.Codec.prod_decEnc` | `combinator_closure_decEnc_and_encDec` result | propext | `371b32b95a805d0a4dbe9721d64b82de05cce44faf08b2723a6a774f190307bd` | `2d8f6d6918af250d5649bc6503267bf52c8b5391546dc44370959969084131de` (8) |
| `Toy.Codec.prod_encDec` | `combinator_closure_decEnc_and_encDec` result | propext | `59335156e34476b651e7c798d2cbebe965ea5280624852f284c1c60d0a6f3323` | `a608e86daa7affa1c5bb97c53bef0685428717723d0212ddbb95800b4aac3495` (8) |
| `Toy.Codec.rightInv_decomp_iff_decEnc` | `decomp_isEquiv_iff_lawful` result | none | `925d801bfc2d2fa6a1f012f95714d938e744422efb2ec692d89e62d1e3ded694` | `48ed017cb0a1f0038cd90cfdd50901d3629b5dca507ce74cbd6dccfb8f6d515a` (11) |
| `Toy.Codec.seq_prefixDecEnc` | `framed_seq_closure` result | propext | `f6f897cf918ddeeb5d01f4dfdeee8cd58ef8bde299551be62401eec7d2d604a4` | `c8c3f908b2d77d36285840172436fa73a5ac5093c6a9370b9c85f44e4b4027c7` (7) |
| `Toy.Codec.seq_prefixEncDec` | `framed_seq_closure` result | propext | `c7a4b88f49293936e0f6cbba2b39027e9eff41a6434ff6c34bd51a0fcff96dc5` | `1fa919525f9f7ca9e3ea860881aaae6d48512d32944182beacb6f7dbf41c2574` (7) |
| `Toy.Codec.suffixEnc_not_prefixFree_yet_concat_lawful` | `lawful_injective_nonEmpty_enc_admits_ambiguous_concat` positive control | Quot.sound, propext | `af730465ddc07c3c74afba458784ada396f6363cabdf68334f23a3827e20570a` | `de4d8085f9ab41596e433a1f736db15b1ff88cb995ab87a92876e66b7f2b4006` (18) |
| `Toy.Codec.sum_decEnc` | `combinator_closure_decEnc_and_encDec` result | none | `3d0a8e8aaf9d2c97ddf2e934c534a320fdd0ca64d4e81062f0464771b139c26f` | `b88710ef1f2b7ac973f5b3ffd40c1688210ae3d8e10e46548301902065b48ec6` (7) |
| `Toy.Codec.sum_encDec` | `combinator_closure_decEnc_and_encDec` result | none | `3b1e456e7c64cda0c54b463b24938b30660d3d6fb8c2317ae4c2193deb7719c8` | `c8ebb5e5f8734f46a619a52344b6552c73816369a230742c7ac7c45e0330fe64` (7) |

### Primary sources

Bibliographic records and pinned repository commits were verified on 2026-11-20 against Crossref metadata, arXiv, USENIX, and GitHub. The reading scope for each source is noted explicitly below:

- **Rendel & Ostermann (2010):** Tillmann Rendel and Klaus Ostermann, "Invertible syntax descriptions: unifying parsing and pretty printing," *Proceedings of the Third ACM Haskell Symposium on Haskell (Haskell '10)*, pp. 1–12, 2010. DOI `10.1145/1863523.1863525`. *Scope read:* Crossref metadata, authors' project page and talk slides, and Hackage package `partial-isomorphisms-0.2.4.0` (`Control.Isomorphism.Partial.Unsafe`, `Control.Isomorphism.Partial.Prim`); full paper PDF not retrieved.
- **Vytiniotis & Kennedy (2010):** Dimitrios Vytiniotis and Andrew J. Kennedy, "Functional pearl: every bit counts," *Proceedings of the 15th ACM SIGPLAN International Conference on Functional Programming (ICFP '10)*, pp. 15–26, 2010. DOI `10.1145/1863543.1863548`. *Scope read:* full text (author-hosted PDF; Section 3 Lemma 1, Corollaries 1–3, Lemma 3).
- **Kennedy & Vytiniotis (2012):** Andrew J. Kennedy and Dimitrios Vytiniotis, "Every bit counts: The binary representation of typed data and programs," *Journal of Functional Programming* 22(4–5), pp. 529–573, 2012. DOI `10.1017/S0956796812000263`. *Scope read:* Crossref metadata and publisher abstract only; full journal body not consulted (cited as secondary prose context alongside the directly examined ICFP '10 paper, and omitted from `REPORT.json` `subjects`).
- **Delaware et al. (2019, Narcissus):** Benjamin Delaware, Sorawit Suriyakarn, Clément Pit-Claudel, Qianchuan Ye, and Adam Chlipala, "Narcissus: Correct-by-Construction Derivation of Decoders and Encoders from Binary Formats," *Proceedings of the ACM on Programming Languages* 3 (ICFP), Article 82, 29 pp., August 2019. DOI `10.1145/3341686`. *Scope read:* full text (author-hosted published version; Definitions 2.1, 2.2, 3.1, Section 3 `format_suit`).
- **Ramananandro et al. (2019, EverParse):** Tahina Ramananandro, Antoine Delignat-Lavaud, Cédric Fournet, Nikhil Swamy, Tej Chajed, Nadim Kobeissi, and Jonathan Protzenko, "EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats," *28th USENIX Security Symposium*, pp. 1465–1482, 2019. URL `https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud` (no DOI). *Scope read:* full text (§2.1, §2.2, §5 Definitions 1–2, §5.1 `plist[p]`).
- **EverParse / LowParse mechanization:** GitHub repository `project-everest/everparse`, commit `f3e4ce51d9b68593fd98472cadcdeb8b6abf388f`, files `lib/everparse/lowparse/LowParse.Spec.Base.fsti` and `LowParse.Spec.List.fsti`. *Scope read:* direct source inspection (`serializer_correct`, `serializer_complete`, `serializer_correct_implies_complete`, `serializer_injective`, `serializer_parser_unique`, `parse_list_aux`, `serialize_list_precond`, `bare_serialize_list_correct`, `parse_list_bare_injective`).
- **Pickering, Gibbons & Wu (2017):** Matthew Pickering, Jeremy Gibbons, and Nicolas Wu, "Profunctor Optics: Modular Data Accessors," *The Art, Science, and Engineering of Programming* 1(2), Article 7, 2017. DOI `10.22152/programming-journal.org/2017/1/7`. *Scope read:* full text (arXiv:1703.10857).
- **Riley (2018):** Mitchell Riley, "Categories of Optics," arXiv:1809.00738v2 [math.CT], 7 September 2018. URL `https://arxiv.org/abs/1809.00738v2`. *Scope read:* full text (§3, Proposition 4.1.3 generalizing Johnson, Rosebrugh, and Wood 2010 as cited therein, §4.2 Definition 4.2.1, Propositions 4.2.2–4.2.3).
- **Clarke et al. (2024):** Bryce Clarke, Derek Elkins, Jeremy Gibbons, Fosco Loregian, Bartosz Milewski, Emily Pillmore, and Mario Román, "Profunctor Optics, a Categorical Update," *Compositionality* 6, Article 1, 23 February 2024. DOI `10.32408/compositionality-6-1` (arXiv:2001.07488). *Scope read:* full text (arXiv HTML v6, §3.1.6).
- **Foster et al. (2005 / 2007):** J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore, Benjamin C. Pierce, and Alan Schmitt, "Combinators for bi-directional tree transformations: a linguistic approach to the view update problem," *POPL '05*, pp. 233–246, 2005, DOI `10.1145/1040305.1040325`; journal version *ACM TOPLAS* 29(3), Article 17, May 2007, DOI `10.1145/1232420.1232424`. *Scope read:* Crossref bibliographic metadata (cited solely as background prose context for the classical `GetPut`/`PutGet`/`PutPut` lens laws, and omitted from `REPORT.json` `subjects`).
- **Haskell `lens` library (`lens-5.3.2`):** Module `Control.Lens.Prism`, Hackage documentation. *Scope read:* module documentation text for the three prism laws.
- **Isabelle Archive of Formal Proofs — `Optics`:** Simon Foster, Christian Pardillo-Laursen, and Frank Zeyda, "Optics," *Archive of Formal Proofs*, 25 May 2017, `https://www.isa-afp.org/entries/Optics.html`; official AFP Isabelle2026 release mirror `isabelle-prover/mirror-afp-2026`, commit `749ee1bd79285aeb2597f31d797d0e55d9af62c9`, file `thys/Optics/Prisms.thy` (also rendered at `https://www.isa-afp.org/browser_info/current/AFP/Optics/Prisms.html`). *Scope read:* direct source inspection (`wb_prism`, `match_build`, `build_match`, `build_match_iff`, `range_build`, `inj_build`, `prism_diff`, `prism_plus`, `prism_plus_wb`, `wb_prim_suml`, `wb_prim_sumr`).
- **Lean Mathlib (`mathlib4`):** GitHub repository `leanprover-community/mathlib4`, commit `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04`, files `Mathlib/Logic/Function/Basic.lean`, `Mathlib/Logic/Encodable/Basic.lean`, `Mathlib/Computability/Encoding.lean`, `Mathlib/Basic/PEquiv.lean`, `Mathlib/InformationTheory/Coding/PrefixFree.lean`, and `Mathlib/InformationTheory/Coding/UniquelyDecodable.lean`. *Scope read:* direct source inspection.
- **Rocq Corelib SSReflect & Mathematical Components:** GitHub repositories `rocq-prover/rocq`, commit `25f5b18a320e4796f181f938d3b74bebe7db4dc4` (`theories/Corelib/ssr/ssrfun.v`), and `math-comp/math-comp`, commit `1cf23375ae1948bc37a50f153a6fdd2338dacf98` (`boot/eqtype.v`). *Scope read:* direct source inspection.
- **`agda-unimath`:** GitHub repository `UniMath/agda-unimath`, commit `c0022bfc4e6f57fc84ca70d4d4e3aa568def5e3f`, files `src/foundation/decidable-maps.lagda.md` and `src/foundation/decidable-embeddings.lagda.md`. *Scope read:* direct source inspection.

Observation date: 2026-11-20 (kernel build, axiom audit, statement/closure hashes, and source verification).

## Revalidation

All commands below run from the package root directory and require only `elan` (which selects the pinned toolchain `leanprover/lean4:v4.34.1` declared in `lean/lean-toolchain`) and `python3` (standard library only).

1. **Primary one-command revalidation (`support/revalidate.py`):**

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` into a temporary directory without modifying the package and checks:
- comment-stripped Lean sources contain no `sorry`, `admit`, `native_decide`, or `axiom` declarations;
- `lake build` succeeds with exit status 0;
- `Lean.collectAxioms` across all 481 non-internal `Toy.*` declarations uses only subsets of `{propext, Classical.choice, Quot.sound}`; and
- every declaration referenced by `results.json` and recorded in `audit/statements.json` (116 declarations) reproduces its exact `statement_sha256`, `closure_sha256`, and `closure_size` as defined in **Evidence**.

Expected output (exit 0):
```text
ok   lake build
ok   axioms (481 declarations)
ok   statement hashes (116 hashed names; 0 referenced names exist but carry no recorded hash)
REVALIDATED
```

What `support/revalidate.py` does *not* check: exact per-declaration axiom-subset equality against `audit/axioms.json` (checked in Step 3 below), prose-to-Lean semantic fidelity, or external prior-art URLs/commits.

2. **Direct `lake` build and `#print axioms` spot-check for no-choice / zero-axiom declarations:**

```sh
(cd lean && lake clean && lake build)
cat <<'EOF' > /tmp/codec_check_axioms.lean
import Toy
#print axioms Toy.Codec.dec_unique_of_lawful
#print axioms Toy.Codec.codecOfFiberSplit_decEnc_of_injective
#print axioms Toy.Codec.codecOfFiberSplit_encDec
#print axioms Toy.Codec.fiberSplitOfLawful
#print axioms Toy.Codec.codecOfFiberSplit_eq_of_lawful
#print axioms Toy.Codec.lawful_dec_isSome_iff_mem_range
#print axioms Toy.Codec.junk_iff_not_in_image_of_lawful
#print axioms Toy.Codec.canonicalize_encDec
#print axioms Toy.Codec.leftInv_decomp_iff_encDec
#print axioms Toy.Codec.rightInv_decomp_iff_decEnc
#print axioms Toy.Codec.decomp_isEquiv_iff_lawful
#print axioms Toy.Codec.nonCanonicalBoolCodec_not_encDec_yet_admits_equiv
#print axioms Toy.Codec.decomp_induces_lawful_and_complement
#print axioms Toy.Codec.complementEquivOfCodecEq
#print axioms Toy.Codec.complementEquivOfCodecEq_intertwines
#print axioms Toy.Codec.codecOfSplit_eq_iff_exists_intertwining_equiv
EOF
(cd lean && lake env lean /tmp/codec_check_axioms.lean)
```

The build must exit 0 with zero `declaration uses 'sorry'` warnings, and `#print axioms` must report `'...' does not depend on any axioms` (or `[Quot.sound]` only for `dec_unique_of_lawful`, `codecOfFiberSplit_eq_of_lawful`, and `codecOfSplit_eq_iff_exists_intertwining_equiv`, and `[propext]` only for `nonCanonicalBoolCodec_not_encDec_yet_admits_equiv`), with `Classical.choice` absent throughout.

3. **Standalone `elan`/`lake`/`python3` reproduction of `audit/axioms.json` and `audit/statements.json` (without `support/revalidate.py`):**

```sh
python3 - <<'PY'
import hashlib, json, re, subprocess, tempfile

with open("results.json", encoding="utf-8") as f:
    results = json.load(f)
with open("audit/axioms.json", encoding="utf-8") as f:
    rec_axioms = json.load(f)["declarations"]
with open("audit/statements.json", encoding="utf-8") as f:
    rec_stmts = json.load(f)["statements"]

names = set(rec_stmts)
for r in results:
    for k in ("lean", "lean_names", "nonvacuity_witness_lean", "positive_control_lean"):
        v = r.get(k)
        names |= {v} if isinstance(v, str) else set(v or [])
    for h in r.get("hypotheses", []):
        ce = h.get("counterexample")
        names |= {ce} if isinstance(ce, str) else set(ce or [])

def lit(n):
    return "`" + ".".join(p if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'!?]*", p) else f"«{p}»" for p in n.split("."))

lean_src = '''import Lean
import Toy
open Lean Elab Command

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`Toy).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inPkg env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with | .inductInfo iv => iv.ctors | _ => [])
      closure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if inPkg env n && !n.isInternal then
      match ci with
      | .axiomInfo _ | .opaqueInfo _ => throwError "disallowed declaration kind: {n}"
      | _ => pure ()
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in [__NAMES__] do
    match env.find? n with
    | none => throwError "missing declaration: {n}"
    | some ci =>
      let cl := closure env (ci.type.getUsedConstants.toList) NameSet.empty
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      stmts := stmts.push (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))])
  IO.println ("AUDIT_JSON " ++ (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
'''.replace("__NAMES__", ", ".join(lit(n) for n in sorted(names)))

with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as tf:
    tf.write(lean_src)
    audit_path = tf.name

out = subprocess.check_output(["lake", "env", "lean", audit_path], cwd="lean", text=True)
data = json.loads(re.search(r"AUDIT_JSON (\{.*\})", out).group(1))
got_axioms = {d["name"]: sorted(d["axioms"]) for d in data["decls"]}
assert got_axioms == rec_axioms, "audit/axioms.json mismatch"
got_stmts = {
    s["name"]: {
        "statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
        "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
        "closure_size": len(s["closure"]),
    }
    for s in data["stmts"]
}
assert got_stmts == rec_stmts, "audit/statements.json mismatch"
print(f"OK: verified {len(got_axioms)} declarations and {len(got_stmts)} statement/closure hashes.")
PY
```

On a different Lean 4 release, `Expr` `repr`-based statement hashes may change even when statements are mathematically unchanged; in that case re-check the pretty-printed `#check` signatures and unfolded definitional-equality forms in **Findings** directly.
