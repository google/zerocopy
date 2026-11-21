# Enum niche layouts: documented guarantees vs. validity invariants (Lean 4 toy model)

## Summary

This package is a Lean 4 model of how an option-like enum can be laid out over the bytes of
its payload, with every theorem kernel-checked. A payload type is its set of valid
initialized byte patterns; a *niche* is an invalid pattern; a layout is an encoder plus a
decoder whose round-trip laws (`DecEnc`: decode after encode; `Canonical`: canonical
decoding) are separate hypotheses. The results separate what Rust's *documented* guarantees
for `Option<NonZero*>` (same size as the payload; `None` is all zero bytes; the transmute
`t -> Some(t)`) imply in the model from what a payload's validity invariant alone does not
imply (for `bool`-like payloads nothing selects `None`'s byte pattern), and count how many
extra dataless variants fit in the payload's size (exactly `numInvalid V`).
Model–system relation: none proved. Every theorem below is a statement about the model; it
neither establishes nor refutes the corresponding claims about Rust's option-like enum
layouts (as laid out by rustc and as documented in `core::option` and `core::result`) or
about zerocopy's byte-conversion traits; each connection to Rust is a separately labeled
modeling bridge.

Results (each sentence is the result's plain-language claim, stating its hypotheses):

* `nicheLayout_lawful_iff_isNiche` (characterization, T1): For any payload validity set V and pattern q, the niche-filled layout of Opt V in the payload's size (None -> q, Some v -> v's pattern, decoder reading q as None first) satisfies both round-trip laws iff q is invalid for V.
* `isNiche_enc_none_of_decSomeTransparent_of_decEnc` (impossibility, T0): For a layout of Opt V in the payload's size n in which every valid payload pattern decodes to Some of itself (DecSomeTransparent, the payload-to-option transmute) and decode-after-encode holds (DecEnc), the pattern of None is a niche of V: None cannot sit on a valid payload pattern. Nothing is assumed about how Some is encoded or about canonical decoding.
* `someTransparent_lawful_iff_eq_nicheLayout` (characterization, T1): A layout L of Opt V in the payload's size is Some-transparent (SomeTransparent: Some v -> v's pattern) and lawful iff L's None pattern q is a niche of V and L equals the niche-filled layout nicheLayout V q (encoder and decoder); the choice of niche is the only freedom. For lawful layouts SomeTransparent and DecSomeTransparent are equivalent (someTransparent_iff_decSomeTransparent_of_lawful).
* `opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc` (theorem, T1): If a layout of Opt V has the payload's size n (hsize), the payload has at most one niche (hV: numInvalid V <= 1) and decode-after-encode holds (hde), then decoding is canonical and every n-byte pattern decodes (FromBytes); neither the pattern of None nor canonical decoding is assumed.
* `dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical` (theorem, T0): For any layout of an option type (any payload type, any size) with None -> the zero pattern (hnone: NonePinned L 0) and both round-trip laws (hde, hcan), a pattern decodes to None iff it is the zero pattern. A definitional reference point for the canonical-free version.
* `dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc` (theorem, T1): If a layout of Opt V has the payload's size (hsize), the payload has at most one niche (hV), decode-after-encode holds (hde) and None -> the zero pattern (hnone), then a pattern decodes to None iff it is the zero pattern; canonical decoding is not assumed (it is forced by hsize, hV, hde).
* `opt_fromBytes_and_zero_iff_none_of_nichePinned_zero_of_numInvalid_le_one_of_decEnc` (theorem, T1): Under the documented guarantee NichePinned L 0 (size n and None -> 0), with at most one payload niche (hV: numInvalid V <= 1) and decode-after-encode (hde), every n-byte pattern decodes and the zero pattern is exactly None. The identity of the payload's niche is not used; for NonZero payloads hV follows from 'zero is the only niche' (numInvalid_le_one_of_only_niche_zero).
* `nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc` (theorem, T0): For the n-byte NonZero payload, any layout of Opt (nonZeroV n) in n bytes in which every valid payload pattern decodes to Some of itself (DecSomeTransparent) and decode-after-encode holds (DecEnc) represents None by the zero pattern.
* `nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc` (theorem, T1): For the n-byte NonZero payload, any layout of Opt (nonZeroV n) in n bytes in which every valid payload pattern decodes to Some of itself (DecSomeTransparent) and decode-after-encode holds (DecEnc) equals nicheLayout (nonZeroV n) (zeroPat n): zero <-> None and every other pattern p <-> Some p. Neither canonical decoding nor encoder-side transparency is assumed.
* `opt_bool_lawful_layouts_in_one_and_two_bytes` (counterexample, T1): For the bool-like payload (valid patterns 0 and 1 of 256), both the 1-byte niche-filled layout with None -> 2 and the 2-byte separately tagged layout are lawful, so validity plus lawfulness do not determine the size of Opt bool.
* `opt_bool_none_pattern_not_forced_by_someTransparent_lawful` (impossibility, T1): For every one-byte pattern q, not every lawful Some-transparent 1-byte layout of Opt bool represents None by q (NonePinned L q); even with the size and Some-transparency pinned, bool's validity set does not determine None's byte.
* `nicheLayoutK_lawful_iff_injective_and_isNiche` (characterization, T1): Niche filling of k extra dataless (inhabited) variants into the payload's n bytes with tag patterns t (nicheLayoutK V t) is lawful iff t is injective and every t i is a niche of V.
* `le_numInvalid_of_decEnc_of_size_le` (impossibility, T0): Any layout of an enum with k extra dataless (inhabited) variants over payload V that is no larger than the payload (hsize: m <= n) and satisfies decode-after-encode (hde) needs k <= numInvalid V (pigeonhole).
* `le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches` (characterization, T1): For k extra dataless (inhabited) variants over payload V: k <= numInvalid V iff some lawful layout of the enum fits in the payload's n bytes, iff the specific layout nicheLayoutK V (firstNiches V k) (the first k niches, in increasing order, used as tags) is lawful.
* `opt_opt_nonZero_no_decEnc_layout_in_payload_size` (impossibility, T0): For every n, the two-level option over the n-byte NonZero payload (Option (Opt (nonZeroV n)), modeling Option<Option<NonZeroUN>>; 257 values for n = 1) has no decode-after-encode layout in n bytes.

The non-claims of every result are listed first under **Boundaries**, before the escape
hatches; read them before applying any result to Rust.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

### Model fidelity

This is a **toy model**, not a model of rustc or of the Rust abstract machine. It captures the
byte-level view used by transmutes and by byte-conversion traits such as zerocopy's
`TryFromBytes`, `FromZeros` and `FromBytes`, restricted to fully initialized,
provenance-free bytes. The core definitions (module `Toy.Niche.Defs`, quoted):

```lean
abbrev Pat (n : Nat) : Type := Fin (256 ^ n)          -- n bytes, little-endian value
def zeroPat (n : Nat) : Pat n := ⟨0, pat_card_pos n⟩   -- [0u8; n]
abbrev Validity (n : Nat) : Type := Pat n → Bool       -- a payload type = its valid patterns
abbrev Val {n : Nat} (V : Validity n) : Type := {p : Pat n // V p = true}
def IsNiche {n : Nat} (V : Validity n) (p : Pat n) : Prop := V p = false
def invalidPats {n : Nat} (V : Validity n) : List (Pat n) :=
  (List.finRange (256 ^ n)).filter (fun p => !V p)
def numInvalid {n : Nat} (V : Validity n) : Nat := (invalidPats V).length
def nonZeroV (n : Nat) : Validity n := fun p => p.val != 0
def boolV : Validity 1 := fun p => decide (p.val < 2)
def geTwoV : Validity 1 := fun p => decide (2 ≤ p.val)
def allV (n : Nat) : Validity n := fun _ => true

@[ext] structure Layout (α : Type) (m : Nat) where
  enc : α → Pat m          -- the chosen representation of each value
  dec : Pat m → Option α   -- validity check plus interpretation
def DecEnc (L : Layout α m) : Prop := ∀ x, L.dec (L.enc x) = some x
def Canonical (L : Layout α m) : Prop := ∀ p x, L.dec p = some x → L.enc x = p
def Lawful (L : Layout α m) : Prop := DecEnc L ∧ Canonical L
def FromBytes (L : Layout α m) : Prop := ∀ p, ∃ x, L.dec p = some x

abbrev Opt {n : Nat} (V : Validity n) : Type := Option (Val V)
abbrev ExtEnum (k : Nat) {n : Nat} (V : Validity n) : Type := Fin k ⊕ Val V
def NonePinned (L : Layout (Option β) m) (p : Pat m) : Prop := L.enc none = p
def NichePinned {V : Validity n} (L : Layout (Opt V) m) (p : Pat m) : Prop :=
  m = n ∧ NonePinned L p
def SomeTransparent {V : Validity n} (L : Layout (Opt V) n) : Prop :=
  ∀ v : Val V, L.enc (some v) = v.val
def DecSomeTransparent {V : Validity n} (L : Layout (Opt V) n) : Prop :=
  ∀ v : Val V, L.dec v.val = some (some v)

def payloadLayout (V : Validity n) : Layout (Val V) n where
  enc v := v.val
  dec p := if h : V p = true then some ⟨p, h⟩ else none
def nicheLayout (V : Validity n) (q : Pat n) : Layout (Opt V) n where
  enc
    | none => q
    | some v => v.val
  dec p := if p = q then some none else if h : V p = true then some (some ⟨p, h⟩) else none
def nicheLayoutK {k : Nat} (V : Validity n) (t : Fin k → Pat n) : Layout (ExtEnum k V) n where
  enc
    | .inl i => t i
    | .inr v => v.val
  dec p :=
    match (List.finRange k).find? (fun i => t i == p) with
    | some i => some (.inl i)
    | none => if h : V p = true then some (.inr ⟨p, h⟩) else none
def firstNiches (V : Validity n) (k : Nat) : Fin k → Pat n :=
  fun i => (invalidPats V).getD i.val (zeroPat n)
```

`payloadLayout V` is the payload type's own layout: a value is its pattern and exactly the
valid patterns decode (it is lawful for every `V`, `payloadLayout_lawful`).
`taggedLayout L` (a separate tag byte: `0` = `None`, `1` = `Some`, `n + 1` bytes, only
canonical patterns decode) and `taggedLooseLayout L` (the same, but any pattern with tag `0`
decodes as `None`) are the tagged comparison layouts. A transmute from type `S` to type `T`
is modeled as `T.dec (S.enc x)`.

What the definitions are meant to capture, and the intended instances: `nonZeroV n` is the
bit validity of `NonZero<uN>` for `n ≥ 1` (at `n = 0` it is the empty validity set);
`boolV` is `bool`; `allV n` is a niche-free integer; `NonePinned L 0` is the documented
"`None` is `[0u8; size_of::<T>()]`"; the size component of `NichePinned` is the documented
"`Option<T>` has the same size as `T`" (`NichePinned` does **not** say the pattern is a
niche); `DecSomeTransparent` is the documented transmute `T -> Option<T>` producing
`Some(t)`; `SomeTransparent` is the documented transmute `Option<T> -> T` producing `t` from
`Some(t)`. Both transparency predicates are stated for `L : Layout (Opt V) n`, so they fix
the layout's size to the payload's. With `DecEnc`, `SomeTransparent` implies
`DecSomeTransparent` (`decSomeTransparent_of_someTransparent_of_decEnc`); with `Canonical`
the converse holds; neither implication holds without that law
(`decSomeTransparent_decEnc_not_someTransparent`, `someTransparent_not_decSomeTransparent`).
`DecEnc` is MiniRust's first round-trip property; `Canonical` is MiniRust's second property
restricted to fully initialized bytes; `Lawful` is a lawful concrete prism from patterns to
values (Riley, §4.2).

Every core definition has proved positive and negative examples in `Toy.Niche.Witnesses`
(for example `ex_isNiche`/`nex_isNiche`, `ex_numInvalid`/`nex_numInvalid`,
`ex_lawful`/`nex_lawful`, `nex_canonical` via `geTwoLooseLayout`, `ex_fromBytes`/`nex_fromBytes`,
`ex_nichePinned`/`nex_nichePinned`/`nex_nichePinned_none`, `nichePinned_admits_valid_pattern`,
`ex_someTransparent`/`nex_someTransparent`, `ex_decSomeTransparent`/`nex_decSomeTransparent`,
`ex_nicheLayoutK`/`nex_nicheLayoutK`, `ex_firstNiches`/`nex_firstNiches`,
`taggedLooseLayout_eq_taggedLayout_at_zero`, `nonZeroV_zero_empty`). For instance,
`ex_nicheLayoutK` shows that two extra variants over `geTwoV` with the distinct niche tags `0`
and `1` give a lawful layout, and `nex_nicheLayoutK` shows that two extra variants over the
one-byte `NonZero` payload sharing the tag `0` break decode-after-encode.

Named concrete layouts used by counterexamples (all in `Toy.Niche.Witnesses`; for the
explicitly enumerated 1-byte layouts the laws are checked by `decide`, `sparse2In1Byte_lawful`
is proved by case analysis and `omega`, the two lawful `ExtEnum 1` transports by
`comap_lawful`, and the facts about `zeroDecLayout` and `ext1AllZeroDecLayout` by case
analysis or `rfl`):

* `swapLayout` (`None ↦ 1`, `Some 1 ↦ 0`, otherwise `Some v ↦ v`; lawful, neither
  transparent);
* `permLayout` (`None ↦ 0`, `Some 1` and `Some 2` exchanged; lawful, neither transparent);
* `zeroDecLayout` (the niche-filling encoder with a decoder that rejects everything);
* `noneLostLayout` (`None ↦ 1`, every valid pattern decodes to `Some`);
* `geTwoLooseLayout` (niche filling `None ↦ 0` whose decoder also reads `1` as `None`;
  `DecEnc`, not `Canonical`);
* `decSomeNotSomeLayout` (a 1-byte layout of `Opt boolV`: `None ↦ 2`, `Some false ↦ 3`,
  `Some true ↦ 4`, with the decoder reading `0` and `3` as `Some false` and `1` and `4` as
  `Some true`; `DecEnc` and `DecSomeTransparent` but not `SomeTransparent`,
  `decSomeTransparent_decEnc_not_someTransparent`);
* `swap01Layout` (a 1-byte layout of `Opt nonOneV`, where `nonOneV` is the one-byte payload
  whose only niche is `1`: `None ↦ 0` although `0` is valid, `Some 0 ↦ 1`, otherwise
  `Some v ↦ v`; lawful);
* `sparse2In1Byte` (one extra variant over `sparse2V`, the two-byte payload whose only valid
  patterns are `0` and `1`, in a single byte: the extra variant `↦ 2`, a payload value `↦` its
  own value; lawful, so a layout can be smaller than its payload);
* the `ExtEnum 1` layouts `ext1NonZeroLayout` (`nicheLayout (nonZeroV 1) (zeroPat 1)`
  transported to `ExtEnum 1 (nonZeroV 1)` by `Layout.comap` along the bijection
  `Opt V ≃ ExtEnum 1 V`; lawful, 1 byte), `ext1AllTaggedLayout`
  (`taggedLayout (payloadLayout (allV 1))` transported the same way to `ExtEnum 1 (allV 1)`;
  lawful, 2 bytes) and `ext1AllZeroDecLayout` (a 1-byte layout of `ExtEnum 1 (allV 1)` that
  encodes everything as the zero pattern and decodes nothing; not `DecEnc`).

### Known gaps between the model and Rust

* No uninitialized bytes, no pointer provenance, no alignment, no padding, and no safety
  invariants. A payload value is identified with its unique byte pattern: true for integers,
  `bool` and `NonZero*`, false for types with padding.
* Pointer-like payloads (`&T`, `&mut T`, `Box<T>`, `NonNull<T>`, `fn` pointers) are not
  modeled: their validity is not a set of initialized patterns with a single invalid element,
  and provenance and alignment matter.
* A model niche is *any* invalid pattern. rustc only uses values outside one scalar's valid
  range (the Unsafe Code Guidelines glossary: not every invalid bit pattern is a niche), so
  `numInvalid V` can exceed what rustc uses: `UnsafeCell` disables niches; `char` surrogates
  `0xD800..=0xDFFF` are invalid but inside `char`'s scalar valid range `0..=0x10FFFF`; for
  `(bool, bool)` only one field's 254 out-of-range values are used although 65532 two-byte
  patterns are invalid.
* The model's extra enum variants are inhabited and dataless; rustc gives uninhabited
  variants whose fields are all 1-ZSTs no discriminant value, and can fit small data-carrying
  variants around a niche.
* `Canonical` excludes a tagged `None` whose payload bytes are unconstrained; with
  uninitialized bytes such a layout satisfies MiniRust's second law but not `Canonical`
  (modeled by `taggedLooseLayout`). Results stated without `Canonical` do not depend on this.
* Byte order: patterns are read as little-endian values by convention; which integer a
  pattern denotes is outside the model.

### Documented guarantees vs. observed layouts

These are kept apart throughout.

*Documented* (Rust core documentation; the hypotheses the bridges instantiate):

* `core::option` "Representation" at the pinned nightly commit: for `Box<U>` (only
  `Box<U, Global>`), `&U`, `&mut U`, `fn` pointers, `num::NonZero*`, `ptr::NonNull<U>` and
  `#[repr(transparent)]` wrappers of these, `Option<T>` has the same size, alignment and call
  ABI as `T`, and transmuting `t` to `Option<T>` produces `Some(t)` and `Some(t)` to `T`
  produces `t`. "In some of these cases" `[0u8; size_of::<T>()]` transmutes to `None` and back:
  only when `U: Sized` for `Box<U, Global>`, `&U`, `&mut U`, `NonNull<U>`; always for `fn`
  pointers and `NonZero*`. The Rust 1.89.0 docs have the same table and zero-bytes bullets but
  state only that the transmutes are sound, without "producing the value `Some(t)`".
* `NonZero<T>` "Layout": same layout and bit validity as `T` except that the all-zero pattern
  is invalid; `NonZero<T>` and `Option<NonZero<T>>` have the same size and alignment.
* `core::result` "Representation" at the pinned nightly commit
  (`library/core/src/result.rs` lines 234-245), verbatim (rustdoc link markup kept):

  > In some cases, [`Result<T, E>`] comes with size, alignment, and ABI
  > guarantees. Specifically, one of either the `T` or `E` type must be a type
  > that qualifies for the `Option` [representation guarantees][opt-rep] (let's
  > call that type `I`), and the *other* type is a zero-sized type with
  > alignment 1 (a "1-ZST").
  >
  > If that is the case, then `Result<T, E>` has the same size, alignment, and
  > [function call ABI] as `I` (and therefore, as `Option<I>`). If `I` is `T`,
  > it is therefore sound to transmute a value `t` of type `I` to type
  > `Result<T, E>` (producing the value `Ok(t)`) and to transmute a value
  > `Ok(t)` of type `Result<T, E>` to type `I` (producing the value `t`). If `I`
  > is `E`, the same applies with `Ok` replaced by `Err`.

  Of the `Option` guarantees listed in the first bullet, exactly four carry over to such a
  `Result<T, E>`: (1) the same **size** as `I`; (2) the same **alignment**; (3) the same
  function call **ABI**; (4) the **Some-transmute**, in its `Ok` form (`t -> Ok(t)` and
  `Ok(t) -> t`) or, when `I` is `E`, its `Err` form. The fifth, the **zeroed-`None`
  case** (`[0u8; size_of::<T>()]` transmutes to `None` and back), does **not** carry over:
  the section never mentions zero bytes, and RFC 3391 grants only "the same layout (size and
  alignment) and the same ABI as the primitive form of the data". So no documented guarantee
  says that zero bytes are `Err(())` (or `Ok(())`) for pointer-like `Result<&U, ()>`,
  `Result<&mut U, ()>`, `Result<Box<U>, ()>`, `Result<NonNull<U>, ()>` or
  `Result<fn(), ()>`. For `Result<NonZeroUN, ()>` and `Result<(), NonZeroUN>` the zero-bytes
  fact holds in the model but is derived, not documented: reading the dataless variant as
  `None` and the payload variant as `Some`, the transmute `t -> Ok(t)` (or `t -> Err(t)`) is
  `DecSomeTransparent`, and with decode-after-encode
  `nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc` puts the dataless variant on
  the zero pattern. The Rust 1.89.0 `core::result` "Representation" section (from line 231)
  says only that `Result<T, E>` "will gain the same size, alignment, and ABI guarantees as
  [`Option<U>`] has", with no transmute sentence, and further requires the 1-ZST to have no
  fields and not to be `#[non_exhaustive]`; it does not state the value-preserving
  `t -> Ok(t)` transmute the derivation uses. Basis: derived (modeling bridge); no theorem
  mentions `Result`.
* RFC 3391 deliberately does not extend these guarantees to all similar enums, so
  user-defined option-like enums have no documented niche guarantee; the Rustonomicon notes
  that an explicit `repr(C)`/`repr(u*)`/`repr(i*)` on an enum with fields suppresses the
  null-pointer optimization.
* The Reference's validity rules: a `bool` must be `0` or `1`; a `char` must not be a
  surrogate.

*Observed but undocumented* (one rustc build on one target; see **Evidence**): `Option<bool>`
and `Option<Option<bool>>` have size 1 with `None = 0x02` and `0xff` respectively;
`Option<Option<NonZeroU8>>` and `Option<u8>` have size 2; `Option<UnsafeCell<NonZeroU32>>` has
size 8; `Result<u8, Infallible>` has size 1; enums with a `bool` payload and 254/255 dataless
variants have sizes 1/2, with a `(bool, bool)` payload 2/3. No theorem proves or relies on
any of these; they illustrate what the documented guarantees and validity alone do not fix.

### Subjects and versions

The Lean development is checked with Lean `v4.34.1` (`leanprover/lean4`), core library only
(no Mathlib, no other dependency). The Rust documentation and rustc layout code are quoted at
`rust-lang/rust` commit `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (1.102.0-nightly), with
the stable Rust 1.89.0 documentation (tag `1.89.0`, commit
`29483883eed69d5fb4db01964cdf2af4d86e9cb2`) as the contrast for the transmute wording. The
Reference, Rustonomicon, Unsafe Code Guidelines, RFC 3391, MiniRust and zerocopy subjects are
the sources of the hypotheses' intended meaning and of the prior-art comparison; the two
literature subjects (Riley; Jung) supply the prism reading of `Lawful` and the
validity/safety distinction. The theorems do not depend on any of these revisions; only the
modeling bridges do.

## Findings

Every result below is a theorem of the Lean library `Toy` (namespace `Toy.Niche`), proved with no `sorry` and checked by the Lean kernel. Per result: tier, Lean statement (with the relevant definitions unfolded in comments), hypothesis ledger, depth, non-vacuity witness, positive control for impossibility results, prior art (keys refer to the records under **Evidence**), and the design question. A depth label rates the argument a result rests on, counting the steps of other package results that its proof actually uses rather than the length of its final proof: a result obtained by composing results that invoke the counting argument of `opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc` is `shallow`, like that result itself. The `Basis: execution (Lean kernel check)` line covers only the formal statement; the separate `Basis: derived (modeling bridge)` line is the claim about Rust and its reasoning.

Notation in the unfolded statements: `Pat n = Fin (256 ^ n)`, `Val V = {p : Pat n // V p = true}`, `Opt V = Option (Val V)`, `ExtEnum k V = Fin k ⊕ Val V`.

### Group 1 — niche filling

#### `nicheLayout_lawful_iff_isNiche`

* **Kind / tier / depth:** characterization, T1, `shallow`.
* **Plain claim:** For any payload validity set V and pattern q, the niche-filled layout of Opt V in the payload's size (None -> q, Some v -> v's pattern, decoder reading q as None first) satisfies both round-trip laws iff q is invalid for V.

```lean
-- lean/Toy/Niche/Results.lean:43-44
theorem nicheLayout_lawful_iff_isNiche (V : Validity n) (q : Pat n) :
    Lawful (nicheLayout V q) ↔ IsNiche V q
-- nicheLayout V q : enc none = q, enc (some v) = v.val,
--   dec p = if p = q then some none else if h : V p = true then some (some ⟨p, h⟩) else none
-- Lawful L = DecEnc L ∧ Canonical L ; IsNiche V q ⇔ V q = false
```

* **Hypotheses:** none beyond the quantified variables (an equivalence or a closed statement).
* **Non-vacuity witness:** V = nonZeroV 4 (4-byte NonZero validity), q = zeroPat 4: both sides hold. (`nv_nicheLayout_lawful_iff_isNiche`)
* **Related proved witnesses:** `ce_nicheLayout_lawful_valid_q` (`q = 1` is valid for `boolV` and `nicheLayout boolV 1` is not lawful), `nicheLayout_valid_q_canonical_not_decEnc` (that layout is still canonical; only decode-after-encode fails), `lawful_not_nicheLayout` (`swapLayout` and `permLayout` are lawful 1-byte layouts of `Opt (nonZeroV 1)` that are not `nicheLayout (nonZeroV 1) (L.enc none)`).
* **Prior art:** [S8] Unsafe Code Guidelines glossary: Niche; [S9] rustc enum layout and `Niche` code; [S11] MiniRust round-trip properties; [S12] Riley, Categories of Optics, §4.2; [S13] Jung, Two Kinds of Invariants.
* **Design question:** Which byte patterns may an option-like enum's None occupy without breaking decode/encode round-trips?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For a Rust payload type `T` whose values correspond one-to-one to their initialized byte patterns (integers, `bool`, `NonZero*`), a layout of an option-like enum that stores `Some(t)` as `t`'s bytes and `None` as a fixed pattern `q`, and decodes `q` first, round-trips exactly when `q` is an invalid bit pattern of `T`. Reasoning: `T` is modeled by its validity set and the layout by `nicheLayout V q`; the theorem is about that layout only and does not say rustc chooses it.

#### `isNiche_enc_none_of_decSomeTransparent_of_decEnc`

* **Kind / tier / depth:** impossibility, T0, `definitional`.
* **Plain claim:** For a layout of Opt V in the payload's size n in which every valid payload pattern decodes to Some of itself (DecSomeTransparent, the payload-to-option transmute) and decode-after-encode holds (DecEnc), the pattern of None is a niche of V: None cannot sit on a valid payload pattern. Nothing is assumed about how Some is encoded or about canonical decoding.

```lean
-- lean/Toy/Niche/Results.lean:29-31
theorem isNiche_enc_none_of_decSomeTransparent_of_decEnc {V : Validity n}
    (L : Layout (Opt V) n) (hdst : DecSomeTransparent L) (hde : DecEnc L) :
    IsNiche V (L.enc none)
-- hdst : ∀ v : Val V, L.dec v.val = some (some v) ; hde : ∀ x, L.dec (L.enc x) = some x
-- ⊢ V (L.enc none) = false
```

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hdst` | DecSomeTransparent L: every valid payload pattern decodes to Some of itself (the documented transmute t -> Some(t)); the type Layout (Opt V) n also fixes the layout's size to the payload's size n. | tight: counterexample `ce_isNiche_enc_none_drop_decSomeTransparent` |
| `hde` | DecEnc L: None's own pattern decodes to None. | tight: counterexample `ce_isNiche_enc_none_drop_decEnc` |

* **Non-vacuity witness:** nicheLayout (nonZeroV 4) (zeroPat 4) satisfies DecSomeTransparent and DecEnc. (`nv_isNiche_enc_none`)
* **Positive control:** `pc_isNiche_enc_none` (a nearby setting where the conclusion fails; see Boundaries for the escape hatches).
* **Prior art:** [S1] `core::option` Representation (rust-lang/rust `3ef0c22c`; Rust 1.89.0 contrast); [S3] `core::result` Representation and RFC 3391; [S8] Unsafe Code Guidelines glossary: Niche; [S7] Rustonomicon: explicit `repr` suppresses the null-pointer optimization.
* **Design question:** Given the documented t -> Some(t) transmute, what can be inferred about the byte pattern of None?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For `Option<T>` with `T` in the `core::option` Representation list and a payload modeled by a validity set (the `NonZero*` types), the value-preserving transmute `t -> Some(t)` together with decode-after-encode implies that `None`'s bytes are invalid for `T`. Reasoning: the documented same-size guarantee fixes `L : Layout (Opt V) n`; the transmute sentence at the pinned nightly commit instantiates `DecSomeTransparent`; decode-after-encode is MiniRust's first round-trip property. The Rust 1.89.0 docs state only that the transmute is sound, which does not instantiate `DecSomeTransparent`.

#### `someTransparent_lawful_iff_eq_nicheLayout`

* **Kind / tier / depth:** characterization, T1, `shallow`.
* **Plain claim:** A layout L of Opt V in the payload's size is Some-transparent (SomeTransparent: Some v -> v's pattern) and lawful iff L's None pattern q is a niche of V and L equals the niche-filled layout nicheLayout V q (encoder and decoder); the choice of niche is the only freedom. For lawful layouts SomeTransparent and DecSomeTransparent are equivalent (someTransparent_iff_decSomeTransparent_of_lawful).

```lean
-- lean/Toy/Niche/Results.lean:57-59
theorem someTransparent_lawful_iff_eq_nicheLayout {V : Validity n} (L : Layout (Opt V) n) :
    (SomeTransparent L ∧ Lawful L) ↔
      (IsNiche V (L.enc none) ∧ L = nicheLayout V (L.enc none))
-- SomeTransparent L : ∀ v : Val V, L.enc (some v) = v.val
-- Canonical L : ∀ p x, L.dec p = some x → L.enc x = p
```

* **Hypotheses:** none beyond the quantified variables (an equivalence or a closed statement).
* **Non-vacuity witness:** nicheLayout (nonZeroV 4) (zeroPat 4): both sides hold. (`nv_someTransparent_lawful_iff_eq_nicheLayout`)
* **Related proved witnesses:** `lawful_not_nicheLayout`, `decSomeTransparent_decEnc_not_someTransparent`.
* **Prior art:** [S1] `core::option` Representation (rust-lang/rust `3ef0c22c`; Rust 1.89.0 contrast); [S11] MiniRust round-trip properties; [S12] Riley, Categories of Optics, §4.2.
* **Design question:** Once size and Some-transparency are pinned, how much freedom is left in an Option<T> layout?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — If a Rust `Option<T>` layout (payload modeled by a validity set) has `T`'s size, represents `Some(t)` by `t`'s bytes, and satisfies both round-trip laws on initialized bytes, it is niche filling at one invalid pattern of `T`. Reasoning: `SomeTransparent` instantiates the documented transmute `Some(t) -> t` (nightly wording); `Canonical` is the initialized-bytes restriction of MiniRust's second round-trip property and is not documented for Rust, so this bridge carries that extra assumption.

### Group 2 — what the documented guarantee buys (`NonZero` payloads)

#### `opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc`

* **Kind / tier / depth:** theorem, T1, `shallow`.
* **Plain claim:** If a layout of Opt V has the payload's size n (hsize), the payload has at most one niche (hV: numInvalid V <= 1) and decode-after-encode holds (hde), then decoding is canonical and every n-byte pattern decodes (FromBytes); neither the pattern of None nor canonical decoding is assumed.

```lean
-- lean/Toy/Niche/Results.lean:104-106
theorem opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc
    (V : Validity n) (L : Layout (Opt V) m) (hsize : m = n) (hV : numInvalid V ≤ 1)
    (hde : DecEnc L) : Canonical L ∧ FromBytes L
-- hV : ((List.finRange (256 ^ n)).filter (fun p => !V p)).length ≤ 1
-- ⊢ (∀ p x, L.dec p = some x → L.enc x = p) ∧ ∀ p : Fin (256 ^ m), ∃ x, L.dec p = some x
```

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hsize` | m = n: the layout's size is equal to the payload's size (the documented same-size guarantee). | tight: counterexample `ce_canonical_fromBytes_drop_size` |
| `hV` | numInvalid V <= 1: the payload's validity set leaves at most one pattern unused. | tight: counterexample `ce_canonical_fromBytes_drop_numInvalid` |
| `hde` | DecEnc L: each value has a valid representation and decoding is a function, so the encoder is injective. | tight: counterexample `ce_canonical_fromBytes_drop_decEnc` |

* **Non-vacuity witness:** nicheLayout (nonZeroV 4) (zeroPat 4) with m = n = 4 (numInvalid (nonZeroV 4) = 1). (`nv_opt_canonical_and_fromBytes`)
* **Prior art:** [S2] `NonZero<T>` Layout (rust-lang/rust `3ef0c22c`); [S1] `core::option` Representation (rust-lang/rust `3ef0c22c`; Rust 1.89.0 contrast); [S10] zerocopy impls for `NonZero*` and `Option<...>`; [S14] Mathlib finite pigeonhole lemmas (not used); [S4] `UnsafeCell<T>` Memory layout and rustc's niche disabling; [S7] Rustonomicon: explicit `repr` suppresses the null-pointer optimization.
* **Design question:** Is FromBytes for Option<NonZero*> justified by the documented same-size guarantee and NonZero's bit validity alone?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For `Option<NonZeroUN>`, the documented same-size guarantee (`core::option`, `NonZero<T>` Layout) and `NonZero`'s documented bit validity (exactly the all-zero pattern is invalid, so `numInvalid V = 1`, `numInvalid_nonZeroV`) together with decode-after-encode imply that every *initialized* `N`-byte pattern is a valid `Option<NonZeroUN>` and that decoding is canonical. Reasoning: instantiate `V = nonZeroV N` and `m = n`. This is the counting argument behind zerocopy's `FromBytes` impl for `Option<NonZeroXxx>`, restricted to initialized bytes; it is not a proof about rustc's actual layout, only about every layout satisfying the documented hypotheses.

#### `dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical`

* **Kind / tier / depth:** theorem, T0, `definitional`.
* **Plain claim:** For any layout of an option type (any payload type, any size) with None -> the zero pattern (hnone: NonePinned L 0) and both round-trip laws (hde, hcan), a pattern decodes to None iff it is the zero pattern. A definitional reference point for the canonical-free version.

```lean
-- lean/Toy/Niche/Results.lean:144-146
theorem dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical
    (L : Layout (Option β) m) (hnone : NonePinned L (zeroPat m)) (hde : DecEnc L)
    (hcan : Canonical L) : ∀ p, L.dec p = some none ↔ p = zeroPat m
-- hnone : L.enc none = zeroPat m   (zeroPat m = ⟨0, _⟩, the pattern [0u8; m])
```

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hnone` | NonePinned L (zeroPat m): the documented None -> [0u8; size] guarantee. | tight: counterexample `ce_zero_iff_none_drop_nonePinned` |
| `hde` | DecEnc L: the zero pattern actually decodes to None. | tight: counterexample `ce_zero_iff_none_drop_decEnc` |
| `hcan` | Canonical L: no second pattern decodes to None. | tight: counterexample `ce_zero_iff_none_drop_canonical` |

* **Non-vacuity witness:** nicheLayout (nonZeroV 4) (zeroPat 4). (`nv_zero_iff_none_lawful`)
* **Prior art:** [S1] `core::option` Representation (rust-lang/rust `3ef0c22c`; Rust 1.89.0 contrast); [S11] MiniRust round-trip properties; [S12] Riley, Categories of Optics, §4.2.
* **Design question:** Reference point (definitional). Informs: when is 'all bytes zero' a complete test for None, and what does canonical decoding contribute compared with the canonical-free route?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For a Rust option type with the documented `None <-> [0u8; size]` guarantee, if decoding is also canonical then the all-zero pattern is the only representation of `None`. Reasoning: `hnone` instantiates the documented zero-bytes bullet (where the `core::option` table grants it); `Canonical` is not documented for Rust and is an extra assumption here.

#### `dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc`

* **Kind / tier / depth:** theorem, T1, `shallow`.
* **Plain claim:** If a layout of Opt V has the payload's size (hsize), the payload has at most one niche (hV), decode-after-encode holds (hde) and None -> the zero pattern (hnone), then a pattern decodes to None iff it is the zero pattern; canonical decoding is not assumed (it is forced by hsize, hV, hde).

```lean
-- lean/Toy/Niche/Results.lean:159-162
theorem dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc
    (V : Validity n) (L : Layout (Opt V) m) (hsize : m = n) (hV : numInvalid V ≤ 1)
    (hde : DecEnc L) (hnone : NonePinned L (zeroPat m)) :
    ∀ p, L.dec p = some none ↔ p = zeroPat m
-- hnone : L.enc none = zeroPat m ; no Canonical hypothesis
```

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hsize` | m = n: excludes extra bytes that could carry a second None representation. | tight: counterexample `ce_zero_iff_none_drop_size` |
| `hV` | numInvalid V <= 1: excludes a spare niche that could also decode as None. | tight: counterexample `ce_zero_iff_none_drop_numInvalid` |
| `hde` | DecEnc L. | tight: counterexample `ce_zero_iff_none_drop_decEnc` |
| `hnone` | NonePinned L (zeroPat m): the documented None -> [0u8; size] guarantee. | tight: counterexample `ce_zero_iff_none_drop_nonePinned` |

* **Non-vacuity witness:** nicheLayout (nonZeroV 4) (zeroPat 4). (`nv_zero_iff_none_size_numInvalid`)
* **Prior art:** [S1] `core::option` Representation (rust-lang/rust `3ef0c22c`; Rust 1.89.0 contrast); [S2] `NonZero<T>` Layout (rust-lang/rust `3ef0c22c`); [S10] zerocopy impls for `NonZero*` and `Option<...>`; [S14] Mathlib finite pigeonhole lemmas (not used); [S7] Rustonomicon: explicit `repr` suppresses the null-pointer optimization.
* **Design question:** Can a validator accept exactly the zero pattern as None for Option<NonZero*> without assuming canonical decoding?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For `Option<NonZeroUN>`, documented facts alone (same size; `None <-> [0u8; N]`, granted "always" for `NonZero*` in the table's second column; `NonZero` bit validity) plus decode-after-encode imply that a pattern decodes to `None` iff it is all zeros. Reasoning: instantiate `V = nonZeroV N`, `m = n`, `hnone` from the zero-bytes bullet; canonicity is derived, not assumed.

#### `opt_fromBytes_and_zero_iff_none_of_nichePinned_zero_of_numInvalid_le_one_of_decEnc`

* **Kind / tier / depth:** theorem, T1, `shallow`.
* **Plain claim:** Under the documented guarantee NichePinned L 0 (size n and None -> 0), with at most one payload niche (hV: numInvalid V <= 1) and decode-after-encode (hde), every n-byte pattern decodes and the zero pattern is exactly None. The identity of the payload's niche is not used; for NonZero payloads hV follows from 'zero is the only niche' (numInvalid_le_one_of_only_niche_zero).

```lean
-- lean/Toy/Niche/Results.lean:171-174
theorem opt_fromBytes_and_zero_iff_none_of_nichePinned_zero_of_numInvalid_le_one_of_decEnc
    (V : Validity n) (L : Layout (Opt V) m) (hpin : NichePinned L (zeroPat m))
    (hV : numInvalid V ≤ 1) (hde : DecEnc L) :
    FromBytes L ∧ ∀ p, L.dec p = some none ↔ p = zeroPat m
-- hpin : m = n ∧ L.enc none = zeroPat m
```

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hpin (size component m = n)` | Same-size guarantee. | tight: counterexample `ce_documented_drop_size_pin` |
| `hpin (None component NonePinned L (zeroPat m))` | None -> [0u8; n]; needed only for the second conjunct. | tight: counterexample `ce_documented_drop_none_pin` |
| `hV` | numInvalid V <= 1: at most one invalid payload pattern (for NonZero: exactly the zero pattern). | tight: counterexample `ce_documented_drop_numInvalid` |
| `hde` | DecEnc L. | tight: counterexample `ce_documented_drop_decEnc` |

* **Non-vacuity witness:** nicheLayout (nonZeroV 4) (zeroPat 4) (the Option<NonZeroU32> case). (`nv_documented`)
* **Related proved witnesses:** `documented_niche_identity_not_needed`, `numInvalid_le_one_of_only_niche_zero`.
* **Prior art:** [S1] `core::option` Representation (rust-lang/rust `3ef0c22c`; Rust 1.89.0 contrast); [S2] `NonZero<T>` Layout (rust-lang/rust `3ef0c22c`); [S3] `core::result` Representation and RFC 3391; [S10] zerocopy impls for `NonZero*` and `Option<...>`; [S4] `UnsafeCell<T>` Memory layout and rustc's niche disabling; [S7] Rustonomicon: explicit `repr` suppresses the null-pointer optimization.
* **Design question:** What do the documented NPO guarantees plus NonZero bit validity buy byte-level code such as zerocopy's FromBytes/FromZeros impls for Option<NonZero*>?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For `Option<NonZeroUN>`, the documented guarantee (size `N`, `None` is `[0u8; N]`) plus `NonZero`'s bit validity plus decode-after-encode give both "every initialized pattern is valid" and "zero bytes are exactly `None`" — the initialized-bytes content of zerocopy's `FromBytes` and `FromZeros` impls for `Option<NonZeroXxx>`. Reasoning: as for the two results it conjoins; uninitialized bytes, `IntoBytes` and alignment are outside the model.

#### `nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc`

* **Kind / tier / depth:** theorem, T0, `definitional`.
* **Plain claim:** For the n-byte NonZero payload, any layout of Opt (nonZeroV n) in n bytes in which every valid payload pattern decodes to Some of itself (DecSomeTransparent) and decode-after-encode holds (DecEnc) represents None by the zero pattern.

```lean
-- lean/Toy/Niche/Results.lean:181-183
theorem nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc
    (L : Layout (Opt (nonZeroV n)) n) (hdst : DecSomeTransparent L) (hde : DecEnc L) :
    NonePinned L (zeroPat n)
-- nonZeroV n p = (p.val != 0) ; ⊢ L.enc none = zeroPat n
```

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hdst` | DecSomeTransparent L: every valid payload pattern decodes to Some of itself (the documented transmute t -> Some(t)); the type Layout (Opt V) n also fixes the layout's size to the payload's size n. | tight: counterexample `ce_nonePinned_zero_drop_decSomeTransparent` |
| `hde` | DecEnc L. | tight: counterexample `ce_nonePinned_zero_drop_decEnc` |

* **Non-vacuity witness:** nicheLayout (nonZeroV 4) (zeroPat 4). (`nv_decSomeTransparent_decEnc`)
* **Prior art:** [S1] `core::option` Representation (rust-lang/rust `3ef0c22c`; Rust 1.89.0 contrast); [S2] `NonZero<T>` Layout (rust-lang/rust `3ef0c22c`); [S7] Rustonomicon: explicit `repr` suppresses the null-pointer optimization.
* **Design question:** Is the documented None -> [0u8; n] guarantee for Option<NonZero*> independent of the t -> Some(t) guarantee?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For `Option<NonZeroUN>`, the transmute `t -> Some(t)` (nightly wording) and decode-after-encode already force `None` to be `[0u8; N]`, so within the model the documented zero-bytes bullet for `NonZero*` is derivable from the transmute sentence. Reasoning: instantiate `V = nonZeroV N`; the only niche is zero (`isNiche_nonZeroV_iff`).

#### `nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc`

* **Kind / tier / depth:** theorem, T1, `shallow`.
* **Plain claim:** For the n-byte NonZero payload, any layout of Opt (nonZeroV n) in n bytes in which every valid payload pattern decodes to Some of itself (DecSomeTransparent) and decode-after-encode holds (DecEnc) equals nicheLayout (nonZeroV n) (zeroPat n): zero <-> None and every other pattern p <-> Some p. Neither canonical decoding nor encoder-side transparency is assumed.

```lean
-- lean/Toy/Niche/Results.lean:189-191
theorem nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc
    (L : Layout (Opt (nonZeroV n)) n) (hdst : DecSomeTransparent L) (hde : DecEnc L) :
    L = nicheLayout (nonZeroV n) (zeroPat n)
-- equality of structures: same enc and same dec
```

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hdst` | DecSomeTransparent L: every valid payload pattern decodes to Some of itself (the documented transmute t -> Some(t)); the type Layout (Opt V) n also fixes the layout's size to the payload's size n. | tight: counterexample `ce_layout_determined_drop_decSomeTransparent` |
| `hde` | DecEnc L. | tight: counterexample `ce_layout_determined_drop_decEnc` |

* **Non-vacuity witness:** nicheLayout (nonZeroV 4) (zeroPat 4). (`nv_decSomeTransparent_decEnc`)
* **Related proved witnesses:** `decSomeTransparent_of_someTransparent_of_decEnc`, `decSomeTransparent_decEnc_not_someTransparent`.
* **Prior art:** [S1] `core::option` Representation (rust-lang/rust `3ef0c22c`; Rust 1.89.0 contrast); [S2] `NonZero<T>` Layout (rust-lang/rust `3ef0c22c`); [S10] zerocopy impls for `NonZero*` and `Option<...>`; [S4] `UnsafeCell<T>` Memory layout and rustc's niche disabling; [S7] Rustonomicon: explicit `repr` suppresses the null-pointer optimization.
* **Design question:** Do the documented guarantees fully determine the bytes-to-value map of Option<NonZero*>?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — For `Option<NonZeroUN>`, the nightly-documented transmute `t -> Some(t)` and decode-after-encode determine the whole layout on initialized bytes: zero is `None` and every nonzero pattern `p` is `Some(p)`. Reasoning: instantiate `V = nonZeroV N`. Under the Rust 1.89.0 docs, which state only that the transmutes are sound, lawful alternatives such as `permLayout` are not excluded by the model.

### Group 3 — what validity alone does not buy (`bool`-like payload)

#### `opt_bool_lawful_layouts_in_one_and_two_bytes`

* **Kind / tier / depth:** counterexample, T1, `definitional`.
* **Plain claim:** For the bool-like payload (valid patterns 0 and 1 of 256), both the 1-byte niche-filled layout with None -> 2 and the 2-byte separately tagged layout are lawful, so validity plus lawfulness do not determine the size of Opt bool.

```lean
-- lean/Toy/Niche/Results.lean:228-229
theorem opt_bool_lawful_layouts_in_one_and_two_bytes :
    Lawful (nicheLayout boolV 2) ∧ Lawful (taggedLayout (payloadLayout boolV))
-- nicheLayout boolV 2 : Layout (Opt boolV) 1 ; taggedLayout (payloadLayout boolV) : Layout (Opt boolV) 2
-- payloadLayout boolV : Layout (Val boolV) 1 (a value is its own pattern; exactly the valid patterns decode)
-- boolV p = decide (p.val < 2)
```

* **Hypotheses:** none beyond the quantified variables (an equivalence or a closed statement).
* **Non-vacuity witness:** The statement itself exhibits both layouts. (`opt_bool_lawful_layouts_in_one_and_two_bytes`)
* **Related proved witnesses:** `nonZero_lawful_layouts_in_one_and_two_bytes` (the same for the one-byte `NonZero` payload: `nicheLayout (nonZeroV 1) (zeroPat 1)` in 1 byte and `taggedLayout (payloadLayout (nonZeroV 1))` in 2 bytes are both lawful).
* **Prior art:** [S5] Reference: default representation and `bool` representation; [S1] `core::option` Representation (rust-lang/rust `3ef0c22c`; Rust 1.89.0 contrast); [S9] rustc enum layout and `Niche` code.
* **Design question:** May code assume size_of::<Option<bool>>() == 1 from bool's validity invariant alone?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — `bool`'s documented validity (0 and 1 valid, every other byte invalid) permits both a 1-byte niche-filling layout and a 2-byte tagged layout of `Option<bool>` that round-trip; no documented guarantee selects one. Reasoning: `boolV` models `bool`'s validity; the observed 1-byte layout of `Option<bool>` (with `None = 0x02`) is a rustc implementation choice, not derivable from validity.

#### `opt_bool_none_pattern_not_forced_by_someTransparent_lawful`

* **Kind / tier / depth:** impossibility, T1, `shallow`.
* **Plain claim:** For every one-byte pattern q, not every lawful Some-transparent 1-byte layout of Opt bool represents None by q (NonePinned L q); even with the size and Some-transparency pinned, bool's validity set does not determine None's byte.

```lean
-- lean/Toy/Niche/Results.lean:235-236
theorem opt_bool_none_pattern_not_forced_by_someTransparent_lawful (q : Pat 1) :
    ¬ ∀ L : Layout (Opt boolV) 1, SomeTransparent L → Lawful L → NonePinned L q
-- NonePinned L q : L.enc none = q
```

* **Hypotheses:** none beyond the quantified variables (an equivalence or a closed statement).
* **Non-vacuity witness:** nicheLayout boolV 2 is lawful and Some-transparent, so the quantified class is nonempty. (`nv_opt_bool_none_pattern_not_forced`)
* **Positive control:** `pc_nonZero_none_pattern_forced` (a nearby setting where the conclusion fails; see Boundaries for the escape hatches).
* **Prior art:** [S5] Reference: default representation and `bool` representation; [S1] `core::option` Representation (rust-lang/rust `3ef0c22c`; Rust 1.89.0 contrast); [S9] rustc enum layout and `Niche` code.
* **Design question:** May code assume Option<bool>::None is the byte 0x02?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — No single byte pattern for `None` in a 1-byte `Option<bool>` follows from `bool`'s validity invariant, Some-transparency and both round-trip laws. Reasoning: two lawful Some-transparent layouts with different `None` patterns exist (`None = 2` and `None = 3`); rustc's observed `0x02` comes from its `Niche::reserve` rule, not from validity.

### Group 4 — cardinality

#### `nicheLayoutK_lawful_iff_injective_and_isNiche`

* **Kind / tier / depth:** characterization, T1, `shallow`.
* **Plain claim:** Niche filling of k extra dataless (inhabited) variants into the payload's n bytes with tag patterns t (nicheLayoutK V t) is lawful iff t is injective and every t i is a niche of V.

```lean
-- lean/Toy/Niche/Results.lean:251-253
theorem nicheLayoutK_lawful_iff_injective_and_isNiche {k : Nat} (V : Validity n)
    (t : Fin k → Pat n) :
    Lawful (nicheLayoutK V t) ↔ (Function.Injective t ∧ ∀ i, IsNiche V (t i))
-- nicheLayoutK V t : enc (inl i) = t i, enc (inr v) = v.val,
--   dec p = match (List.finRange k).find? (fun i => t i == p) with
--     | some i => some (inl i) | none => if h : V p = true then some (inr ⟨p, h⟩) else none
```

* **Hypotheses:** none beyond the quantified variables (an equivalence or a closed statement).
* **Non-vacuity witness:** k = 2, V = geTwoV, tags 0 and 1: injective, both niches, layout lawful. (`nv_nicheLayoutK`)
* **Related proved witnesses:** `nex_nicheLayoutK` (two extra variants over the one-byte `NonZero` payload sharing the tag `0` break decode-after-encode), `ex_nicheLayoutK_one` (one extra variant over that payload with tag `0` is lawful).
* **Prior art:** [S9] rustc enum layout and `Niche` code; [S8] Unsafe Code Guidelines glossary: Niche.
* **Design question:** Which tag assignments are valid when an enum hides several dataless variants in a payload's niches?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — An enum with `k` inhabited dataless variants plus one variant carrying `T`, laid out by niche filling with tag patterns `t`, round-trips iff the `k` tags are pairwise distinct invalid patterns of `T`. Reasoning: `ExtEnum k V` models such an enum; rustc additionally restricts tags to out-of-range values of one scalar, so the model's condition is necessary but not sufficient for a tag set rustc would use.

#### `le_numInvalid_of_decEnc_of_size_le`

* **Kind / tier / depth:** impossibility, T0, `shallow`.
* **Plain claim:** Any layout of an enum with k extra dataless (inhabited) variants over payload V that is no larger than the payload (hsize: m <= n) and satisfies decode-after-encode (hde) needs k <= numInvalid V (pigeonhole).

```lean
-- lean/Toy/Niche/Results.lean:304-305
theorem le_numInvalid_of_decEnc_of_size_le {k : Nat} (V : Validity n)
    (L : Layout (ExtEnum k V) m) (hsize : m ≤ n) (hde : DecEnc L) : k ≤ numInvalid V
-- ExtEnum k V = Fin k ⊕ Val V
```

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hsize` | m <= n: the layout is no larger than the payload; the case m < n is inhabited (nv_le_numInvalid_size_lt). | tight: counterexample `ce_le_numInvalid_drop_size` |
| `hde` | DecEnc L: injective encoder. | tight: counterexample `ce_le_numInvalid_drop_decEnc` |

* **Non-vacuity witness:** ext1NonZeroLayout: one extra variant over nonZeroV 1 in 1 byte, DecEnc. (`nv_le_numInvalid`)
* **Positive control:** `pc_le_numInvalid` (a nearby setting where the conclusion fails; see Boundaries for the escape hatches).
* **Related proved witnesses:** `nv_le_numInvalid_size_lt` (the case `m < n` is inhabited: `sparse2In1Byte`, one extra variant over the two-byte payload `sparse2V`, satisfies `DecEnc` in 1 byte).
* **Prior art:** [S14] Mathlib finite pigeonhole lemmas (not used); [S9] rustc enum layout and `Niche` code; [S13] Jung, Two Kinds of Invariants; [S4] `UnsafeCell<T>` Memory layout and rustc's niche disabling; [S6] Reference: invalid values; rustc `char` valid range; [S7] Rustonomicon: explicit `repr` suppresses the null-pointer optimization.
* **Design question:** When must an enum be larger than its payload?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — An enum with `k` inhabited dataless variants plus one `T` variant has no decode-after-encode layout in at most `size_of::<T>()` bytes unless `T` has at least `k` invalid initialized patterns; e.g. `Option<u8>` (no invalid pattern) cannot fit in 1 byte (observed size 2). Reasoning: pigeonhole over `256^m <= 256^n` patterns; rustc's usable niche values are a subset of the invalid patterns, so rustc's own constraint is at least as strong. Uninhabited extra variants (not modeled) need no pattern.

#### `le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches`

* **Kind / tier / depth:** characterization, T1, `shallow`.
* **Plain claim:** For k extra dataless (inhabited) variants over payload V: k <= numInvalid V iff some lawful layout of the enum fits in the payload's n bytes, iff the specific layout nicheLayoutK V (firstNiches V k) (the first k niches, in increasing order, used as tags) is lawful.

```lean
-- lean/Toy/Niche/Results.lean:335-338
theorem le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches
    (V : Validity n) (k : Nat) :
    (k ≤ numInvalid V ↔ ∃ L : Layout (ExtEnum k V) n, Lawful L) ∧
      (k ≤ numInvalid V ↔ Lawful (nicheLayoutK V (firstNiches V k)))
-- firstNiches V k i = (invalidPats V).getD i.val (zeroPat n)
-- invalidPats V = (List.finRange (256 ^ n)).filter (fun p => !V p)
```

* **Hypotheses:** none beyond the quantified variables (an equivalence or a closed statement).
* **Non-vacuity witness:** k = 2, V = geTwoV: 2 <= numInvalid geTwoV and nicheLayoutK geTwoV (firstNiches geTwoV 2) is lawful. (`nv_le_numInvalid_iff`)
* **Related proved witnesses:** `firstNiches_injective_and_isNiche_of_le_numInvalid` (if `k ≤ numInvalid V`, the first `k` niches `firstNiches V k` are pairwise distinct niches), `ce_firstNiches_drop_le` (for `nonZeroV 1`, which has one niche, `2 ≤ numInvalid` fails and `firstNiches (nonZeroV 1) 2` is not injective).
* **Prior art:** [S14] Mathlib finite pigeonhole lemmas (not used); [S9] rustc enum layout and `Niche` code; [S4] `UnsafeCell<T>` Memory layout and rustc's niche disabling; [S6] Reference: invalid values; rustc `char` valid range.
* **Design question:** How many extra variants can a payload absorb without growing, and which layout realizes that?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — `k` inhabited dataless variants fit next to `T` in `T`'s size under *some* lawful layout iff `T` has at least `k` invalid patterns, witnessed by tagging with the first `k` invalid patterns. Reasoning: the existence direction is about the model; rustc can use fewer niches than the model counts (one scalar's range only; none behind `UnsafeCell`), so it does not predict rustc's sizes (an enum with a `(bool, bool)` payload and 255 dataless variants is observed at 3 bytes although 65532 of its 2-byte patterns are invalid).

#### `opt_opt_nonZero_no_decEnc_layout_in_payload_size`

* **Kind / tier / depth:** impossibility, T0, `shallow`.
* **Plain claim:** For every n, the two-level option over the n-byte NonZero payload (Option (Opt (nonZeroV n)), modeling Option<Option<NonZeroUN>>; 257 values for n = 1) has no decode-after-encode layout in n bytes.

```lean
-- lean/Toy/Niche/Results.lean:351-352
theorem opt_opt_nonZero_no_decEnc_layout_in_payload_size
    (L : Layout (Option (Opt (nonZeroV n))) n) : ¬ DecEnc L
-- Option (Opt (nonZeroV n)) = Option (Option {p : Fin (256 ^ n) // p.val != 0})
```

* **Hypotheses:** none beyond the quantified variables (an equivalence or a closed statement).
* **Non-vacuity witness:** For every n the quantified type of n-byte layouts is nonempty. (`nv_opt_opt_nonZero`)
* **Positive control:** `pc_opt_opt_nonZero` (a nearby setting where the conclusion fails; see Boundaries for the escape hatches).
* **Related proved witnesses:** `pc_opt_nonZero_one_level` (one level of option over the `n`-byte `NonZero` payload has a lawful `n`-byte layout), `opt_opt_two_niches_one_byte` (states `Lawful (nicheLayoutK geTwoV geTwoTags) ∧ numInvalid geTwoV = 2`: a lawful 1-byte layout of `ExtEnum 2 geTwoV`, the enum with two dataless variants over a payload with exactly two niches; it is not stated for `Option (Opt geTwoV)`), `optOptNonZero_two_bytes_not_canonical_and_fromBytes` (no 2-byte layout of `Option (Opt (nonZeroV 1))` is both canonical and `FromBytes`), `optOptNonZeroTwoByteLoose_decEnc_fromBytes_not_canonical` (a 2-byte layout of that type with `DecEnc` and `FromBytes` but not `Canonical`), `optOpt_card_bound_of_canonical_of_fromBytes` (if `L : Layout (Option (Opt V)) m` is canonical and every pattern decodes, the encoder is onto all `256 ^ m` patterns, so `256 ^ m + numInvalid V ≤ 256 ^ n + 2`).
* **Prior art:** [S14] Mathlib finite pigeonhole lemmas (not used); [S2] `NonZero<T>` Layout (rust-lang/rust `3ef0c22c`); [S9] rustc enum layout and `Niche` code.
* **Design question:** Can nested options over NonZero integers stay the size of the integer?
* **Non-claims:** listed under Boundaries.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — `Option<Option<NonZeroUN>>` has no decode-after-encode layout of size `N`; for `N = 1` (257 values, 256 patterns) this is consistent with the observed size 2 of `Option<Option<NonZeroU8>>`. Reasoning: instantiate the cardinality bound with `numInvalid (nonZeroV n) = 1 < 2`. No specific size is implied.

### Execution cross-check against one rustc build (evidence, not proof)

`lean/support/niche_probe.rs` was compiled with `rustc -O niche_probe.rs` using
`rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, commit
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, host `x86_64-unknown-linux-gnu`, LLVM 23.1.5
(`lean/support/rustc_version.txt`). Its output (`lean/support/niche_probe_output.txt`):

```text
== sizes (bytes) and alignments ==
u32: size 4 align 4
NonZeroU32: size 4 align 4
Option<NonZeroU32>: size 4 align 4
u8: size 1
NonZeroU8: size 1
Option<NonZeroU8>: size 1
Option<Option<NonZeroU8>>: size 2
Option<u8>: size 2
&u32: size 8
Option<&u32>: size 8
Box<u32>: size 8
Option<Box<u32>>: size 8
fn(): size 8
Option<fn()>: size 8
bool: size 1
Option<bool>: size 1  (observed; not guaranteed)
Option<Option<bool>>: size 1  (observed; not guaranteed)
== Option<NonZeroU32> from bytes (guaranteed cases) ==
transmute([0u8; 4]) = None
transmute(None::<NonZeroU32>) = [0, 0, 0, 0]
transmute(0x00000001.to_ne_bytes()) = Some(1)
transmute(0x00000002.to_ne_bytes()) = Some(2)
transmute(0x01020304.to_ne_bytes()) = Some(16909060)
transmute(0xffffffff.to_ne_bytes()) = Some(4294967295)
== observed byte patterns (not guaranteed) ==
Option<bool>: None = 0x02, Some(false) = 0x00, Some(true) = 0x01
Option<Option<bool>>: None = 0xff, Some(None) = 0x02
== layout facts referenced by the non-claims (observed; not guaranteed) ==
Result<u8, Infallible>: size 1
UnsafeCell<NonZeroU32>: size 4
Option<UnsafeCell<NonZeroU32>>: size 8
char: size 4
Option<char>: size 4
(bool, bool): size 2
enum { P(bool), 254 dataless }: size 1
enum { P(bool), 255 dataless }: size 2
enum { P((bool, bool)), 254 dataless }: size 2
enum { P((bool, bool)), 255 dataless }: size 3
```

Basis: execution (rustc probe on the recorded toolchain and host)

How the observations relate to the model (none of them is proved by, or proves, a theorem):

* `Option<NonZero*>`: the observed sizes and zero-bytes transmute results are consistent with
  the *hypotheses* of `opt_fromBytes_and_zero_iff_none_of_nichePinned_zero_of_numInvalid_le_one_of_decEnc`
  and `nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc` (same size,
  `None ↦ 0`, `t ↦ Some(t)`) and with what those theorems derive (every pattern decodes; zero
  is exactly `None`; a nonzero `p` decodes to `Some p`). The theorems assume the size and
  transmute guarantees; they do not prove that Rust provides them.
* `Option<Option<NonZeroU8>>` and `Option<u8>` observed at 2 bytes: consistent with
  `opt_opt_nonZero_no_decEnc_layout_in_payload_size` and `le_numInvalid_of_decEnc_of_size_le`
  (with `numInvalid (allV 1) = 0`), which rule out a 1-byte layout. They do not say the size
  is 2.
* `Option<Option<bool>>` observed at 1 byte: consistent with
  `le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches`
  (`2 ≤ numInvalid boolV = 254`), but not implied by it; no guarantee covers it.
* The `None` bytes `0x02` (`Option<bool>`) and `0xff` (`Option<Option<bool>>`) come from
  rustc's `Niche::reserve`: for a single reserved value it takes the free value closest to
  zero under signed (sign-extended, wrapping) distance, except that the valid range `0..=1`
  is excluded from that rule; for `Option<Option<bool>>` the inner `Option<bool>` has valid
  range `0..=2` and the closest free value is `-1 = 0xff`.
  `opt_bool_none_pattern_not_forced_by_someTransparent_lawful` says no such choice follows
  from validity.
* Last section: `Result<u8, Infallible>` has size 1 (uninhabited extra variants need no
  niche, unlike the model's `ExtEnum`); `Option<UnsafeCell<NonZeroU32>>` has size 8 (niches
  disabled, so the documented size guarantee does not extend to it); with 254 vs. 255 dataless
  variants next to a `(bool, bool)` payload the size goes from 2 to 3, so at most 254 niche
  values were used although 65532 two-byte patterns are invalid (model niche counts are an
  upper bound on what rustc uses).

`lean/support/small_universe_check.py` (output in `lean/support/small_universe_check_output.txt`)
exhaustively enumerates all encoders and decoders over pattern universes of at most 4
patterns and checks the shapes of the statements named in its output. It is a sanity check,
not a proof. The quoted documentation text is reproduced in `lean/support/README.md`.

## Boundaries

### Non-claims (per result)

**`nicheLayout_lawful_iff_isNiche`**

* Concerns one specific decoder (nicheLayout); that no decoder at all works when None sits on a valid pattern and valid patterns decode to Some is isNiche_enc_none_of_decSomeTransparent_of_decEnc.
* When q is valid only decode-after-encode fails: nicheLayout V q is still canonical (nicheLayout_valid_q_canonical_not_decEnc).
* Does not say every lawful n-byte layout of Opt V is a nicheLayout: without Some-transparency, lawful layouts such as swapLayout and permLayout exist outside this family (lawful_not_nicheLayout).
* Does not say rustc uses this layout or this q; rustc only uses values outside a scalar's valid range (Niche::available) and may choose a tagged layout instead.
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`isNiche_enc_none_of_decSomeTransparent_of_decEnc`**

* Escape hatches: dropping DecSomeTransparent admits a lawful layout with None on a valid pattern (swapLayout: None -> 1, Some 1 -> 0; the positive control); dropping DecEnc admits noneLostLayout (None -> 1 while every valid pattern decodes to Some).
* Does not say L.enc none is the only pattern decoding to None: without Canonical (or the payload's size together with numInvalid V <= 1), other niches may also decode to None (geTwoLooseLayout).
* Does not determine which niche None uses when V has several niches (opt_bool_none_pattern_not_forced_by_someTransparent_lawful).
* DecSomeTransparent models the value-preserving transmute t -> Some(t), which the core::option docs state at the pinned nightly commit; the Rust 1.89.0 docs state only that this transmute is sound, so the hypothesis is not justified by the 1.89.0 docs alone.
* Applies in Rust only where the guarantees it instantiates (the payload's size and the value-preserving transmute t -> Some(t)) are documented: Option<T> for T in the core::option Representation list, or Result<T, E> with a 1-ZST, for which core::result documents the same size and the t -> Ok(t) (or t -> Err(t)) transmute but not Option's zeroed-None guarantee; user-defined option-like enums and enums with explicit repr(C)/repr(u*)/repr(i*) have no documented niche guarantee.
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`someTransparent_lawful_iff_eq_nicheLayout`**

* Uses canonical decoding: without Canonical, a Some-transparent DecEnc layout may decode extra niches as None (as in geTwoLooseLayout), so the decoder is not determined on niches other than q.
* Does not assert that a Some-transparent lawful layout exists: when numInvalid V = 0 both sides are false.
* Without SomeTransparent, lawful n-byte layouts need not equal nicheLayout V (L.enc none) (lawful_not_nicheLayout: swapLayout, permLayout).
* Says nothing about layouts of a different size (e.g. tagged layouts).
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc`**

* If numInvalid V = 0 the hypotheses are unsatisfiable (le_numInvalid_of_decEnc_of_size_le), so the statement is vacuous there.
* Does not say which value a pattern decodes to; that needs None -> 0 for the zero pattern and DecSomeTransparent for valid payload patterns (nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc).
* Does not establish zerocopy's IntoBytes or Unaligned: the model has no uninitialized or padding bytes and no alignment (Option<NonZeroU32> has alignment 4); IntoBytes for Option<NonZero*> additionally needs that none of its values contains uninitialized bytes.
* In Rust, the size hypothesis holds only where documented: Option<T> for T in the core::option Representation list, and Result<T, E> with a 1-ZST. It is undocumented or false for user-defined option-like enums, enums with explicit repr(C)/repr(u*)/repr(i*), and Option<UnsafeCell<NonZero*>> (UnsafeCell disables niches; observed size 8 for Option<UnsafeCell<NonZeroU32>> in lean/support/niche_probe_output.txt).
* Does not apply to Option<&T>, Option<Box<T>>, Option<NonNull<T>> or Option<fn()>: their payloads are not modeled by a validity set with at most one invalid initialized pattern, and provenance and alignment are outside the model. For unsized pointees (Option<&[u8]>, Option<Box<dyn Trait>>) not even the zero-bytes <-> None guarantee is documented (core::option restricts it to U: Sized).
* Says nothing about uninitialized bytes: real from-bytes conversions also require initialized input.
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical`**

* Canonical decoding is not documented for Rust option types; the version without it is dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc.
* Does not imply FromBytes or that nonzero patterns are valid: for bool-like payloads or tagged layouts most nonzero patterns decode to nothing (nex_fromBytes, ex_taggedLayout).
* In Rust, the documented None <-> [0u8; size_of::<T>()] guarantee (hnone) holds for NonZero* and fn pointers, and for Box<U, Global>, &U, &mut U and NonNull<U> only when U: Sized; it is not documented for unsized pointees such as Option<&[u8]>.
* For tagged enums whose None leaves payload bytes unconstrained (modeled by taggedLooseLayout with at least one payload byte) Canonical fails and nonzero patterns can also decode to None.
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc`**

* If numInvalid V = 0 the hypotheses are unsatisfiable (le_numInvalid_of_decEnc_of_size_le), so the statement is vacuous there.
* Canonical decoding is not assumed but is forced by hsize, hV and hde (opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc); the theorem is that result combined with dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical. Its depth is shallow although its final proof is a two-step composition: the canonicity step is the counting (pigeonhole) argument of opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc.
* Does not apply to Option<&T>, Option<Box<T>>, Option<NonNull<T>>, Option<fn()>, Option<bool>, or payloads with padding (e.g. #[repr(C)] struct S(NonZeroU8, u16), where patterns differing only in padding bytes denote the same value): none of these is modeled by a validity set with numInvalid V <= 1.
* Soundness of a validator that accepts only all-zero bytes as None (such as zerocopy's pointer::is_zeroed for Option<&T> and the other pointer options) needs only the <- direction (zero decodes to None), which follows from hnone and hde alone; it needs neither this theorem's -> direction nor canonical decoding, and this theorem does not apply to those pointer options.
* Does not depend on zero being the payload's niche: only numInvalid V <= 1 and None -> 0 are used (documented_niche_identity_not_needed).
* In Rust, hnone (None -> [0u8; size_of::<T>()]) is documented only by core::option's zero-bytes bullets (always for NonZero* and fn pointers; for Box<U, Global>, &U, &mut U and NonNull<U> only when U: Sized). core::result does not state it for Result<T, E> with a 1-ZST: for pointer-like Result<T, ()> it is undocumented, and for Result<NonZero*, ()> it is available only as the in-model derivation from the t -> Ok(t) transmute and decode-after-encode (nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc). User-defined option-like enums and enums with explicit repr(C)/repr(u*)/repr(i*) have no documented niche guarantee.
* Does not say what nonzero patterns decode to (needs DecSomeTransparent; see nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc).
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`opt_fromBytes_and_zero_iff_none_of_nichePinned_zero_of_numInvalid_le_one_of_decEnc`**

* If numInvalid V = 0 the hypotheses are unsatisfiable (le_numInvalid_of_decEnc_of_size_le), so the statement is vacuous there.
* Neither conjunct uses that the payload's niche is the zero pattern: documented_niche_identity_not_needed exhibits a payload whose only niche is 1, a lawful layout pinned at zero, and both conclusions.
* The two conjuncts have different minimal hypotheses: FromBytes does not use the None component of hpin (opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc), the second conjunct is dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc; each tightness counterexample falsifies one conjunct. This theorem is their conjunction. Its depth is shallow, not definitional: both conjuncts rest on the counting argument of opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc, and the same convention labels dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc shallow.
* Does not say what a nonzero pattern decodes to.
* Does not establish zerocopy's IntoBytes or Unaligned: the model has no uninitialized or padding bytes and no alignment (Option<NonZeroU32> has alignment 4); IntoBytes for Option<NonZero*> additionally needs that none of its values contains uninitialized bytes.
* Does not apply to user-defined option-like enums, enums with explicit repr(C)/repr(u*)/repr(i*), or Option<UnsafeCell<NonZero*>>, for which NichePinned is not documented (or false). For Result<T, E> with a 1-ZST, core::result documents the size component of NichePinned but not its None component (zero bytes <-> the dataless variant); for Result<NonZero*, ()> that component is derived inside the model, from the t -> Ok(t) transmute and decode-after-encode (nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc), and this neither establishes nor refutes that Rust's Result<NonZero*, ()> puts the dataless variant on the zero pattern.
* Says nothing about payloads with more than one invalid pattern (references, Box, NonNull, fn pointers, bool).
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc`**

* Specific to payloads with exactly one niche; for bool-like payloads None's pattern is not forced (opt_bool_none_pattern_not_forced_by_someTransparent_lawful).
* Shows that in the model the None -> 0 guarantee for NonZero is derivable from the t -> Some(t) transmute, not that Rust documents it this way; the Rust 1.89.0 docs state only that this transmute is sound, so the derivation is not available from them.
* Does not apply to pointer-like payloads (Option<&T>, Option<Box<T>>, Option<NonNull<T>>, Option<fn()>): they have many invalid patterns, so None -> 0 is not derivable this way and is a separate documented guarantee (for U: Sized).
* Applies in Rust only where the guarantees it instantiates (the payload's size and the value-preserving transmute t -> Some(t)) are documented: Option<T> for T in the core::option Representation list, or Result<T, E> with a 1-ZST, for which core::result documents the same size and the t -> Ok(t) (or t -> Err(t)) transmute but not Option's zeroed-None guarantee; user-defined option-like enums and enums with explicit repr(C)/repr(u*)/repr(i*) have no documented niche guarantee.
* At n = 0, nonZeroV 0 is the empty validity set (not a NonZero integer) and DecSomeTransparent holds vacuously; the statement still holds there.
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc`**

* Depends on the value-preserving transmute t -> Some(t) (DecSomeTransparent), stated in the core::option docs at the pinned nightly commit; under the Rust 1.89.0 docs, which state only that the transmutes are sound, permLayout (None -> 0, Some 1 and Some 2 exchanged; lawful) is not excluded.
* Does not extend to Option<&T> etc.; their validity sets are not nonZeroV n in this model.
* Does not establish zerocopy's IntoBytes or Unaligned: the model has no uninitialized or padding bytes and no alignment (Option<NonZeroU32> has alignment 4); IntoBytes for Option<NonZero*> additionally needs that none of its values contains uninitialized bytes.
* Does not apply to Option<UnsafeCell<NonZero*>> (UnsafeCell disables niches), to user-defined option-like enums, or to enums with explicit repr(C)/repr(u*)/repr(i*); none of these has a documented niche guarantee.
* Byte order (which integer a pattern denotes) is outside the model; patterns are little-endian values by convention.
* At n = 0, nonZeroV 0 is the empty validity set (not a NonZero integer) and DecSomeTransparent holds vacuously; the statement still holds there.
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`opt_bool_lawful_layouts_in_one_and_two_bytes`**

* Does not say rustc does or will make Option<bool> two bytes; the observed size is 1 on the recorded compiler (lean/support/niche_probe_output.txt), and no documented Rust guarantee forbids a 2-byte layout.
* Validity plus lawfulness do not fix the size of Option<NonZero*> either (nonZero_lawful_layouts_in_one_and_two_bytes: a 1-byte and a 2-byte lawful layout of the 1-byte NonZero option); Option<NonZero*>'s size is fixed only by the documented guarantee.
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`opt_bool_none_pattern_not_forced_by_someTransparent_lawful`**

* Does not say that rustc's choice (observed None = 0x02 for Option<bool>) will change; only that it is not derivable from validity.
* Escape hatches: a payload with exactly one niche (the positive control pc_nonZero_none_pattern_forced, NonZero) or an explicit documented None pin (NonePinned, as the core::option docs give for the listed pointer and NonZero types) defeats this impossibility.
* Does not imply that Option<bool> is FromBytes: with canonical decoding only three of the 256 patterns decode (shown for the observed layout nicheLayout boolV 2 by opt_bool_nicheLayout_not_fromBytes; the general count is not proved here).
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`nicheLayoutK_lawful_iff_injective_and_isNiche`**

* Concerns the specific decoder of nicheLayoutK (tags looked up first).
* Models only dataless extra variants (ExtEnum k V = Fin k ⊕ Val V); enums with several data-carrying variants are out of scope (rustc can also fit small data-carrying variants around a niche, try_fit_variants_around_niche_tag).
* Does not mean rustc can use any injective niche assignment: rustc reserves a contiguous run of values outside one scalar's wrapping valid range, sized by the variant-index span of the variants that need encoding.
* Does not by itself give FromBytes: a niche that is not a tag decodes to nothing.
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`le_numInvalid_of_decEnc_of_size_le`**

* Model niches include every invalid initialized pattern, which can exceed what rustc uses: UnsafeCell<NonZero*> (niches disabled), char (the 2048 surrogates 0xD800..=0xDFFF are invalid but inside char's scalar valid range 0..=0x10FFFF), and multi-field payloads such as (bool, bool) (65532 invalid patterns, but only one field's 254 out-of-range values are used: observed sizes 2 and 3 for 254 and 255 extra dataless variants, lean/support/niche_probe_output.txt).
* ExtEnum k V models k inhabited dataless variants. Uninhabited extra variants carry no value and need no niche: size_of::<Result<u8, Infallible>>() == 1 on the recorded compiler although u8 has no invalid pattern (rustc gives no discriminant value to such 'absent' variants).
* Escape hatches in the model: a layout larger than the payload (pc_le_numInvalid) or dropping DecEnc (ce_le_numInvalid_drop_decEnc) defeats the bound.
* Does not apply to payloads with padding (such as #[repr(C)] struct S(u8, u16)), where several initialized patterns denote one value, so values and valid patterns are not in one-to-one correspondence.
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches`**

* Existence of a lawful layout does not mean rustc uses it (rustc's niche is the complement of a scalar valid range and rustc may prefer a tagged layout of equal size).
* Model niches include every invalid initialized pattern, which can exceed what rustc uses: UnsafeCell<NonZero*> (niches disabled), char (the 2048 surrogates 0xD800..=0xDFFF are invalid but inside char's scalar valid range 0..=0x10FFFF), and multi-field payloads such as (bool, bool) (65532 invalid patterns, but only one field's 254 out-of-range values are used: observed sizes 2 and 3 for 254 and 255 extra dataless variants, lean/support/niche_probe_output.txt).
* Even when k <= numInvalid V and rustc does niche-fill (e.g. Option<Option<bool>>, observed size 1), Rust documents no such layout outside the Option/Result guarantees.
* The direction from a lawful layout to k <= numInvalid V concerns inhabited extra variants only; uninhabited variants (Result<u8, Infallible>) need no niches.
* Only dataless extra variants are modeled; enums with several data-carrying variants are not covered.
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

**`opt_opt_nonZero_no_decEnc_layout_in_payload_size`**

* Rules out only size n; it does not say rustc uses n + 1 bytes (observed: Option<Option<NonZeroU8>> has size 2 on the recorded compiler, lean/support/niche_probe_output.txt).
* Escape hatches: one more byte (pc_opt_opt_nonZero), a single level of Option (pc_opt_nonZero_one_level), or dropping DecEnc.
* Does not mean Option<Option<T>> always exceeds size_of::<T>(): a payload with two niches leaves room for two dataless values in its own size. The supporting witness opt_opt_two_niches_one_byte states exactly Lawful (nicheLayoutK geTwoV geTwoTags) ∧ numInvalid geTwoV = 2, i.e. a lawful 1-byte layout of ExtEnum 2 geTwoV (two dataless variants tagged 0 and 1 beside the one-byte payload whose valid patterns are 2..255) for a payload with exactly two niches; it is stated for ExtEnum 2 geTwoV, not for Option (Opt geTwoV), and no theorem transports it along a bijection between the two types. Observed, not derived: size_of::<Option<Option<bool>>>() == 1.
* Says nothing about which patterns are valid for Option<Option<NonZeroU8>> in its observed 2-byte layout; that layout is not documented, and no documented guarantee makes the type FromBytes or FromZeros. In the model, 257 values in 65536 patterns rule out FromBytes only together with canonical decoding (optOptNonZero_two_bytes_not_canonical_and_fromBytes); without Canonical a 2-byte layout satisfying DecEnc and FromBytes exists (optOptNonZeroTwoByteLoose_decEnc_fromBytes_not_canonical, which decodes every surplus pattern as the outer None).
* The model has no uninitialized bytes, no pointer provenance, no alignment, no padding and no safety invariants; payload values are identified with their unique byte patterns.

### Escape hatches of the impossibility results

* `isNiche_enc_none_of_decSomeTransparent_of_decEnc` (None must sit on a niche): dropping
  `DecSomeTransparent` admits the lawful `swapLayout` with `None ↦ 1`, a valid pattern
  (`ce_isNiche_enc_none_drop_decSomeTransparent`; positive control `pc_isNiche_enc_none`);
  dropping `DecEnc` admits `noneLostLayout` (`ce_isNiche_enc_none_drop_decEnc`). Encoder-side
  transparency alone is not the right hypothesis: with `DecEnc` it implies
  `DecSomeTransparent`, but not without it.
* `opt_bool_none_pattern_not_forced_by_someTransparent_lawful` (no `None` pattern is forced
  for `bool`-like payloads): for a payload with exactly one niche the pattern *is* forced
  (`pc_nonZero_none_pattern_forced`); what defeats forcing is having at least two niches.
* `le_numInvalid_of_decEnc_of_size_le` (`k ≤ numInvalid V`): one more byte than the payload
  (`ce_le_numInvalid_drop_size`; positive control `pc_le_numInvalid`), dropping
  decode-after-encode (`ce_le_numInvalid_drop_decEnc`), uninhabited extra variants (not modeled; observed
  `Result<u8, Infallible>` of size 1), and data-carrying extra variants fitted around a niche
  (not modeled).
* `opt_opt_nonZero_no_decEnc_layout_in_payload_size`: one more byte (`pc_opt_opt_nonZero`), a
  single level of `Option` (`pc_opt_nonZero_one_level`), a payload with two niches
  (`opt_opt_two_niches_one_byte`, stated for the enum with two dataless variants
  `ExtEnum 2 geTwoV` in 1 byte, not for `Option (Opt geTwoV)`), or dropping `DecEnc`.

### Hypotheses with `unknown` tightness

None. Every hypothesis of every result is `tight`, with a proved counterexample in which all
other hypotheses hold and the conclusion fails; results without hypotheses are equivalences
or closed statements.

### Disproved or dropped statements

None. Every result stated in the package is proved, and none was found false or dropped for
lack of a proof. Two facts are kept as supporting lemmas in `Toy.Niche.Lemmas` rather than as
result cards: `firstNiches_injective_and_isNiche_of_le_numInvalid` (used by the cardinality
characterization) and `decSomeTransparent_of_someTransparent_of_decEnc` (encoder-side
transparency plus decode-after-encode implies decoder-side transparency). The counting
lemmas in `Toy.Niche.Counting` (duplicate-free lists, the valid/invalid partition of all
`256 ^ n` patterns) serve only the proofs.

### Not examined

* Uninitialized bytes, padding, alignment, pointer provenance, and safety invariants (outside
  the model).
* Payloads with several data-carrying variants, uninhabited variants, `#[repr]` attributes on
  user enums, and generic or `#[repr(transparent)]` wrappers (only through the documented
  list quoted under Applicability).
* Pointer-like payloads (`&T`, `Box<T>`, `NonNull<T>`, `fn`), including unsized pointees.
* Targets, compiler versions and flags other than the single recorded rustc build; the
  execution cross-check says nothing about other builds.

### Attractive stronger conclusions that are not established

* "`Option<NonZeroUN>` is `FromBytes` because `NonZero` has only one invalid pattern." Not
  from validity alone: the counting argument also needs the documented same-size guarantee
  (`ce_canonical_fromBytes_drop_size`) and decode-after-encode, and it covers only
  initialized bytes.
* "Any option-like enum over a one-niche payload puts `None` on that niche." Only with the
  documented same-size and transparency facts, which Rust documents only for the listed
  types; not for user-defined enums, enums with explicit `repr`, or `UnsafeCell` payloads.
* "rustc's layout of `Option<bool>` (or of any enum) is determined by validity." It is not:
  `opt_bool_none_pattern_not_forced_by_someTransparent_lawful` and
  `opt_bool_lawful_layouts_in_one_and_two_bytes` show several lawful layouts.
* "`k ≤ numInvalid V` predicts rustc's enum sizes." It is only a necessary condition in the
  model; rustc may use fewer niches than the model counts.
* "The model's results hold for Rust." Every such statement is a `derived (modeling bridge)`
  claim with its own assumptions, stated under Findings.

## Evidence

### Kernel-check records

Toolchain: Lean `v4.34.1` (`leanprover/lean4`, tag commit
`5045d0056413266e57c625dcd7c365b10e377c52`), core library only; no Mathlib and no other
dependency (`lean/lakefile.toml` has a single `[[lean_lib]]` named `Toy` and no `[[require]]`).
The library builds with `lake build` and contains no `sorry`, `admit`, `native_decide`,
`axiom`, `opaque`, `implemented_by`, `@[extern]`, `unsafe` or `debug.skipKernelTC`. Every
declaration of the library (271 declarations, recorded in `audit/axioms.json`) depends only on
a subset of `propext`, `Classical.choice`, `Quot.sound`.

Modules: `Toy.Niche.Defs` (definitions), `Toy.Niche.Lemmas` (supporting lemmas),
`Toy.Niche.Counting` (finite counting lemmas used only inside proofs), `Toy.Niche.Results`
(the 15 results), `Toy.Niche.Witnesses` (definition examples, counterexamples, non-vacuity
theorems, positive controls, and the two-level-option witnesses
`optOpt_card_bound_of_canonical_of_fromBytes` (the counting bound
`256 ^ m + numInvalid V ≤ 256 ^ n + 2` for canonical layouts of `Option (Opt V)` in which
every pattern decodes),
`optOptNonZero_two_bytes_not_canonical_and_fromBytes`,
`optOptNonZeroTwoByteLoose_decEnc_fromBytes_not_canonical`).

For every declaration referenced by a result card, the table gives the axioms reported by
`Lean.collectAxioms` and two SHA-256 hashes, copied from `audit/statements.json`: the
**statement hash** is the hash of `toString (repr ci.type)` (the Lean `repr` of the
declaration's type), and the **closure hash** is the hash of the newline-joined, sorted list
of `name : repr type [:= repr value]` entries for every constant of the `Toy` library
reachable from that type through types, definition values (theorem proofs excluded) and
inductive constructors; the number in parentheses is the size of that closure. A change to a
statement, or to any definition it depends on, changes one of the two hashes.

| Declaration | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `nicheLayout_lawful_iff_isNiche` | result | propext | `1b7b47f6a0b1af6bc90898634cf52d5d732c0d41fe36a550948ae077e1bd7c28` | `e9e266f21a645775adcd2f1ff242b358af73c67ea3bdb5aa80153ac3b2af8199` (14) |
| `isNiche_enc_none_of_decSomeTransparent_of_decEnc` | result | none | `6ba77c437a122718bb46f1de8a7eb6aa2818f8f1e2c3c45cb27eb731ae882eee` | `375e6a5da414f979fe0e65542e28c954e703406ed30f98841e090b166555be6d` (11) |
| `someTransparent_lawful_iff_eq_nicheLayout` | result | Quot.sound, propext | `a13411272f7f8c62487bc330e4cac312c2b2803c1396cda8c342f4216ac95f6c` | `1b4a216fa69e1a8e5c9a3e53c6f345ce861c0ac556f5f4367d54174a4c12717c` (15) |
| `opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc` | result | Classical.choice, Quot.sound, propext | `51381a8fdeb0fdafbd2c81c8af62671d4ed10d8d60da1d5b1e0bacc71ff06a7c` | `22d7aaf4e60206089358d0d781e80df32a5f2ed8308c046de1b061982f2fb897` (13) |
| `dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical` | result | none | `325011828fc6d5cb0aa5a895071b963cd9dc0dec77751f8def88a2b347397cf7` | `6fe246c382eaaf87a6a701a51cc7582433ba2996385b0d8c9f88b824a9e11beb` (10) |
| `dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc` | result | Classical.choice, Quot.sound, propext | `436fb7e487b81e91c51a426aa080fff4490659ee8f740bd4c0eceac289990d29` | `70ba5043a820c6408ca8e826d78fc1a82b2655be86979990302d44602c17a869` (14) |
| `opt_fromBytes_and_zero_iff_none_of_nichePinned_zero_of_numInvalid_le_one_of_decEnc` | result | Classical.choice, Quot.sound, propext | `18848099ac703c92e94b7dbdedab438bcb473a5ef7f9743e50b389dfa538105b` | `60caca0477f225fe096c62a64f1410b7ae9e5d5fba35998821698da73afe8be7` (16) |
| `nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc` | result | Quot.sound, propext | `5cac77e6609c768115d69476e94698bc29191adb9f73932c6a2e0d677a0df9ae` | `58dfbaf5188eb56ebaf97f8ee12f4e5287de4f9819d20bf7339ec8a8fb9e693d` (14) |
| `nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc` | result | Quot.sound, propext | `7a7c4e20041051636906dde2a2015a27709dbf550feebafd42b7be606999668b` | `543fbb4d855471c8785905f348cc5bdb30f4d7906e6b31a69f994339d64ed616` (15) |
| `opt_bool_lawful_layouts_in_one_and_two_bytes` | result, non-vacuity | Quot.sound, propext | `31971b2f04fc018b93011b54efca8f9f7f43f0a9408cba368536f52d2aa4a128` | `7460317fdb63533b4f130110e2789f16edb13efe3fc3cccfa48441303e47745c` (22) |
| `opt_bool_none_pattern_not_forced_by_someTransparent_lawful` | result | propext | `dfba35d8e2a2342afcd5a60878a9a6a056fa6a6bca46d5212b713e464c7d4757` | `17760db206073ca221faaf226d71e1ea842da7609f76b57282c2c31e5d34ef6c` (14) |
| `nicheLayoutK_lawful_iff_injective_and_isNiche` | result | Classical.choice, Quot.sound, propext | `9565e9b33b2efbb9451fb1d13a869b4912493e1489a586c55a9dc51cb3b4de8a` | `6f42490b79695bd2f08899fae90e2f5878f4ba071cb354752de56f25cfb3f625` (15) |
| `le_numInvalid_of_decEnc_of_size_le` | result | Classical.choice, Quot.sound, propext | `feee00b2c9087d5f3fee362c10b0ad453d582f86d075726c9ffbf77b77382343` | `84b3c2c218f5025aff3428e873cce562b2ee5dca2eef8cee63e988f83b7c3ceb` (11) |
| `le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches` | result | Classical.choice, Quot.sound, propext | `df473d7fbefce56902691e0461cbcf15dd4b80076a1168e5b5d8373d615ebca8` | `0d6d1481bbdb0113986a334f6daa89f69d50227339223aca26437d62c90d0d89` (19) |
| `opt_opt_nonZero_no_decEnc_layout_in_payload_size` | result | Classical.choice, Quot.sound, propext | `cb39a0bea33e2448cdd68d5b1ddfaec07abf14738a29779d17ac26106ff2d17f` | `3daca916a964928ea69b7b5d06f5815e1f974d3e92a081b749474ac54d48c1c2` (10) |
| `ce_canonical_fromBytes_drop_decEnc` | counterexample (hde) | Classical.choice, Quot.sound, propext | `84440564d9d1cff1fb26f0fac5710ea395c01f5ce6911ffcde02aca48024d8c3` | `f998dc22553295f89ac1efa7f7a8d1784db74a19fefcdc3ae2bc34100335a91d` (19) |
| `ce_canonical_fromBytes_drop_numInvalid` | counterexample (hV) | propext | `5707b193e3041a0b7ab3ca3978ad01e5714828e3c06661c726731cbe43f48a81` | `aee851bd6cf33276a372e548828ff2f42852f76595db90d38d140be1f840329e` (18) |
| `ce_canonical_fromBytes_drop_size` | counterexample (hsize) | Classical.choice, Quot.sound, propext | `2e6279a255617aed7cd45d4be509d6ab5056fc9f02bb5855f932685267151352` | `34ff09f50d4c5cf956c446c3de3d96f98aaf9ddd0a46be5ecd41079355e033e6` (20) |
| `ce_documented_drop_decEnc` | counterexample (hde) | Classical.choice, Quot.sound, propext | `1cb364af5942a8001601db3ab5769bf18848ab732876f54cca768c93288bb8d1` | `ad4ff7e884ac93f540719517c9f129ae6267504e4bb601639022a8b338aed301` (20) |
| `ce_documented_drop_none_pin` | counterexample (hpin) | Classical.choice, Quot.sound, propext | `54d0900594b96c65e6db8f1ce1ead87070eff67da7cad3626669463865fb7040` | `5c2e39e3be043c92ad894db0a0f6796cd86a0decfe4fd21ede91880942e98ec8` (21) |
| `ce_documented_drop_numInvalid` | counterexample (hV) | propext | `43eea28657f6a2f59918a795131bd858293192008886f720fab4e422a7b1fde1` | `5927886069610e43986cca3749e06b8750a9002a81622f5b23dc4df48936ec2c` (19) |
| `ce_documented_drop_size_pin` | counterexample (hpin) | Classical.choice, Quot.sound, propext | `43bd9cc6380c30bd4dec81f5280b200d9641ff41641b43200d2554b1b8f98311` | `483ef8c0040e0ffc7e6aaf1c6c2aa6c2bd5c74feb76c7a61283c708150d25833` (20) |
| `ce_isNiche_enc_none_drop_decEnc` | counterexample (hde) | none | `e121f8d3b72a563fa1f7f7fb3a30c294bb7640e3581064343cfd0cd851263ef2` | `bd2defe5252796afca8fd49a9fb6fd21afd5990f7bbb5ca1197e27d5e1e38b49` (15) |
| `ce_isNiche_enc_none_drop_decSomeTransparent` | counterexample (hdst) | propext | `c233aa5ecd8833ca1ccea3d00b39feab50bb5a6b45c1af3beb3249b3c84b8b15` | `72e8a374972a61253d9a0c726e86890864dfa2efc893ac5b035679f94eecaa2e` (17) |
| `ce_layout_determined_drop_decEnc` | counterexample (hde) | none | `ab93412219f3e993ca6b3d12fc279c305b546492e548a92971d19704ba1a3413` | `a02d03b5f05a0d3923e9253abf5f3b8dca0e699030b85a62bbb2f4cd8e12c63c` (18) |
| `ce_layout_determined_drop_decSomeTransparent` | counterexample (hdst) | propext | `ef85d3a763a01e170b38d14dad3980294633cdda1550cf356b270e5ead43df83` | `a092e0a06dbd9a3e613b624a408c8f222e608f5d74132ff1ccf84765442a38c5` (19) |
| `ce_le_numInvalid_drop_decEnc` | counterexample (hde) | propext | `2a11df0fcec837fe0db55af3e750739471b329b43aa413e2d14f22474999d134` | `e85015b9ebdf31017d2c0726c32587935de8bcdf5aa4152f451e266ae26ee6a8` (15) |
| `ce_le_numInvalid_drop_size` | counterexample (hsize) | Quot.sound, propext | `fb4e9e632ca158699cd96b4e4ae30c3446471b6752036c16fc88167bc05bd963` | `5d4a33fe2c156f1175c8b61be29add91cb94a17c1851a82c6952d2ad1043015d` (27) |
| `ce_nonePinned_zero_drop_decEnc` | counterexample (hde) | none | `71ffe6b5f20c7147def6bdfbe490166882df0aa08a184db1396ac68dcd380fba` | `2d1219bf880f7c8c6908fd1a2d90e59170fbe72dc9fac9cacbac008058bff591` (17) |
| `ce_nonePinned_zero_drop_decSomeTransparent` | counterexample (hdst) | propext | `e82c51f05e7fbd2b23f2a177f805b0b2bebfef060606fb93c7b919f355e8915d` | `40e3180848d83a5e4e64b86f210e651c8a1245947f2485a677ba412ef40e5b2d` (19) |
| `ce_zero_iff_none_drop_canonical` | counterexample (hcan) | none | `141c717b6bc0fcf40abfb5edf4939ec40a998a6c58124791c8aba4b65022d14c` | `3aaa0331601965e2c95f2973b65ecb96cb41cdd6198949f51ee1149b5e816204` (18) |
| `ce_zero_iff_none_drop_decEnc` | counterexample (hde) | Classical.choice, Quot.sound, propext | `8442539f05b956390a13a9f510a8e8919ab2bee6cb3e78c7ba073025a508ea89` | `e33dffd0c9021b4b7423bd1fb81cffea1e4059e3a87edcb3093b284c013af419` (19) |
| `ce_zero_iff_none_drop_nonePinned` | counterexample (hnone) | Classical.choice, Quot.sound, propext | `37639ab2a064e5ee346d9f463dec5a2fcdda7143f0c003d3b9e3f62c87b99fef` | `b48f72a63776101e7ab1e502453a8925103d09b73f53f285d8ff59fad9a5c4ed` (22) |
| `ce_zero_iff_none_drop_numInvalid` | counterexample (hV) | none | `dbb5a47a1a033ea2711f5a8bc240c7fb4d9d6c8a33ad8bf4fe89a4a97a1c2bc2` | `80085fc58c57dc2e9b689e6bd7a60e67a89b6799a5eb26f29e9309b9dba3023b` (19) |
| `ce_zero_iff_none_drop_size` | counterexample (hsize) | Classical.choice, Quot.sound, propext | `dbb907b2a953c6237756e2ea56e4127ce6a54f4f3b2b7f281d76fe6ad50142e8` | `dc8dfc4b8c2c33dc4b7f3dedbf898f4678b86ccefc79365ba75eaaefc8e100b6` (20) |
| `nv_decSomeTransparent_decEnc` | non-vacuity | Quot.sound, propext | `7a00a19d2fa0c037baf8e8c13f6b13d68089bbcf172d32ecf16c6e0ed5ffd066` | `543fbb4d855471c8785905f348cc5bdb30f4d7906e6b31a69f994339d64ed616` (15) |
| `nv_documented` | non-vacuity | Classical.choice, Quot.sound, propext | `91a85223236161014fa812a2d62e9624531c7c9f6a3ab795d9d7ef203aeac31b` | `c82d1fb328e0a3bb46e0eecf78ef9a258d1e3b75119dce9e21db70848232fbc2` (18) |
| `nv_isNiche_enc_none` | non-vacuity | Quot.sound, propext | `7a00a19d2fa0c037baf8e8c13f6b13d68089bbcf172d32ecf16c6e0ed5ffd066` | `543fbb4d855471c8785905f348cc5bdb30f4d7906e6b31a69f994339d64ed616` (15) |
| `nv_le_numInvalid` | non-vacuity | Quot.sound, propext | `0b57e525bddbe9f5cee51a7636f91e20bc93d31bd61e181d3d26580b21b32bdd` | `4794a842d064f946ea436f987b78047cbb6b1f6357eea9d0be75a875e2ad0c67` (21) |
| `nv_le_numInvalid_iff` | non-vacuity | propext | `c11b4aa4e6978a11f7e6098f319c177b3d8f0a17fbd9c2d75bc9a01f08c93f33` | `b1ba8a5c8b3e5b7a8b3bece9255a34c3caa0a482f603a93c8032d48e738acff9` (20) |
| `nv_nicheLayoutK` | non-vacuity | propext | `b858259e4b9a2f7da49730d0bd284f70ef189c19a04da2cc044a7a43ebb261a7` | `1987ef5b09547f2100e8e1dc176381e8541a3f79aa929ead71c8066cc99bc854` (18) |
| `nv_nicheLayout_lawful_iff_isNiche` | non-vacuity | Quot.sound, propext | `1714864db82561664332f6cae4496cfd86b6efa6ce440b1d2a7bd2560f0e688b` | `aee3695fa6047b23c26471d797a14ac8dc4d23a3509b4a1f17eb51bf4ab9c2df` (17) |
| `nv_opt_bool_none_pattern_not_forced` | non-vacuity | Quot.sound, propext | `c7a8a5eb45e371cd9119a837fc2e1de9757341fb82638bab70c115d58d7799bb` | `e8d7e5314e93d06685dd5d1dc0196670a23fee3e70922c3da430e620280724cd` (16) |
| `nv_opt_canonical_and_fromBytes` | non-vacuity | Classical.choice, Quot.sound, propext | `68ce0cb36c7deed7616dcec3fc35bf0ac8dc403a19525f251317db253b53f98d` | `e7d20d404c3ec7903c2219716b960d60cfec58b944a34e603675fac0a04ac46c` (16) |
| `nv_opt_opt_nonZero` | non-vacuity | none | `adee6ac48a21c216f2ee8acc75f4d76e0b445b3c95fa535058b0f6f8bec1d19e` | `57e37a878a1590c519dbefbb2066f4ad9690207d5b0908fa980325f529a02fbf` (7) |
| `nv_someTransparent_lawful_iff_eq_nicheLayout` | non-vacuity | Quot.sound, propext | `6b39e18eb70da9816898c547a894ebc75a05613412fb48f9eaf865e4c6a611a5` | `6ab948e693b15036ad0f513b7ea64888c41b373bc977e7888a774c882b261337` (18) |
| `nv_zero_iff_none_lawful` | non-vacuity | Quot.sound, propext | `9ce791d4dba3fb00c45b3114aff835e28f98a7e4cc1a5202e5174b4802c4767f` | `233a8a812db9bbf9ee1fe3c2bdfe8e172318b3dbf2e238b8c1e717e6dba469fa` (16) |
| `nv_zero_iff_none_size_numInvalid` | non-vacuity | Classical.choice, Quot.sound, propext | `8649afc7d19bc0ca6ee840ad02150705333aad8ac55c2e8a6bcfaa278dbc0075` | `0c8b15d84b6a6d120d2c9952880813cb3ee0e4785e4845b174b61e98afa6d584` (17) |
| `pc_isNiche_enc_none` | positive control | propext | `059897d42611b41c17ce8c8f786e93db9797de7af9688bf1a306c7c7b22f26c0` | `de5fd3de32f4c1ff07b73b35e801e09a783b7757625714e0a88f545157a5157a` (18) |
| `pc_le_numInvalid` | positive control | Quot.sound, propext | `42ae2cdeb7eb8b2bd32eec7934a86cefb477d087f920565f8403f859284fd967` | `92150715b33d25ca35104ceda2527428007d9ac0031403350f7121b74242da5e` (29) |
| `pc_nonZero_none_pattern_forced` | positive control | Quot.sound, propext | `708e5952f02f6bdd50ed1414883961dd41857d2eab4ba14f6f0429c867080513` | `2a15aa60e628403fbe0df005ba85727a8c3f79df9f5ee9790513bf6d728200a7` (16) |
| `pc_opt_opt_nonZero` | positive control | Quot.sound, propext | `6d139bd80077606c152069eb9052edba8533fe08303d2e89c4fc156ab1e7f849` | `45381cac6e648f9e16038f44d2a4da02057f914618d0861bf2d609cff557da3a` (20) |

### Execution evidence (rustc probe)

* Program: `lean/support/niche_probe.rs`; command: `rustc -O niche_probe.rs` and running the
  resulting binary; output preserved byte-for-byte in `lean/support/niche_probe_output.txt`
  (quoted under Findings).
* Compiler: `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, commit-hash
  `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, host `x86_64-unknown-linux-gnu`, LLVM 23.1.5
  (`lean/support/rustc_version.txt`).
* Observed on 2026-11-20. This is evidence about one compiler build on one target, not a
  language guarantee; the lines marked "observed; not guaranteed" are exactly the values the
  results say cannot be derived from the documented guarantees.

#### Primary sources (prior-art records)

Each record below is quoted exactly as in `results.json`; all were checked at the stated revisions on 2026-11-20.

* **[S1]** Rust core library docs, module core::option, section 'Representation', rust-lang/rust commit 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1, library/core/src/option.rs lines 116-158: for the listed T (Box<U>, specifically only Box<U, Global>; &U; &mut U; fn and extern "abi" fn pointers including unsafe variants; num::NonZero*; ptr::NonNull<U>; #[repr(transparent)] structs around one of these), Option<T> has the same size, alignment and function call ABI as T, and transmuting t: T to Option<T> produces Some(t) and transmuting Some(t) to T produces t. 'In some of these cases' Rust further guarantees that transmuting [0u8; size_of::<T>()] to Option<T> produces None and None to bytes produces [0u8; size_of::<T>()]; the table's second column restricts this to U: Sized for Box<U, Global>, &U, &mut U and NonNull<U>, gives it always for fn pointers and NonZero*, and for #[repr(transparent)] wrappers when it holds for the inner type. Rust 1.89.0 (tag 1.89.0, library/core/src/option.rs section 'Representation' from line 119; https://doc.rust-lang.org/1.89.0/core/option/index.html#representation) has the same table and zero-bytes bullets but states only that the transmutes are sound, not that t becomes Some(t) and Some(t) becomes t.
* **[S2]** Rust core library docs, NonZero<T> 'Layout', rust-lang/rust commit 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1, library/core/src/num/nonzero.rs lines 81-89: 'NonZero<T> is guaranteed to have the same layout and bit validity as T with the exception that the all-zero bit pattern is invalid'; NonZero<T> and Option<NonZero<T>> have the same size and alignment.
* **[S3]** Rust core library docs, module core::result, section 'Representation', rust-lang/rust commit 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1, library/core/src/result.rs lines 232-258: Result<T, E> has Option's size, alignment and ABI guarantees (and the Ok(t)/Err(t) transmutes) when one of T, E qualifies for Option's representation guarantees and the other is a zero-sized type with alignment 1. The section does not state Option's zeroed-None guarantee ([0u8; size_of::<T>()] <-> None) for Result, and RFC 3391 (line 36) grants only 'the same layout (size and alignment) and the same ABI as the primitive form of the data'. The Rust 1.89.0 section (tag 1.89.0, library/core/src/result.rs from line 231) says only that Result<T, E> 'will gain the same size, alignment, and ABI guarantees as [`Option<U>`] has', with no transmute sentence, and also requires the 1-ZST to have no fields and not to be #[non_exhaustive]. RFC 3391 'result_ffi_guarantees', rust-lang/rfcs text/3391-result_ffi_guarantees.md at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 (the last change to the file), line 94: the guarantees 'could be extended to *all* similar enums in the future', but without an opt-in 'it becomes yet another semver hazard for library authors' and the RFC 'is deliberately limited in scope'. User-defined option-like enums therefore have no documented niche guarantee.
* **[S4]** Rust core library docs, UnsafeCell<T> 'Memory layout', rust-lang/rust commit 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1, library/core/src/cell.rs lines 2221-2233: UnsafeCell<T> has the same in-memory representation as T, but 'UnsafeCell disables niche optimizations' (Option<NonNull<u8>> is typically 8 bytes on 64-bit platforms while Option<UnsafeCell<NonNull<u8>>> takes 16); compiler/rustc_ty_utils/src/layout.rs lines 713-717 at the same commit select NicheOptimizations::Disabled for UnsafeCell and UnsafePinned. Documentation plus implementation.
* **[S5]** The Rust Reference, rust-lang/reference commit a2ae66d7037cbedac68746b9510b24cc34b96d69, src/type-layout.md rules layout.repr.rust.layout and layout.repr.rust.unspecified (the default representation makes no data layout guarantees beyond those listed, none of which concerns niches), and src/types/boolean.md rule type.bool.repr (bool: 0x00 = false, 0x01 = true, any other bit pattern is undefined behavior).
* **[S6]** The Rust Reference, rust-lang/reference commit a2ae66d7037cbedac68746b9510b24cc34b96d69, src/behavior-considered-undefined.md lines 111-200 (r[undefined.validity]: producing an invalid value is immediate undefined behavior; a bool must be 0 or 1, undefined.validity.bool lines 120-121; a char must not be a surrogate 0xD800..=0xDFFF and must be at most char::MAX, undefined.validity.char lines 126-127). rustc, rust-lang/rust commit 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1, compiler/rustc_ty_utils/src/layout.rs lines 418-424: ty::Char is a scalar with valid_range 0..=0x10FFFF, so the surrogates are invalid values but not niche values. Normative (Reference) plus implementation.
* **[S7]** The Rustonomicon, rust-lang/nomicon commit b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6, src/other-reprs.md line 105: 'Adding an explicit repr(u*), repr(i*), or repr(C) to an enum with fields suppresses the null-pointer optimization'. Descriptive, not normative.
* **[S8]** Unsafe Code Guidelines, rust-lang/unsafe-code-guidelines commit d809f91e62968913d808e53397fbcf7cea762cce, reference/src/glossary.md section 'Niche' (lines 150-163: the niche of a type determines invalid bit-patterns used by layout optimizations; not all invalid bit-patterns are niches). reference/src/layout/enums.md at that commit is archived as not reflecting current layout guarantees; its earlier text (commit c138499c1de03b908dfe719a41193c84f8146883, section 'Discriminant elision on Option-like enums', from line 296) described option-like enums and niche use. Non-normative.
* **[S9]** rustc layout code, rust-lang/rust commit 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1: compiler/rustc_abi/src/layout/enum_layout.rs fn layout_of_enum (lines 15-58; computes a niche-filling and a tagged layout and keeps the smaller, on equal size the one with the larger niche, otherwise the tagged one) and fn calculate_niche_filling_layout (from line 558; line 605 gives no discriminant value to 'absent' variants, i.e. uninhabited variants whose fields are all 1-ZSTs (fn absent, compiler/rustc_abi/src/layout.rs line 90); line 611 counts the variant-index span to encode; lines 613-615 take the largest niche of the largest variant (a single scalar) and reserve that many values via Niche::reserve; line 618 tries to fit the other variants' data around the niche); compiler/rustc_abi/src/lib.rs struct Niche (line 2105), Niche::available (line 2118: number of values outside the scalar's wrapping valid_range) and Niche::reserve (line 2129: fails when count exceeds available; for count == 1 and a valid range other than 0..=1 it takes the free value closest to zero under signed, sign-extended wrapping distance, lines 2165-2174). Implementation behavior, not a guarantee.
* **[S10]** zerocopy, google/zerocopy commit c55af491426ef53f35fb8c6e83f220fa07712e66: zerocopy/src/impls.rs lines 193-254 (NonZeroXxx: IntoBytes but not FromZeros/FromBytes; TryFromBytes validated by NonZero::new), lines 256-295 (Option<NonZeroXxx>: TryFromBytes with no validator, FromZeros, FromBytes, IntoBytes, and Unaligned for the 8-bit ones; SAFETY comment: 'The Rust compiler reuses `0` value to represent `None`, so size_of::<Option<NonZeroXxx>>() == size_of::<xxx>(); see `NonZeroXxx` documentation.'), lines 310-375 (Option<Box<T>>, Option<&T>, Option<&mut T>, Option<NonNull<T>> (with T: Sized) and Option of fn pointers: FromZeros, and TryFromBytes with validator pointer::is_zeroed, which accepts exactly the all-zero bytes); zerocopy/src/lib.rs trait docs: TryFromBytes line 1788 'Types for which some bit patterns are valid.', FromZeros line 3623 'Types for which a sequence of `0` bytes is a valid instance.', FromBytes line 4173 'Types for which any bit pattern is valid.'
* **[S11]** MiniRust, minirust/minirust commit 063d784186d3252bee242217f218223205c0b568, spec/lang/representation.md lines 758-763 (round-trip properties: decode(encode(val)) == Some(val) for well-formed val; decode(bytes) == Some(val) implies encode(val) <= bytes, '<=' allowing bytes to be more initialized); spec/lang/types.md enum Discriminator (line 113); issue https://github.com/minirust/minirust/issues/288 'Enum well-formedness checks don't guarantee the round-trip properties' (open as of 2026-11-20). DecEnc is the first property; Canonical is the second restricted to fully initialized, provenance-free bytes.
* **[S12]** Mitchell Riley, 'Categories of Optics', arXiv:1809.00738 (v2, 2018), section 4.2 'Prisms': the concrete prism laws Matching . Review = inr and [id_S, Review] . Matching = id_S, which suffice in Set (Proposition 4.2.2). With Review = enc and Matching p = inr x if dec p = some x and inl p otherwise, the first law is DecEnc and the second is Canonical: a Lawful layout is a lawful concrete prism from m-byte patterns to the enum's values.
* **[S13]** Ralf Jung, 'Two Kinds of Invariants: Safety and Validity', blog post, 2018-08-22, https://www.ralfj.de/blog/2018/08/22/two-kinds-of-invariants.html: distinguishes the validity invariant, which 'is exploited by the compiler to perform optimizations (e.g. enum layout optimizations)', from the safety invariant. The model's Validity sets are validity invariants over initialized bytes.
* **[S14]** Mathlib, leanprover-community/mathlib4 commit b476d8fd31a353258f27f2e35e8e25b689d6a052, Mathlib/Data/Fintype/Card.lean: Fintype.card_le_of_injective (line 239), Finite.injective_iff_surjective (line 335) and Finite.injective_iff_surjective_of_equiv (line 347): the finite pigeonhole bound and 'an injection between finite types of equal size is surjective', the abstract facts behind this result. This package is Mathlib-free and does not use them.

Additional identity records:

* Rust 1.89.0 documentation: tag `1.89.0` of `rust-lang/rust` is the annotated tag object
  `8b14d85d4e1d87024385e70ac0e1996213c2030a` pointing at commit
  `29483883eed69d5fb4db01964cdf2af4d86e9cb2`; its `library/core/src/option.rs` section
  "Representation" starts at line 119 and reads "Rust guarantees to optimize the following
  types `T` such that [`Option<T>`] has the same size, alignment, and [function call ABI] as
  `T`. In some of these cases, Rust further guarantees the following: ..." (no "producing the
  value `Some(t)`" sentence).
* Riley, "Categories of Optics": arXiv:1809.00738, version 2 (revised 7 Sep 2018), DOI
  `10.48550/arXiv.1809.00738`.
* Jung, "Two Kinds of Invariants: Safety and Validity" ([S13]): a blog post with no DOI or
  other immutable identifier, and this report pins no archived snapshot or source revision of
  the page. Its URL (https://www.ralfj.de/blog/2018/08/22/two-kinds-of-invariants.html) and
  publication date (2018-08-22) are the strongest identity available; the quoted sentence was
  checked at that URL on 2026-11-20 (the report's observation date). If the page changes,
  [S13] may no longer match it.
* The quoted documentation passages for `core::option` and `NonZero<T>` are reproduced in
  `lean/support/README.md` at the pinned commit.

Novelty: no mechanized treatment of these specific statements was found. The tiers are T0
(re-derivation) and T1 (folklore made precise); no result is claimed novel.

## Revalidation

Requirements: `elan` (so that `lake` selects the toolchain pinned in `lean/lean-toolchain`,
`leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is
installed; there are no Lake dependencies.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not
modified) and then:

1. runs `lake build`;
2. rejects any Lean source containing `sorry`, `admit`, `native_decide`, or an `axiom`
   declaration;
3. writes and runs (`lake env lean`) a small Lean audit program that, for every declaration
   of the `Toy` library, computes its axioms with `Lean.collectAxioms` and requires them to be
   a subset of `propext`, `Classical.choice`, `Quot.sound`;
4. for every Lean name referenced by `results.json` (fields `lean`,
   `nonvacuity_witness_lean`, `positive_control_lean`, hypothesis `counterexample`s) and every
   name recorded in `audit/statements.json`, recomputes the SHA-256 of the statement
   (`toString (repr ci.type)`) and of the definition closure (the sorted, newline-joined
   `name : repr type [:= repr value]` entries of every `Toy` constant reachable from the type
   through types, definition values and inductive constructors, theorem proofs excluded), and
   compares both, and the closure size, with `audit/statements.json`.

It prints `ok` or `FAIL` per check and ends with `REVALIDATED` (exit status 0) when
everything matches. Expected summary lines for this package: `ok   lake build`,
`ok   axioms (271 declarations)`, `ok   statement hashes (52 hashed names; 0 referenced
names exist but carry no recorded hash)`, `REVALIDATED`.

**Manual equivalent.** From `lean/`:

```sh
lake build                       # builds the Toy library under the pinned toolchain
lake env lean AxiomAudit.lean    # prints #print axioms for all 52 card-referenced names
```

`lean/AxiomAudit.lean` is outside the library target; every line it prints must be "does not
depend on any axioms" or list only `propext`, `Classical.choice`, `Quot.sound`.

**Re-checking the modeling bridges after a Rust change.** The theorems do not depend on any
Rust revision; the bridges do. The cheapest discriminating checks are: compare
`library/core/src/option.rs` (section "Representation"), `library/core/src/num/nonzero.rs`
(`NonZero<T>` "Layout"), `library/core/src/result.rs` ("Representation") and
`library/core/src/cell.rs` (`UnsafeCell<T>` "Memory layout") of the new revision with the
passages recorded under Evidence; and rerun the probe (`rustc -O lean/support/niche_probe.rs
-o /tmp/niche_probe && /tmp/niche_probe`) and diff its output against
`lean/support/niche_probe_output.txt`. A changed observed size or `None` byte affects only the
observation lines, not any theorem; a changed documented guarantee affects the bridges that
cite it.
