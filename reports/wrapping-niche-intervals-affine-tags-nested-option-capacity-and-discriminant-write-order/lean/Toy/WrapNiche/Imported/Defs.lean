/-
Imported module (not a result of this package).

Copied from the published corpus package `enum-niche-layout-guarantees-and-validity-invariants`
(repository `google/zerocopy`, branch `reference`, published at commit
`00c8f874bf1e70c933b7a2ea2572a76c1baa7327`; Lean sources unchanged at the latest correction
commit `f9bee82a6d3f8bb6698b4c9e716138018db94d4d`), file
`reports/enum-niche-layout-guarantees-and-validity-invariants/lean/Toy/Niche/Defs.lean`,
whose SHA-256 at both commits is
`91c672ae20c64317dd288cb83199123f3add4dc5818f8ed03a590a3eff94d886`.
The only edits are the namespace (`Toy.Niche` renamed to `Toy.WrapNiche.Imported`) and this
header. Declaration names, statements and proofs are otherwise verbatim.
-/

/-!
# Toy model: byte patterns, validity sets, layouts, and their laws

This module fixes the vocabulary of the package.

* `Pat n` is a fully initialized, provenance-free `n`-byte pattern.
* A payload type is given by its validity set `V : Validity n` over `n`-byte patterns;
  its values are its valid patterns (`Val V`). A *niche* of `V` is an invalid pattern.
* A `Layout α m` of a type `α` in `m` bytes is an encoder (one chosen representation per
  value) together with a decoder (the validity check plus the interpretation of a pattern).
* The round-trip laws `DecEnc` (decode after encode) and `Canonical` (canonical decoding)
  are kept as separate propositions; `Lawful` is their conjunction.

The model deliberately omits uninitialized bytes, pointer provenance, alignment, padding,
and safety (as opposed to validity) invariants.
-/

namespace Toy.WrapNiche.Imported

/-! ## Byte patterns -/

/-- An `n`-byte pattern: the fully initialized, provenance-free contents of `n` bytes,
identified with its little-endian value in `[0, 256 ^ n)`. Byte `i` of a pattern is
`byteAt p i`. This captures the bytes that a transmute from `[u8; n]` can supply. -/
abbrev Pat (n : Nat) : Type := Fin (256 ^ n)

theorem pat_card_pos (n : Nat) : 0 < 256 ^ n := Nat.pow_pos (by decide)

instance instNeZeroPatCard (n : Nat) : NeZero (256 ^ n) :=
  ⟨Nat.pos_iff_ne_zero.mp (pat_card_pos n)⟩

/-- The all-zero pattern of `n` bytes (`[0u8; n]`). -/
def zeroPat (n : Nat) : Pat n := ⟨0, pat_card_pos n⟩

/-- Byte `i` (little-endian position) of an `n`-byte pattern. -/
def byteAt {n : Nat} (p : Pat n) (i : Fin n) : Fin 256 :=
  ⟨p.val / 256 ^ i.val % 256, Nat.mod_lt _ (by decide)⟩

/-! ## Payload validity sets -/

/-- A payload type, given by its validity set over `n`-byte patterns (`true` = valid).
This captures the bit-validity invariant of a type whose values are in one-to-one
correspondence with their (fully initialized) byte representations, such as integers,
`bool`, or `NonZero` integers. -/
abbrev Validity (n : Nat) : Type := Pat n → Bool

/-- The values of a payload with validity set `V`: exactly its valid patterns. -/
abbrev Val {n : Nat} (V : Validity n) : Type := {p : Pat n // V p = true}

/-- `p` is a *niche* of `V`: a pattern that is invalid for the payload.

This is the model's notion, and it is broader than rustc's. In rustc a niche is a value
outside the valid range of one scalar field (UCG glossary: not every invalid bit-pattern is
a niche), so the invalid patterns counted here can exceed the niche values the compiler can
use: `UnsafeCell` disables niche use entirely; the `char` surrogate range `0xD800..=0xDFFF`
is invalid but lies inside `char`'s scalar valid range `0..=0x10FFFF`; and for a payload
with several fields, only one field's out-of-range values are used (for `(bool, bool)`,
65532 invalid patterns but 254 usable niche values). -/
def IsNiche {n : Nat} (V : Validity n) (p : Pat n) : Prop := V p = false

instance {n : Nat} (V : Validity n) (p : Pat n) : Decidable (IsNiche V p) :=
  inferInstanceAs (Decidable (V p = false))

/-- Validity of an `n`-byte `NonZero` integer: every pattern except the all-zero one.
For `n ≥ 1` this is the bit validity of `NonZero<uN>`; at `n = 0` the only pattern is the
zero pattern, so `nonZeroV 0` is the empty validity set (an uninhabited payload). -/
def nonZeroV (n : Nat) : Validity n := fun p => p.val != 0

/-- Validity of a one-byte `bool`-like type: exactly the patterns `0` and `1`. -/
def boolV : Validity 1 := fun p => decide (p.val < 2)

/-- A one-byte payload whose invalid patterns are exactly `0` and `1` (two niches). -/
def geTwoV : Validity 1 := fun p => decide (2 ≤ p.val)

/-- Validity of an `n`-byte payload with no niche (every pattern valid, like `u8`/`u32`). -/
def allV (n : Nat) : Validity n := fun _ => true

/-- The list of niches (invalid patterns) of `V`, in increasing order of value. -/
def invalidPats {n : Nat} (V : Validity n) : List (Pat n) :=
  (List.finRange (256 ^ n)).filter (fun p => !V p)

/-- The number of niches (invalid patterns) of `V`. -/
def numInvalid {n : Nat} (V : Validity n) : Nat := (invalidPats V).length

/-! ## Layouts and their laws -/

/-- A layout of type `α` in `m` bytes: `enc` picks one representation for each value and
`dec` decides whether a pattern is valid for `α` (`some`) and which value it denotes.
`m` is the size of the layout. -/
@[ext] structure Layout (α : Type) (m : Nat) where
  /-- The chosen representation of each value. -/
  enc : α → Pat m
  /-- The validity check and interpretation of a pattern. -/
  dec : Pat m → Option α

variable {α β : Type} {m n : Nat}

/-- Decode after encode: every value's chosen representation is valid and denotes that
value. This alone allows a value to have several valid representations. -/
def DecEnc (L : Layout α m) : Prop := ∀ x, L.dec (L.enc x) = some x

/-- Canonical decoding: a pattern that decodes to `x` is exactly `x`'s chosen
representation (so each value has exactly one valid representation). -/
def Canonical (L : Layout α m) : Prop := ∀ p x, L.dec p = some x → L.enc x = p

/-- A lawful layout: both round-trip laws hold. -/
def Lawful (L : Layout α m) : Prop := DecEnc L ∧ Canonical L

/-- Every `m`-byte pattern is valid for the layout (the type is "from-bytes": a transmute
from any `[u8; m]` produces a valid value). -/
def FromBytes (L : Layout α m) : Prop := ∀ p, ∃ x, L.dec p = some x

/-! ## Option-like enums and documented-guarantee hypotheses -/

/-- The option-like enum over the payload `V`: a `None` variant plus `Some v`. -/
abbrev Opt {n : Nat} (V : Validity n) : Type := Option (Val V)

/-- An enum with `k` extra dataless variants plus one variant carrying the payload `V`.
`Opt V` corresponds to `k = 1` (see `optToExt1`). -/
abbrev ExtEnum (k : Nat) {n : Nat} (V : Validity n) : Type := Fin k ⊕ Val V

/-- The `None` variant is represented by pattern `p` (`transmute::<Option<T>, [u8; m]>(None)`
produces `p`). -/
def NonePinned (L : Layout (Option β) m) (p : Pat m) : Prop := L.enc none = p

/-- The documented niche guarantee, as a hypothesis about a layout of `Opt V` (payload of
`n` bytes): the layout has size `n` (the payload's size) and `None` is pattern `p`.
It does not say that `p` is a niche of `V`; for Some-transparent layouts that follows
(`isNiche_enc_none_of_decSomeTransparent_of_decEnc`), otherwise it need not hold. -/
def NichePinned {V : Validity n} (L : Layout (Opt V) m) (p : Pat m) : Prop :=
  m = n ∧ NonePinned L p

/-- Encoder-side transparency: `Some v` is represented by `v`'s own pattern. Since the
payload's own decoder reads a valid pattern as itself, this models the documented
transmute `Option<T> → T` producing `t` from `Some(t)`. The type of `L` fixes the layout's
size to the payload's size `n`. With `DecEnc` it implies `DecSomeTransparent`
(`decSomeTransparent_of_someTransparent_of_decEnc`); the converse needs `Canonical`. -/
def SomeTransparent {V : Validity n} (L : Layout (Opt V) n) : Prop :=
  ∀ v : Val V, L.enc (some v) = v.val

/-- Decoder-side transparency: every valid payload pattern decodes to `Some` of itself.
This models the documented transmute `T → Option<T>` producing `Some(t)` from `t`. The type
of `L` fixes the layout's size to the payload's size `n`. -/
def DecSomeTransparent {V : Validity n} (L : Layout (Opt V) n) : Prop :=
  ∀ v : Val V, L.dec v.val = some (some v)

/-! ## Constructions -/

/-- The payload's own layout: a value is its pattern; exactly the valid patterns decode. -/
def payloadLayout (V : Validity n) : Layout (Val V) n where
  enc v := v.val
  dec p := if h : V p = true then some ⟨p, h⟩ else none

/-- Niche filling with `None ↦ q`: `Some v ↦ v`'s pattern, all in the payload's `n` bytes.
The decoder reads `q` as `None` and any other valid pattern as `Some`. -/
def nicheLayout (V : Validity n) (q : Pat n) : Layout (Opt V) n where
  enc
    | none => q
    | some v => v.val
  dec p := if p = q then some none else if h : V p = true then some (some ⟨p, h⟩) else none

theorem tag_enc_lt {n : Nat} (x : Nat) (hx : x < 256 ^ n) : 1 + 256 * x < 256 ^ (n + 1) := by
  rw [Nat.pow_succ]; omega

theorem tag_dec_lt {n : Nat} (p : Pat (n + 1)) : p.val / 256 < 256 ^ n := by
  have h1 : p.val < 256 ^ (n + 1) := p.isLt
  have h2 : 256 ^ (n + 1) = 256 ^ n * 256 := Nat.pow_succ _ _
  omega

/-- Separate-tag layout of `Option α` in `n + 1` bytes over a layout `L` of `α` in `n`
bytes: byte 0 is a tag (`0` = `None`, `1` = `Some`), bytes `1..n` hold `L`'s pattern;
`None` is the all-zero pattern, and only canonical patterns decode. -/
def taggedLayout (L : Layout α n) : Layout (Option α) (n + 1) where
  enc
    | none => zeroPat (n + 1)
    | some a => ⟨1 + 256 * (L.enc a).val, tag_enc_lt _ (L.enc a).isLt⟩
  dec p :=
    if p.val = 0 then some none
    else if p.val % 256 = 1 then (L.dec ⟨p.val / 256, tag_dec_lt p⟩).map some
    else none

/-- Like `taggedLayout`, but the payload bytes of a `None` pattern are ignored (any
pattern with tag byte `0` decodes as `None`), as for a tagged enum whose `None` variant
leaves its payload bytes unconstrained. Satisfies `DecEnc` whenever `L` does; for `n ≥ 1`
it is not `Canonical` (a pattern with tag `0` and nonzero payload bytes also decodes as
`None`). At `n = 0` there are no payload bytes and it coincides with `taggedLayout L`. -/
def taggedLooseLayout (L : Layout α n) : Layout (Option α) (n + 1) where
  enc := (taggedLayout L).enc
  dec p :=
    if p.val % 256 = 0 then some none
    else if p.val % 256 = 1 then (L.dec ⟨p.val / 256, tag_dec_lt p⟩).map some
    else none

/-- Niche filling for `k` extra variants: variant `inl i ↦ t i`, `inr v ↦ v`'s pattern,
in the payload's `n` bytes. The decoder looks the pattern up among the tags first. -/
def nicheLayoutK {k : Nat} (V : Validity n) (t : Fin k → Pat n) : Layout (ExtEnum k V) n where
  enc
    | .inl i => t i
    | .inr v => v.val
  dec p :=
    match (List.finRange k).find? (fun i => t i == p) with
    | some i => some (.inl i)
    | none => if h : V p = true then some (.inr ⟨p, h⟩) else none

/-- The first `k` niches of `V` in increasing order (defaulting to the zero pattern past
the end of `invalidPats V`). -/
def firstNiches (V : Validity n) (k : Nat) : Fin k → Pat n :=
  fun i => (invalidPats V).getD i.val (zeroPat n)

/-- Transport a layout of `α` to `β` along `f : β → α` (encode) and `g : α → β` (decode). -/
def Layout.comap (f : β → α) (g : α → β) (L : Layout α m) : Layout β m where
  enc b := L.enc (f b)
  dec p := (L.dec p).map g

/-- `Option α` as an enum with one extra variant. -/
def optToExt1 {n : Nat} {V : Validity n} : Opt V → ExtEnum 1 V
  | none => .inl 0
  | some v => .inr v

/-- Inverse of `optToExt1`. -/
def ext1ToOpt {n : Nat} {V : Validity n} : ExtEnum 1 V → Opt V
  | .inl _ => none
  | .inr v => some v

/-! ## Decidability helpers for small concrete instances -/

instance decForallVal {V : Validity n} (P : Val V → Prop) [DecidablePred P] :
    Decidable (∀ v : Val V, P v) :=
  decidable_of_iff (∀ p : Pat n, (h : V p = true) → P ⟨p, h⟩)
    ⟨fun h v => h v.1 v.2, fun h p hp => h ⟨p, hp⟩⟩

instance decForallOption (P : Option α → Prop) [Decidable (P none)]
    [Decidable (∀ a, P (some a))] : Decidable (∀ x, P x) :=
  decidable_of_iff (P none ∧ ∀ a, P (some a))
    ⟨fun ⟨h0, h1⟩ x => match x with
      | none => h0
      | some a => h1 a,
     fun h => ⟨h none, fun a => h (some a)⟩⟩

instance decForallSum {γ δ : Type} (P : γ ⊕ δ → Prop) [Decidable (∀ a, P (.inl a))]
    [Decidable (∀ b, P (.inr b))] : Decidable (∀ x, P x) :=
  decidable_of_iff ((∀ a, P (.inl a)) ∧ ∀ b, P (.inr b))
    ⟨fun ⟨h1, h2⟩ x => match x with
      | .inl a => h1 a
      | .inr b => h2 b,
     fun h => ⟨fun _ => h _, fun _ => h _⟩⟩

/-- `Canonical` checked one pattern at a time (convenient for `decide`). -/
theorem canonical_of_forall_pat (L : Layout α m)
    (h : ∀ p, (L.dec p).all (fun x => decide (L.enc x = p)) = true) : Canonical L := by
  intro p x hx
  have := h p
  rw [hx] at this
  simpa using this

theorem fromBytes_of_forall_pat (L : Layout α m) (h : ∀ p, (L.dec p).isSome = true) :
    FromBytes L := by
  intro p
  have := h p
  cases hp : L.dec p with
  | none => rw [hp] at this; cases this
  | some x => exact ⟨x, rfl⟩

end Toy.WrapNiche.Imported
