import Toy.WrapNiche.Interval

/-!
# Affine niche encodings, their decoders, and the rotated comparison design

An *affine niche encoding* `A` (fields `first`, `span`, `nicheStart`) assigns the variant with
index `first + r`, for a relative index `r ≤ span`, the tag `nicheStart + r` (wrapping, mod
`M`). The *niche variant range* is `[first, first + span]` (`span` is `last - first` in the
notation `[first, last]`; writing the range by its start and length rules out an empty range).
The decoder `decodeIdx u A` performs one modular subtraction `rel := (x - nicheStart) mod M`
and returns `first + rel` if `rel ≤ span`, otherwise the untagged variant `u`.

Two enum shapes are used.

* **Dead-slot-free shape** (`affineLayout`): the values are the imported
  `ExtEnum (span + 1) V` — relative indices `r ≤ span` for the dataless variants, plus the
  untagged variant carrying a valid field value. Every slot of the range is a live variant.
* **General shape** (`genLayout`, over an `EnumSpec`): `k` variants indexed `0..k-1`, an
  untagged variant `u`, and an inhabitedness flag `inh i` for the others (dataless variants
  are the inhabited `i ≠ u`; uninhabited variants have no values). The niche range may
  contain `u` or uninhabited variants ("dead slots"). The decoder is the checked decoder: a
  field value whose relative index is in range decodes to that variant if it is live and is
  rejected otherwise; a value out of range decodes to `u` if it is valid for the payload and is
  rejected otherwise.

The rotated encoding renumbers the variants cyclically starting after `u` before applying an
affine encoding with `first = 0`; its decoder adds one modular rotation of the index.
-/

namespace Toy.WrapNiche

open Imported

/-- Parameters of an affine niche encoding over a niche field `Fin M`: the niche variant range
`[first, first + span]` and the tag `nicheStart` of variant `first`. -/
structure AffineNiche (M : Nat) where
  /-- Index of the first variant of the niche variant range. -/
  first : Nat
  /-- `last - first`: the range is `[first, first + span]`, with `span + 1` slots. -/
  span : Nat
  /-- Tag of variant `first`. -/
  nicheStart : Fin M
deriving DecidableEq, Repr

namespace AffineNiche

variable {M : Nat}

/-- The last variant index of the niche variant range. -/
def last (A : AffineNiche M) : Nat := A.first + A.span

/-- The tag of relative index `r` (variant `first + r`): `(nicheStart + r) mod M`. -/
def tagOf (A : AffineNiche M) (r : Nat) : Fin M := wrapAdd A.nicheStart r

/-- The tag interval `[nicheStart, nicheStart + span]` (wrapping). Its members are exactly the
tags `tagOf r`, `r ≤ span`, when `span < M`; when `span ≥ M` the end point wraps (floor modulo)
and the interval no longer equals that set (for `span = M` it is the singleton
`[nicheStart, nicheStart]`). -/
def tagInterval (A : AffineNiche M) : WrapInterval M :=
  ⟨A.nicheStart, wrapAdd A.nicheStart A.span⟩

end AffineNiche

/-- The single-subtraction niche decoder (variant index only): `rel := (x - nicheStart) mod M`;
if `rel ≤ span` return `first + rel`, else return the untagged variant `u`. -/
def decodeIdx {M : Nat} (u : Nat) (A : AffineNiche M) (x : Fin M) : Nat :=
  if offset A.nicheStart x ≤ A.span then A.first + offset A.nicheStart x else u

/-- Every one of the `span + 1` tags `ns + r` (`r ≤ span`, wrapping) is invalid for `V`. -/
def TagsDisjoint {M : Nat} (V : Fin M → Bool) (ns : Fin M) (span : Nat) : Prop :=
  ∀ r, r ≤ span → V (wrapAdd ns r) = false

instance {M : Nat} (V : Fin M → Bool) (ns : Fin M) (span : Nat) :
    Decidable (TagsDisjoint V ns span) :=
  Nat.decidableBallLE span (fun r _ => V (wrapAdd ns r) = false)

/-! ## Dead-slot-free shape (imported `ExtEnum`) -/

/-- The affine tag map on relative indices, `r ↦ nicheStart + r` (wrapping). -/
def affineTags {M : Nat} (A : AffineNiche M) : Fin (A.span + 1) → Fin M :=
  fun r => A.tagOf r.val

/-- The affine niche layout of `ExtEnum (span + 1) V` in the payload's `n` bytes: relative
index `r` is encoded as its tag, a payload value as itself; the decoder is the single
subtraction (`inl rel` if `rel ≤ span`), and otherwise the payload's validity check. Variants
are named by their relative index `r`, so `A.first` is not used by this layout. -/
def affineLayout {n : Nat} (V : Validity n) (A : AffineNiche (256 ^ n)) :
    Layout (ExtEnum (A.span + 1) V) n where
  enc
    | .inl r => A.tagOf r.val
    | .inr v => v.val
  dec x :=
    if h : offset A.nicheStart x ≤ A.span then
      some (.inl ⟨offset A.nicheStart x, Nat.lt_succ_of_le h⟩)
    else if hv : V x = true then some (.inr ⟨x, hv⟩) else none

/-! ## General shape (dead slots allowed) -/

/-- An enum shape: `k` variants `0..k-1`, the untagged variant `u` (carrying the payload),
and an inhabitedness flag for the other variants. The structure does not require `u < k`
(nor `k ≥ 1`): if `u ≥ k`, every variant `0..k-1` is a candidate dataless variant and the
untagged variant is the extra index `u`. Discriminants are the variant indices. -/
structure EnumSpec where
  /-- Number of variants. -/
  k : Nat
  /-- Index of the untagged variant. -/
  u : Nat
  /-- Whether variant `i` (for `i ≠ u`) is inhabited. -/
  inh : Nat → Bool

/-- Variant `i` is a *live* dataless variant: an inhabited variant other than `u`. -/
def EnumSpec.Live (E : EnumSpec) (i : Nat) : Prop := i < E.k ∧ i ≠ E.u ∧ E.inh i = true

instance (E : EnumSpec) (i : Nat) : Decidable (E.Live i) := by
  unfold EnumSpec.Live; infer_instance

/-- Every live variant lies in the niche variant range `[first, first + span]`. -/
def LiveInRange {M : Nat} (E : EnumSpec) (A : AffineNiche M) : Prop :=
  ∀ i, i < E.k → i ≠ E.u → E.inh i = true → A.first ≤ i ∧ i ≤ A.first + A.span

instance {M : Nat} (E : EnumSpec) (A : AffineNiche M) : Decidable (LiveInRange E A) := by
  unfold LiveInRange; infer_instance

/-- The values of the general enum: a live dataless variant (by its index), or the untagged
variant carrying a valid field value. -/
abbrev GenVal (E : EnumSpec) {n : Nat} (V : Validity n) : Type :=
  {i : Nat // E.Live i} ⊕ Val V

/-- The affine niche layout of the general enum with the checked decoder. Variant `i` is
encoded as the tag of relative index `i - first` (truncated subtraction; exact when
`first ≤ i`). Every variant other than `u` is dataless here (`GenVal` gives it no field
values). -/
def genLayout (E : EnumSpec) {n : Nat} (A : AffineNiche (256 ^ n)) (V : Validity n) :
    Layout (GenVal E V) n where
  enc
    | .inl i => A.tagOf (i.val - A.first)
    | .inr v => v.val
  dec x :=
    if offset A.nicheStart x ≤ A.span then
      if h : E.Live (A.first + offset A.nicheStart x) then
        some (.inl ⟨A.first + offset A.nicheStart x, h⟩)
      else none
    else if hv : V x = true then some (.inr ⟨x, hv⟩) else none

/-- The four classes of field values under an affine encoding. -/
inductive FieldClass
  /-- Outside the tag interval and valid for the payload. -/
  | valid
  /-- In the tag interval, at the slot of a live variant. -/
  | liveTag
  /-- In the tag interval, at a dead slot (the slot of `u`, of an uninhabited variant, or of
  an index `≥ k`). -/
  | deadTag
  /-- Outside the tag interval and invalid for the payload. -/
  | unusedNiche
deriving DecidableEq, Repr

/-- Classify a field value by semantic membership in the tag interval, liveness of its slot,
and payload validity. By construction exactly one class applies. -/
def classify {M : Nat} (E : EnumSpec) (A : AffineNiche M) (V : Fin M → Bool) (x : Fin M) :
    FieldClass :=
  if A.tagInterval.Mem x then
    (if E.Live (A.first + offset A.nicheStart x) then .liveTag else .deadTag)
  else if V x then .valid else .unusedNiche

/-! ## Variant order: natural range and the rotated encoding -/

/-- For an enum with `k ≥ 2` variants, all inhabited, and untagged variant `u < k`: the first
variant needing a tag (`1` if `u = 0`, else `0`). -/
def naturalFirst (u : Nat) : Nat := if u = 0 then 1 else 0

/-- The last variant needing a tag (`k - 2` if `u = k - 1`, else `k - 1`; truncated
subtraction, meaningful for `k ≥ 2`). -/
def naturalLast (k u : Nat) : Nat := if u = k - 1 then k - 2 else k - 1

/-- `last - first` of the smallest range covering every variant that needs a tag. -/
def naturalSpan (k u : Nat) : Nat := naturalLast k u - naturalFirst u

/-- Rotated index of variant `i`: `(i - (u + 1)) mod k`, computed as
`(i + k - (u + 1) % k) % k`, so the variants after `u` come first and `u` gets `k - 1`. -/
def rotIdx (k u i : Nat) : Nat := (i + k - (u + 1) % k) % k

/-- Rotated tag of variant `i`: `nicheStart + rotIdx k u i` (wrapping). -/
def rotTag {M : Nat} (k u : Nat) (ns : Fin M) (i : Nat) : Fin M := wrapAdd ns (rotIdx k u i)

/-- Rotated decoder: `rel := (x - ns) mod M`; if `rel + 1 < k` (that is, `rel` is one of the
`k - 1` rotated indices `0..k-2`; no truncated subtraction) return `(rel + u + 1) mod k` — one
extra modular operation — else `u`. -/
def rotDecodeIdx {M : Nat} (k u : Nat) (ns : Fin M) (x : Fin M) : Nat :=
  if offset ns x + 1 < k then (offset ns x + u + 1) % k else u

/-- The `k - 1` rotated tags `ns + r` (wrapping), for the rotated indices `r` with `r + 1 < k`,
are all invalid for `V`. For `k ≤ 1` there is no rotated tag and the condition holds trivially;
for `k ≥ 2` it is `TagsDisjoint V ns (k - 2)` (`rotTagsInvalid_iff_tagsDisjoint_sub_two`). -/
def RotTagsInvalid {M : Nat} (V : Fin M → Bool) (k : Nat) (ns : Fin M) : Prop :=
  ∀ r, r + 1 < k → V (wrapAdd ns r) = false

instance {M : Nat} (V : Fin M → Bool) (k : Nat) (ns : Fin M) :
    Decidable (RotTagsInvalid V k ns) :=
  decidable_of_iff (∀ r, r < k → r + 1 < k → V (wrapAdd ns r) = false)
    ⟨fun h r hr => h r (Nat.lt_of_succ_lt hr) hr, fun h r _ hr => h r hr⟩

/-! ## Fully proved auxiliary lemmas -/

/-- For `k ≥ 2`, the natural range is the least range covering every variant other than `u`: its
ends are variants other than `u`, and every variant other than `u` lies between them. -/
theorem naturalFirst_naturalLast_spec (k u : Nat) (hk : 2 ≤ k) :
    naturalFirst u < k ∧ naturalFirst u ≠ u ∧ naturalLast k u < k ∧ naturalLast k u ≠ u ∧
      ∀ i, i < k → i ≠ u → naturalFirst u ≤ i ∧ i ≤ naturalLast k u := by
  unfold naturalFirst naturalLast
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try intro i hi hiu) <;> split <;> (try split) <;> omega

/-- For `k ≥ 2`, the natural span is `k - 2` when `u = 0` or `u = k - 1`, and `k - 1` otherwise. -/
theorem naturalSpan_eq (k u : Nat) (hk : 2 ≤ k) :
    naturalSpan k u = if u = 0 ∨ u = k - 1 then k - 2 else k - 1 := by
  unfold naturalSpan naturalFirst naturalLast
  by_cases h0 : u = 0 <;> by_cases h1 : u = k - 1
  · rw [ite_eq_left h1, ite_eq_left h0, ite_eq_left (Or.inl h0)]; omega
  · rw [ite_eq_right h1, ite_eq_left h0, ite_eq_left (Or.inl h0)]; omega
  · rw [ite_eq_left h1, ite_eq_right h0, ite_eq_left (Or.inr h1)]; omega
  · rw [ite_eq_right h1, ite_eq_right h0, ite_eq_right (by omega)]; omega

/-- For `k ≥ 2`, the rotated-tag condition is `TagsDisjoint` with span `k - 2` (under `2 ≤ k`
the truncated subtraction `k - 2` does not truncate). -/
theorem rotTagsInvalid_iff_tagsDisjoint_sub_two {M : Nat} (V : Fin M → Bool) (k : Nat)
    (ns : Fin M) (hk : 2 ≤ k) : RotTagsInvalid V k ns ↔ TagsDisjoint V ns (k - 2) :=
  ⟨fun h r hr => h r (by omega), fun h r hr => h r (by omega)⟩

end Toy.WrapNiche
