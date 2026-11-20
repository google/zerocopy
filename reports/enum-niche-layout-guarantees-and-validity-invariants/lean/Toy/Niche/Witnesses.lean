import Toy.Niche.Results

/-!
# Witnesses: definition examples, counterexamples, non-vacuity, positive controls

Everything in this module is fully proved. Small concrete cases are decided by `decide`
over one-byte patterns.

Naming:
* `ex_*` / `nex_*` — positive / negative examples for a definition;
* `ce_<result>_drop_<hypothesis>` — a concrete instance where every *other* hypothesis of
  the result holds and its conclusion fails;
* `nv_<result>` — a concrete instance satisfying all hypotheses of the result;
* `pc_<result>` — a positive control for an impossibility result.
-/

namespace Toy.Niche

set_option maxRecDepth 100000

/-! ## Concrete layouts used as counterexamples -/

/-- The value `1` of the one-byte `NonZero` payload. -/
def oneNZ : Val (nonZeroV 1) := ⟨1, by decide⟩

/-- A lawful one-byte layout of `Opt (nonZeroV 1)` that is *not* Some-transparent:
`None ↦ 1` (a valid payload pattern), `Some 1 ↦ 0`, other `Some v ↦ v`. -/
def swapLayout : Layout (Opt (nonZeroV 1)) 1 where
  enc
    | none => 1
    | some v => if v.val = 1 then 0 else v.val
  dec p := if p = 1 then some none
    else if h : nonZeroV 1 p = true then some (some ⟨p, h⟩) else some (some oneNZ)

/-- Exchanges the patterns `1` and `2`. -/
def swap12 (p : Pat 1) : Pat 1 := if p = 1 then 2 else if p = 2 then 1 else p

/-- A lawful one-byte layout of `Opt (nonZeroV 1)` with `None ↦ 0` that is not
Some-transparent: `Some 1 ↦ 2`, `Some 2 ↦ 1`, other `Some v ↦ v`. -/
def permLayout : Layout (Opt (nonZeroV 1)) 1 where
  enc
    | none => 0
    | some v => swap12 v.val
  dec p := if p = 0 then some none
    else if h : nonZeroV 1 (swap12 p) = true then some (some ⟨swap12 p, h⟩) else none

/-- The niche-filling encoder with a decoder that rejects every pattern. -/
def zeroDecLayout : Layout (Opt (nonZeroV 1)) 1 where
  enc := (nicheLayout (nonZeroV 1) (zeroPat 1)).enc
  dec _ := none

/-- `None ↦ 1` (a valid payload pattern) and `Some v ↦ v`; the decoder reads every valid
pattern as `Some` of itself, so the payload-to-option direction holds while `None` does not
round-trip. -/
def noneLostLayout : Layout (Opt (nonZeroV 1)) 1 where
  enc
    | none => 1
    | some v => v.val
  dec p := if h : nonZeroV 1 p = true then some (some ⟨p, h⟩) else none

/-- Niche filling over `geTwoV` with `None ↦ 0`, whose decoder also reads the other niche
`1` as `None` (decode-after-encode holds, canonical decoding fails). -/
def geTwoLooseLayout : Layout (Opt geTwoV) 1 where
  enc := (nicheLayout geTwoV (zeroPat 1)).enc
  dec p := if p = 1 then some none else (nicheLayout geTwoV (zeroPat 1)).dec p

/-- A one-byte layout of `Opt boolV`: `None ↦ 2`, `Some false ↦ 3`, `Some true ↦ 4`; the
decoder reads `0` and `3` as `Some false` and `1` and `4` as `Some true`. Decoder-side
transparent and decode-after-encode, but not encoder-side transparent (and not canonical). -/
def decSomeNotSomeLayout : Layout (Opt boolV) 1 where
  enc
    | none => 2
    | some v => if v.val = 0 then 3 else 4
  dec p :=
    if p = 2 then some none
    else if p = 0 ∨ p = 3 then some (some ⟨0, by decide⟩)
    else if p = 1 ∨ p = 4 then some (some ⟨1, by decide⟩)
    else none

/-- A one-byte payload whose only niche is the pattern `1` (the zero pattern is valid). -/
def nonOneV : Validity 1 := fun p => p.val != 1

/-- The value `0` of `nonOneV`. -/
def zeroNonOne : Val nonOneV := ⟨0, by decide⟩

/-- A lawful one-byte layout of `Opt nonOneV` with `None ↦ 0` although `0` is a valid
payload pattern: `Some 0 ↦ 1`, other `Some v ↦ v`. -/
def swap01Layout : Layout (Opt nonOneV) 1 where
  enc
    | none => 0
    | some v => if v.val = 0 then 1 else v.val
  dec p :=
    if p = 0 then some none
    else if h : nonOneV p = true then some (some ⟨p, h⟩)
    else some (some zeroNonOne)

/-- One extra variant over the one-byte `NonZero` payload, niche-filled in 1 byte. -/
def ext1NonZeroLayout : Layout (ExtEnum 1 (nonZeroV 1)) 1 :=
  (nicheLayout (nonZeroV 1) (zeroPat 1)).comap ext1ToOpt optToExt1

/-- One extra variant over a niche-free one-byte payload, separately tagged in 2 bytes. -/
def ext1AllTaggedLayout : Layout (ExtEnum 1 (allV 1)) 2 :=
  (taggedLayout (payloadLayout (allV 1))).comap ext1ToOpt optToExt1

/-- One extra variant over a niche-free one-byte payload with a constant encoder and a
decoder that rejects everything. -/
def ext1AllZeroDecLayout : Layout (ExtEnum 1 (allV 1)) 1 :=
  ⟨fun _ => zeroPat 1, fun _ => none⟩

/-- A two-byte payload with exactly two valid patterns (`0` and `1`). -/
def sparse2V : Validity 2 := fun p => decide (p.val < 2)

/-- One extra variant over `sparse2V`, lawful in one byte (smaller than the payload). -/
def sparse2In1Byte : Layout (ExtEnum 1 sparse2V) 1 where
  enc
    | .inl _ => 2
    | .inr v => ⟨v.val.val, by have hv := v.2; simp [sparse2V] at hv; omega⟩
  dec p :=
    if p.val = 2 then some (.inl 0)
    else if h : p.val < 2 then
      some (.inr ⟨⟨p.val, by omega⟩, by simp [sparse2V, h]⟩)
    else none

/-- Tags `0` and `1` for two extra variants over `geTwoV`. -/
def geTwoTags : Fin 2 → Pat 1 := fun i => if i.val = 0 then 0 else 1

/-! ## Laws of the concrete layouts -/

theorem swapLayout_lawful : Lawful swapLayout :=
  ⟨by unfold DecEnc; decide, canonical_of_forall_pat _ (by decide)⟩

theorem permLayout_lawful : Lawful permLayout :=
  ⟨by unfold DecEnc; decide, canonical_of_forall_pat _ (by decide)⟩

theorem zeroDecLayout_not_decEnc : ¬ DecEnc zeroDecLayout := by
  intro h
  have := h none
  cases this

theorem zeroDecLayout_canonical : Canonical zeroDecLayout := by
  intro p x hx
  cases hx

theorem zeroDecLayout_someTransparent : SomeTransparent zeroDecLayout := fun _ => rfl

theorem noneLostLayout_decSomeTransparent : DecSomeTransparent noneLostLayout := by
  unfold DecSomeTransparent; decide

theorem noneLostLayout_not_decEnc : ¬ DecEnc noneLostLayout := by
  intro h
  exact absurd (h none) (by decide)

theorem geTwoLooseLayout_decEnc : DecEnc geTwoLooseLayout := by
  unfold DecEnc; decide

theorem geTwoLooseLayout_not_canonical : ¬ Canonical geTwoLooseLayout := by
  intro h
  have := h 1 none (by decide)
  exact absurd this (by decide)

theorem swap01Layout_lawful : Lawful swap01Layout :=
  ⟨by unfold DecEnc; decide, canonical_of_forall_pat _ (by decide)⟩

theorem nicheLayout_nonZero_lawful (n : Nat) : Lawful (nicheLayout (nonZeroV n) (zeroPat n)) :=
  (nicheLayout_lawful_iff_isNiche _ _).mpr ((isNiche_nonZeroV_iff _).mpr rfl)

theorem ext1NonZeroLayout_lawful : Lawful ext1NonZeroLayout :=
  comap_lawful optToExt1_ext1ToOpt ext1ToOpt_optToExt1 (nicheLayout_nonZero_lawful 1)

theorem ext1AllTaggedLayout_lawful : Lawful ext1AllTaggedLayout :=
  comap_lawful optToExt1_ext1ToOpt ext1ToOpt_optToExt1
    (taggedLayout_lawful (payloadLayout_lawful _))

theorem sparse2In1Byte_lawful : Lawful sparse2In1Byte := by
  have hde : DecEnc sparse2In1Byte := by
    intro x
    cases x with
    | inl i =>
      cases i using Fin.cases with
      | zero => simp [sparse2In1Byte]
      | succ j => exact j.elim0
    | inr v =>
      have hv : v.val.val < 2 := by simpa [sparse2V] using v.2
      simp only [sparse2In1Byte]
      have hne : ¬ v.val.val = 2 := by omega
      rw [ite_eq_right hne, dite_eq_left hv]
  refine ⟨hde, ?_⟩
  intro p x hp
  simp only [sparse2In1Byte] at hp
  split at hp
  · cases hp; apply Fin.ext; simp [sparse2In1Byte]; omega
  · split at hp
    · cases hp; apply Fin.ext; rfl
    · cases hp

theorem numInvalid_allV_one : numInvalid (allV 1) = 0 := by decide

theorem numInvalid_geTwoV : numInvalid geTwoV = 2 := by decide

theorem numInvalid_nonOneV : numInvalid nonOneV = 1 := by decide

theorem numInvalid_nonZeroV_le_one (n : Nat) : numInvalid (nonZeroV n) ≤ 1 := by
  rw [numInvalid_nonZeroV]; exact Nat.le_refl 1

/-! ## Definition examples -/

/-- `byteAt` reads little-endian bytes: `258 = 0x0102`. -/
theorem ex_byteAt : byteAt (258 : Pat 2) 0 = 2 ∧ byteAt (258 : Pat 2) 1 = 1 := by decide

/-- A pattern whose first byte is zero need not be the zero pattern. -/
theorem nex_zeroPat_first_byte : byteAt (256 : Pat 2) 0 = 0 ∧ (256 : Pat 2) ≠ zeroPat 2 := by
  decide

/-- Every byte of `zeroPat 4` is zero. -/
theorem ex_zeroPat_bytes : ∀ i, byteAt (zeroPat 4) i = 0 :=
  (eq_zeroPat_iff_bytes_zero (zeroPat 4)).mp rfl

theorem ex_isNiche : IsNiche (nonZeroV 4) (zeroPat 4) := by decide

theorem nex_isNiche : ¬ IsNiche (nonZeroV 4) 1 := by decide

theorem ex_validity_sets :
    nonZeroV 4 1 = true ∧ boolV 0 = true ∧ boolV 1 = true ∧ geTwoV 2 = true ∧
      allV 1 0 = true := by decide

theorem nex_validity_sets :
    nonZeroV 4 (zeroPat 4) = false ∧ boolV 2 = false ∧ boolV 255 = false ∧
      geTwoV 1 = false := by decide

/-- At `n = 0` the `NonZero` validity set is empty (its only pattern is zero). -/
theorem nonZeroV_zero_empty : ∀ p : Pat 0, nonZeroV 0 p = false := by decide

theorem ex_invalidPats : invalidPats geTwoV = [0, 1] := by decide

/-- `invalidPats` omits valid patterns, and a niche-free payload has none. -/
theorem nex_invalidPats : (0 : Pat 1) ∉ invalidPats boolV ∧ invalidPats (allV 1) = [] := by
  decide

theorem ex_numInvalid :
    numInvalid boolV = 254 ∧ numInvalid geTwoV = 2 ∧ numInvalid (allV 1) = 0 ∧
      numInvalid (nonZeroV 1) = 1 := by decide

/-- `numInvalid` counts invalid patterns, not valid ones (`boolV` has 2 valid patterns). -/
theorem nex_numInvalid : numInvalid boolV ≠ 2 := by decide

theorem ex_payloadLayout_lawful : Lawful (payloadLayout boolV) := payloadLayout_lawful _

theorem nex_payloadLayout_fromBytes : ¬ FromBytes (payloadLayout (nonZeroV 1)) := by
  intro h
  obtain ⟨x, hx⟩ := h 0
  have : (payloadLayout (nonZeroV 1)).dec 0 = none := by decide
  rw [this] at hx
  cases hx

/-- `DecEnc` rejects a decoder that rejects encoded values. -/
theorem nex_decEnc : ¬ DecEnc zeroDecLayout ∧ Canonical zeroDecLayout :=
  ⟨zeroDecLayout_not_decEnc, zeroDecLayout_canonical⟩

/-- `Canonical` rejects a second representation of `None`. -/
theorem nex_canonical : DecEnc geTwoLooseLayout ∧ ¬ Canonical geTwoLooseLayout :=
  ⟨geTwoLooseLayout_decEnc, geTwoLooseLayout_not_canonical⟩

theorem ex_lawful : Lawful (nicheLayout (nonZeroV 4) (zeroPat 4)) := nicheLayout_nonZero_lawful 4

theorem nex_lawful : ¬ Lawful (nicheLayout boolV 1) := by
  rw [nicheLayout_lawful_iff_isNiche]; decide

/-- The niche-filled `NonZero` layout with `None ↦ 0` is from-bytes, for every size. -/
theorem ex_fromBytes (n : Nat) : FromBytes (nicheLayout (nonZeroV n) (zeroPat n)) := by
  intro p
  by_cases hp : p = zeroPat n
  · exact ⟨none, by simp [nicheLayout, hp]⟩
  · have hv : nonZeroV n p = true := by
      cases hw : nonZeroV n p with
      | true => rfl
      | false => exact absurd ((isNiche_nonZeroV_iff p).mp hw) hp
    exact ⟨some ⟨p, hv⟩, by simp [nicheLayout, hp, hv]⟩

theorem nex_fromBytes : ¬ FromBytes (nicheLayout boolV 2) := by
  intro h
  obtain ⟨x, hx⟩ := h 3
  have : (nicheLayout boolV 2).dec 3 = none := by decide
  rw [this] at hx
  cases hx

theorem ex_nonePinned : NonePinned (nicheLayout (nonZeroV 4) (zeroPat 4)) (zeroPat 4) := rfl

theorem nex_nonePinned : ¬ NonePinned swapLayout (zeroPat 1) := by
  unfold NonePinned; decide

theorem ex_nichePinned : NichePinned (nicheLayout (nonZeroV 4) (zeroPat 4)) (zeroPat 4) :=
  ⟨rfl, rfl⟩

/-- A 2-byte tagged layout of a 1-byte payload with `None ↦ 0` is not `NichePinned`
(wrong size). -/
theorem nex_nichePinned :
    ¬ NichePinned (taggedLayout (payloadLayout (nonZeroV 1))) (zeroPat 2) := by
  intro h
  exact absurd h.1 (by decide)

/-- A layout of the payload's size whose `None` is not at the given pattern is not
`NichePinned` (wrong `None` pattern). -/
theorem nex_nichePinned_none : ¬ NichePinned swapLayout (zeroPat 1) := by
  intro h
  exact nex_nonePinned h.2

/-- `NichePinned` does not assert that the pinned pattern is a niche: the lawful
`swapLayout` is `NichePinned` at the valid pattern `1`. -/
theorem nichePinned_admits_valid_pattern :
    Lawful swapLayout ∧ NichePinned swapLayout 1 ∧ ¬ IsNiche (nonZeroV 1) 1 :=
  ⟨swapLayout_lawful, ⟨rfl, rfl⟩, by decide⟩

theorem ex_someTransparent : SomeTransparent (nicheLayout boolV 2) := fun _ => rfl

theorem nex_someTransparent : ¬ SomeTransparent permLayout := by
  intro h
  have := h oneNZ
  exact absurd this (by decide)

theorem ex_decSomeTransparent : DecSomeTransparent (nicheLayout boolV 2) := by
  unfold DecSomeTransparent; decide

/-- `swapLayout` reads the valid pattern `1` as `None`, not as `Some 1`. -/
theorem nex_decSomeTransparent : ¬ DecSomeTransparent swapLayout := by
  intro h
  exact absurd (h oneNZ) (by decide)

/-- Without canonical decoding, decoder-side transparency does not give encoder-side
transparency (even with decode-after-encode). -/
theorem decSomeTransparent_decEnc_not_someTransparent :
    DecEnc decSomeNotSomeLayout ∧ DecSomeTransparent decSomeNotSomeLayout ∧
      ¬ SomeTransparent decSomeNotSomeLayout := by
  refine ⟨by unfold DecEnc; decide, by unfold DecSomeTransparent; decide, ?_⟩
  intro h
  exact absurd (h ⟨0, by decide⟩) (by decide)

/-- Encoder-side transparency does not give decoder-side transparency without
decode-after-encode. -/
theorem someTransparent_not_decSomeTransparent :
    SomeTransparent zeroDecLayout ∧ ¬ DecSomeTransparent zeroDecLayout := by
  refine ⟨zeroDecLayout_someTransparent, ?_⟩
  intro h
  have := h oneNZ
  cases this

theorem ex_taggedLayout :
    Lawful (taggedLayout (payloadLayout (nonZeroV 1))) ∧
      ¬ FromBytes (taggedLayout (payloadLayout (nonZeroV 1))) := by
  refine ⟨taggedLayout_lawful (payloadLayout_lawful _), ?_⟩
  intro h
  obtain ⟨x, hx⟩ := h 2
  have : (taggedLayout (payloadLayout (nonZeroV 1))).dec 2 = none := by decide
  rw [this] at hx
  cases hx

theorem ex_taggedLooseLayout :
    DecEnc (taggedLooseLayout (payloadLayout (nonZeroV 1))) ∧
      ¬ Canonical (taggedLooseLayout (payloadLayout (nonZeroV 1))) := by
  refine ⟨taggedLooseLayout_decEnc (payloadLayout_lawful _).1, ?_⟩
  intro h
  have := h 256 none (by decide)
  exact absurd this (by decide)

/-- At `n = 0` (no payload bytes) the loose tagged layout is the canonical tagged layout. -/
theorem taggedLooseLayout_eq_taggedLayout_at_zero {α : Type} (L : Layout α 0) :
    taggedLooseLayout L = taggedLayout L := by
  apply Layout.ext
  · rfl
  · funext p
    have hlt : p.val < 256 := p.isLt
    have hmod : (p.val % 256 = 0) ↔ (p.val = 0) := by omega
    simp only [taggedLooseLayout, taggedLayout, hmod]

/-- Two extra variants over `geTwoV` with distinct niche tags `0`, `1`: lawful. -/
theorem ex_nicheLayoutK : Lawful (nicheLayoutK geTwoV geTwoTags) :=
  ⟨by unfold DecEnc; decide, canonical_of_forall_pat _ (by decide)⟩

/-- One extra variant over the one-byte `NonZero` payload with tag `0`: lawful. -/
theorem ex_nicheLayoutK_one :
    Lawful (nicheLayoutK (nonZeroV 1) (fun _ : Fin 1 => zeroPat 1)) :=
  ⟨by unfold DecEnc; decide, canonical_of_forall_pat _ (by decide)⟩

/-- Two extra variants sharing one tag pattern break decode-after-encode. -/
theorem nex_nicheLayoutK : ¬ DecEnc (nicheLayoutK (nonZeroV 1) (fun _ : Fin 2 => zeroPat 1)) := by
  intro h
  have := h (.inl 1)
  exact absurd this (by decide)

theorem ex_firstNiches : firstNiches boolV 2 0 = 2 ∧ firstNiches boolV 2 1 = 3 := by decide

/-- Past the end of `invalidPats`, `firstNiches` repeats its default. -/
theorem nex_firstNiches : firstNiches (nonZeroV 1) 2 0 = firstNiches (nonZeroV 1) 2 1 := by
  decide

/-- Tightness of `k ≤ numInvalid V` in `firstNiches_injective_and_isNiche_of_le_numInvalid`. -/
theorem ce_firstNiches_drop_le :
    ¬ (2 ≤ numInvalid (nonZeroV 1)) ∧ ¬ Function.Injective (firstNiches (nonZeroV 1) 2) := by
  refine ⟨by rw [numInvalid_nonZeroV]; decide, ?_⟩
  intro h
  have := h nex_firstNiches
  exact absurd this (by decide)

theorem ex_comap : Lawful ext1NonZeroLayout := ext1NonZeroLayout_lawful

/-- Transport along maps that are not inverse can break the laws: collapsing `Bool` onto one
payload value is not decode-after-encode. -/
theorem nex_comap :
    ¬ DecEnc ((payloadLayout boolV).comap (fun _ : Bool => (⟨0, by decide⟩ : Val boolV))
        (fun _ => false)) := by
  intro h
  have := h true
  exact absurd this (by decide)

/-! ## Result group 1 -/

/-- The counterexample when `q` is valid: `q = 1` is valid for `boolV` and the niche-filled
layout with `None ↦ 1` is not lawful. -/
theorem ce_nicheLayout_lawful_valid_q : boolV 1 = true ∧ ¬ Lawful (nicheLayout boolV 1) :=
  ⟨by decide, nex_lawful⟩

/-- The niche-filled layout at a valid `q` is still canonical; only decode-after-encode
fails. -/
theorem nicheLayout_valid_q_canonical_not_decEnc :
    Canonical (nicheLayout boolV 1) ∧ ¬ DecEnc (nicheLayout boolV 1) :=
  ⟨nicheLayout_canonical _ _, fun h => nex_lawful ⟨h, nicheLayout_canonical _ _⟩⟩

theorem nv_nicheLayout_lawful_iff_isNiche :
    IsNiche (nonZeroV 4) (zeroPat 4) ∧ Lawful (nicheLayout (nonZeroV 4) (zeroPat 4)) :=
  ⟨ex_isNiche, ex_lawful⟩

theorem ce_isNiche_enc_none_drop_decSomeTransparent :
    DecEnc swapLayout ∧ ¬ DecSomeTransparent swapLayout ∧
      ¬ IsNiche (nonZeroV 1) (swapLayout.enc none) :=
  ⟨swapLayout_lawful.1, nex_decSomeTransparent, by decide⟩

theorem ce_isNiche_enc_none_drop_decEnc :
    DecSomeTransparent noneLostLayout ∧ ¬ DecEnc noneLostLayout ∧
      ¬ IsNiche (nonZeroV 1) (noneLostLayout.enc none) :=
  ⟨noneLostLayout_decSomeTransparent, noneLostLayout_not_decEnc, by decide⟩

/-- Positive control: without the payload-to-option transmute, a lawful layout may put
`None` on a valid payload pattern. -/
theorem pc_isNiche_enc_none : Lawful swapLayout ∧ ¬ IsNiche (nonZeroV 1) (swapLayout.enc none) :=
  ⟨swapLayout_lawful, by decide⟩

theorem nv_isNiche_enc_none :
    DecSomeTransparent (nicheLayout (nonZeroV 4) (zeroPat 4)) ∧
      DecEnc (nicheLayout (nonZeroV 4) (zeroPat 4)) :=
  ⟨nicheLayout_decSomeTransparent_of_isNiche ex_isNiche, ex_lawful.1⟩

theorem nv_someTransparent_lawful_iff_eq_nicheLayout :
    (SomeTransparent (nicheLayout (nonZeroV 4) (zeroPat 4)) ∧
        Lawful (nicheLayout (nonZeroV 4) (zeroPat 4))) ∧
      IsNiche (nonZeroV 4) (zeroPat 4) :=
  ⟨⟨fun _ => rfl, ex_lawful⟩, ex_isNiche⟩

/-- Without Some-transparency, lawful layouts of the payload's size need not be niche-filled
layouts (`swapLayout` and `permLayout` are not `nicheLayout _ (L.enc none)`). -/
theorem lawful_not_nicheLayout :
    Lawful swapLayout ∧ swapLayout ≠ nicheLayout (nonZeroV 1) (swapLayout.enc none) ∧
      Lawful permLayout ∧ permLayout ≠ nicheLayout (nonZeroV 1) (permLayout.enc none) := by
  refine ⟨swapLayout_lawful, ?_, permLayout_lawful, ?_⟩
  · intro h
    have := congrArg (fun L => L.enc (some oneNZ)) h
    exact absurd this (by decide)
  · intro h
    have := congrArg (fun L => L.enc (some oneNZ)) h
    exact absurd this (by decide)

/-! ## Result group 2 -/

theorem ce_canonical_fromBytes_drop_size :
    (2 : Nat) ≠ 1 ∧ numInvalid (nonZeroV 1) ≤ 1 ∧
      DecEnc (taggedLayout (payloadLayout (nonZeroV 1))) ∧
      ¬ (Canonical (taggedLayout (payloadLayout (nonZeroV 1))) ∧
        FromBytes (taggedLayout (payloadLayout (nonZeroV 1)))) :=
  ⟨by decide, numInvalid_nonZeroV_le_one 1, ex_taggedLayout.1.1, fun h => ex_taggedLayout.2 h.2⟩

theorem nicheLayout_geTwoV_zero_not_fromBytes : ¬ FromBytes (nicheLayout geTwoV (zeroPat 1)) := by
  intro h
  obtain ⟨x, hx⟩ := h 1
  have : (nicheLayout geTwoV (zeroPat 1)).dec 1 = none := by decide
  rw [this] at hx
  cases hx

theorem ce_canonical_fromBytes_drop_numInvalid :
    numInvalid geTwoV = 2 ∧ DecEnc (nicheLayout geTwoV (zeroPat 1)) ∧
      ¬ (Canonical (nicheLayout geTwoV (zeroPat 1)) ∧
        FromBytes (nicheLayout geTwoV (zeroPat 1))) :=
  ⟨numInvalid_geTwoV, ((nicheLayout_lawful_iff_isNiche _ _).mpr (by decide)).1,
    fun h => nicheLayout_geTwoV_zero_not_fromBytes h.2⟩

theorem zeroDecLayout_not_fromBytes : ¬ FromBytes zeroDecLayout := by
  intro h
  obtain ⟨x, hx⟩ := h 0
  cases hx

theorem ce_canonical_fromBytes_drop_decEnc :
    numInvalid (nonZeroV 1) ≤ 1 ∧ ¬ DecEnc zeroDecLayout ∧
      ¬ (Canonical zeroDecLayout ∧ FromBytes zeroDecLayout) :=
  ⟨numInvalid_nonZeroV_le_one 1, zeroDecLayout_not_decEnc,
    fun h => zeroDecLayout_not_fromBytes h.2⟩

theorem nv_opt_canonical_and_fromBytes :
    (4 : Nat) = 4 ∧ numInvalid (nonZeroV 4) ≤ 1 ∧ DecEnc (nicheLayout (nonZeroV 4) (zeroPat 4)) :=
  ⟨rfl, numInvalid_nonZeroV_le_one 4, ex_lawful.1⟩

/-- `None` is not at zero (`swapLayout`: lawful, one niche, payload size), and the zero
pattern does not decode to `None`. -/
theorem ce_zero_iff_none_drop_nonePinned :
    numInvalid (nonZeroV 1) ≤ 1 ∧ Lawful swapLayout ∧ ¬ NonePinned swapLayout (zeroPat 1) ∧
      ¬ (∀ p, swapLayout.dec p = some none ↔ p = zeroPat 1) := by
  refine ⟨numInvalid_nonZeroV_le_one 1, swapLayout_lawful, nex_nonePinned, ?_⟩
  intro h
  exact absurd ((h (zeroPat 1)).mpr rfl) (by decide)

theorem ce_zero_iff_none_drop_decEnc :
    numInvalid (nonZeroV 1) ≤ 1 ∧ NonePinned zeroDecLayout (zeroPat 1) ∧
      Canonical zeroDecLayout ∧ ¬ DecEnc zeroDecLayout ∧
      ¬ (∀ p, zeroDecLayout.dec p = some none ↔ p = zeroPat 1) := by
  refine ⟨numInvalid_nonZeroV_le_one 1, rfl, zeroDecLayout_canonical,
    zeroDecLayout_not_decEnc, ?_⟩
  intro h
  have := (h (zeroPat 1)).mpr rfl
  cases this

theorem ce_zero_iff_none_drop_canonical :
    NonePinned geTwoLooseLayout (zeroPat 1) ∧ DecEnc geTwoLooseLayout ∧
      ¬ Canonical geTwoLooseLayout ∧
      ¬ (∀ p, geTwoLooseLayout.dec p = some none ↔ p = zeroPat 1) := by
  refine ⟨rfl, geTwoLooseLayout_decEnc, geTwoLooseLayout_not_canonical, ?_⟩
  intro h
  exact absurd ((h 1).mp (by decide)) (by decide)

theorem nv_zero_iff_none_lawful :
    NonePinned (nicheLayout (nonZeroV 4) (zeroPat 4)) (zeroPat 4) ∧
      DecEnc (nicheLayout (nonZeroV 4) (zeroPat 4)) ∧
      Canonical (nicheLayout (nonZeroV 4) (zeroPat 4)) :=
  ⟨rfl, ex_lawful.1, ex_lawful.2⟩

theorem ce_zero_iff_none_drop_size :
    (2 : Nat) ≠ 1 ∧ numInvalid (nonZeroV 1) ≤ 1 ∧
      DecEnc (taggedLooseLayout (payloadLayout (nonZeroV 1))) ∧
      NonePinned (taggedLooseLayout (payloadLayout (nonZeroV 1))) (zeroPat 2) ∧
      ¬ (∀ p, (taggedLooseLayout (payloadLayout (nonZeroV 1))).dec p = some none ↔
          p = zeroPat 2) := by
  refine ⟨by decide, numInvalid_nonZeroV_le_one 1, ex_taggedLooseLayout.1, rfl, ?_⟩
  intro h
  exact absurd ((h 256).mp (by decide)) (by decide)

theorem ce_zero_iff_none_drop_numInvalid :
    numInvalid geTwoV = 2 ∧ DecEnc geTwoLooseLayout ∧
      NonePinned geTwoLooseLayout (zeroPat 1) ∧
      ¬ (∀ p, geTwoLooseLayout.dec p = some none ↔ p = zeroPat 1) :=
  ⟨numInvalid_geTwoV, geTwoLooseLayout_decEnc, rfl, ce_zero_iff_none_drop_canonical.2.2.2⟩

theorem nv_zero_iff_none_size_numInvalid :
    (4 : Nat) = 4 ∧ numInvalid (nonZeroV 4) ≤ 1 ∧ DecEnc (nicheLayout (nonZeroV 4) (zeroPat 4)) ∧
      NonePinned (nicheLayout (nonZeroV 4) (zeroPat 4)) (zeroPat 4) :=
  ⟨rfl, numInvalid_nonZeroV_le_one 4, ex_lawful.1, rfl⟩

/-! ### The documented-guarantee form -/

theorem ce_documented_drop_size_pin :
    (2 : Nat) ≠ 1 ∧ NonePinned (taggedLayout (payloadLayout (nonZeroV 1))) (zeroPat 2) ∧
      numInvalid (nonZeroV 1) ≤ 1 ∧
      DecEnc (taggedLayout (payloadLayout (nonZeroV 1))) ∧
      ¬ (FromBytes (taggedLayout (payloadLayout (nonZeroV 1))) ∧
        ∀ p, (taggedLayout (payloadLayout (nonZeroV 1))).dec p = some none ↔ p = zeroPat 2) :=
  ⟨by decide, rfl, numInvalid_nonZeroV_le_one 1, ex_taggedLayout.1.1,
    fun h => ex_taggedLayout.2 h.1⟩

theorem ce_documented_drop_none_pin :
    ¬ NonePinned swapLayout (zeroPat 1) ∧ numInvalid (nonZeroV 1) ≤ 1 ∧
      DecEnc swapLayout ∧
      ¬ (FromBytes swapLayout ∧ ∀ p, swapLayout.dec p = some none ↔ p = zeroPat 1) :=
  ⟨nex_nonePinned, numInvalid_nonZeroV_le_one 1, swapLayout_lawful.1,
    fun h => ce_zero_iff_none_drop_nonePinned.2.2.2 h.2⟩

theorem ce_documented_drop_numInvalid :
    NichePinned (nicheLayout geTwoV (zeroPat 1)) (zeroPat 1) ∧
      numInvalid geTwoV = 2 ∧
      DecEnc (nicheLayout geTwoV (zeroPat 1)) ∧
      ¬ (FromBytes (nicheLayout geTwoV (zeroPat 1)) ∧
        ∀ p, (nicheLayout geTwoV (zeroPat 1)).dec p = some none ↔ p = zeroPat 1) :=
  ⟨⟨rfl, rfl⟩, numInvalid_geTwoV, ce_canonical_fromBytes_drop_numInvalid.2.1,
    fun h => nicheLayout_geTwoV_zero_not_fromBytes h.1⟩

theorem ce_documented_drop_decEnc :
    NichePinned zeroDecLayout (zeroPat 1) ∧ numInvalid (nonZeroV 1) ≤ 1 ∧
      ¬ DecEnc zeroDecLayout ∧
      ¬ (FromBytes zeroDecLayout ∧ ∀ p, zeroDecLayout.dec p = some none ↔ p = zeroPat 1) :=
  ⟨⟨rfl, rfl⟩, numInvalid_nonZeroV_le_one 1, zeroDecLayout_not_decEnc,
    fun h => zeroDecLayout_not_fromBytes h.1⟩

theorem nv_documented :
    NichePinned (nicheLayout (nonZeroV 4) (zeroPat 4)) (zeroPat 4) ∧
      numInvalid (nonZeroV 4) ≤ 1 ∧
      DecEnc (nicheLayout (nonZeroV 4) (zeroPat 4)) :=
  ⟨ex_nichePinned, numInvalid_nonZeroV_le_one 4, ex_lawful.1⟩

/-- The identity of the payload's niche is not needed by the documented-guarantee form: for
`nonOneV` (only niche `1`, zero valid) the lawful `swap01Layout` is `NichePinned` at zero,
and both conclusions hold. -/
theorem documented_niche_identity_not_needed :
    NichePinned swap01Layout (zeroPat 1) ∧ numInvalid nonOneV ≤ 1 ∧ DecEnc swap01Layout ∧
      ¬ IsNiche nonOneV (zeroPat 1) ∧ FromBytes swap01Layout ∧
      (∀ p, swap01Layout.dec p = some none ↔ p = zeroPat 1) := by
  refine ⟨⟨rfl, rfl⟩, by rw [numInvalid_nonOneV]; exact Nat.le_refl 1, swap01Layout_lawful.1,
    by decide, fromBytes_of_forall_pat _ (by decide), ?_⟩
  exact dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical _ rfl
    swap01Layout_lawful.1 swap01Layout_lawful.2

/-! ### `NonZero`: the payload-to-option transmute determines the layout -/

theorem ce_nonePinned_zero_drop_decSomeTransparent :
    DecEnc swapLayout ∧ ¬ DecSomeTransparent swapLayout ∧
      ¬ NonePinned swapLayout (zeroPat 1) :=
  ⟨swapLayout_lawful.1, nex_decSomeTransparent, nex_nonePinned⟩

theorem ce_nonePinned_zero_drop_decEnc :
    DecSomeTransparent noneLostLayout ∧ ¬ DecEnc noneLostLayout ∧
      ¬ NonePinned noneLostLayout (zeroPat 1) := by
  refine ⟨noneLostLayout_decSomeTransparent, noneLostLayout_not_decEnc, ?_⟩
  unfold NonePinned; decide

theorem nv_decSomeTransparent_decEnc :
    DecSomeTransparent (nicheLayout (nonZeroV 4) (zeroPat 4)) ∧
      DecEnc (nicheLayout (nonZeroV 4) (zeroPat 4)) :=
  nv_isNiche_enc_none

theorem ce_layout_determined_drop_decSomeTransparent :
    DecEnc permLayout ∧ ¬ DecSomeTransparent permLayout ∧
      permLayout ≠ nicheLayout (nonZeroV 1) (zeroPat 1) := by
  refine ⟨permLayout_lawful.1, ?_, ?_⟩
  · intro h
    exact absurd (h oneNZ) (by decide)
  · intro h
    have := congrArg (fun L => L.enc (some oneNZ)) h
    exact absurd this (by decide)

theorem ce_layout_determined_drop_decEnc :
    DecSomeTransparent noneLostLayout ∧ ¬ DecEnc noneLostLayout ∧
      noneLostLayout ≠ nicheLayout (nonZeroV 1) (zeroPat 1) := by
  refine ⟨noneLostLayout_decSomeTransparent, noneLostLayout_not_decEnc, ?_⟩
  intro h
  have := congrArg (fun L => L.enc none) h
  exact absurd this (by decide)

/-! ## Result group 3 -/

/-- Positive control: for the one-byte `NonZero` payload (exactly one niche), every lawful
Some-transparent 1-byte layout puts `None` on the zero pattern. -/
theorem pc_nonZero_none_pattern_forced :
    ∀ L : Layout (Opt (nonZeroV 1)) 1, SomeTransparent L → Lawful L →
      NonePinned L (zeroPat 1) :=
  fun L hst hL => nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc L
    (decSomeTransparent_of_someTransparent_of_decEnc hst hL.1) hL.1

theorem nv_opt_bool_none_pattern_not_forced :
    SomeTransparent (nicheLayout boolV 2) ∧ Lawful (nicheLayout boolV 2) :=
  ⟨fun _ => rfl, opt_bool_lawful_layouts_in_one_and_two_bytes.1⟩

/-- Validity does not fix the size of `Option<NonZeroU8>` either: a 1-byte niche-filled and a
2-byte tagged layout are both lawful. Only the documented size guarantee pins it. -/
theorem nonZero_lawful_layouts_in_one_and_two_bytes :
    Lawful (nicheLayout (nonZeroV 1) (zeroPat 1)) ∧
      Lawful (taggedLayout (payloadLayout (nonZeroV 1))) :=
  ⟨nicheLayout_nonZero_lawful 1, taggedLayout_lawful (payloadLayout_lawful _)⟩

/-- No lawful 1-byte layout of `Opt boolV` is from-bytes (it has 3 values and 256
patterns); witnessed for the observed layout `nicheLayout boolV 2`. -/
theorem opt_bool_nicheLayout_not_fromBytes : ¬ FromBytes (nicheLayout boolV 2) := nex_fromBytes

/-! ## Result group 4 -/

theorem geTwoTags_injective : Function.Injective geTwoTags := by
  intro a b h
  revert a b
  decide

theorem nv_nicheLayoutK :
    Function.Injective geTwoTags ∧ (∀ i : Fin 2, IsNiche geTwoV (geTwoTags i)) ∧
      Lawful (nicheLayoutK geTwoV geTwoTags) :=
  ⟨geTwoTags_injective, by decide, ex_nicheLayoutK⟩

theorem ce_le_numInvalid_drop_size :
    ¬ ((2 : Nat) ≤ 1) ∧ DecEnc ext1AllTaggedLayout ∧ ¬ (1 ≤ numInvalid (allV 1)) :=
  ⟨by decide, ext1AllTaggedLayout_lawful.1, by rw [numInvalid_allV_one]; decide⟩

theorem ce_le_numInvalid_drop_decEnc :
    (1 : Nat) ≤ 1 ∧ ¬ DecEnc ext1AllZeroDecLayout ∧ ¬ (1 ≤ numInvalid (allV 1)) := by
  refine ⟨Nat.le_refl 1, ?_, by rw [numInvalid_allV_one]; decide⟩
  intro h
  have := h (.inl 0)
  cases this

/-- Positive control: in one more byte, an enum with more extra variants than niches has a
lawful layout (here one extra variant over a niche-free byte, tagged in 2 bytes). -/
theorem pc_le_numInvalid : Lawful ext1AllTaggedLayout ∧ ¬ (1 ≤ numInvalid (allV 1)) :=
  ⟨ext1AllTaggedLayout_lawful, by rw [numInvalid_allV_one]; decide⟩

theorem nv_le_numInvalid : (1 : Nat) ≤ 1 ∧ DecEnc ext1NonZeroLayout :=
  ⟨Nat.le_refl 1, ext1NonZeroLayout_lawful.1⟩

/-- The strictly-smaller case `m < n` of the size hypothesis is inhabited: one extra variant
over the 2-byte payload `sparse2V` has a lawful 1-byte layout. -/
theorem nv_le_numInvalid_size_lt : (1 : Nat) ≤ 2 ∧ DecEnc sparse2In1Byte :=
  ⟨by decide, sparse2In1Byte_lawful.1⟩

/-- Both sides of the cardinality characterization hold at `k = 2` over `geTwoV`, with the
exposed witness `nicheLayoutK geTwoV (firstNiches geTwoV 2)`. -/
theorem nv_le_numInvalid_iff :
    2 ≤ numInvalid geTwoV ∧ Lawful (nicheLayoutK geTwoV (firstNiches geTwoV 2)) := by
  refine ⟨by rw [numInvalid_geTwoV]; exact Nat.le_refl 2, ?_⟩
  exact ⟨by unfold DecEnc; decide, canonical_of_forall_pat _ (by decide)⟩

/-- Positive control: the two-level option over an `n`-byte `NonZero` payload has a lawful
layout in `n + 1` bytes (a tag byte over the niche-filled inner option). -/
theorem pc_opt_opt_nonZero (n : Nat) :
    Lawful (taggedLayout (nicheLayout (nonZeroV n) (zeroPat n))) :=
  taggedLayout_lawful (nicheLayout_nonZero_lawful n)

/-- One level of option over the `n`-byte `NonZero` payload does fit in `n` bytes. -/
theorem pc_opt_nonZero_one_level (n : Nat) : Lawful (nicheLayout (nonZeroV n) (zeroPat n)) :=
  nicheLayout_nonZero_lawful n

/-- Two dataless variants over a payload with exactly two niches fit in the payload's size:
the enum `ExtEnum 2 geTwoV` (two dataless variants tagged `0` and `1` beside the one-byte
payload `geTwoV`) has a lawful 1-byte layout, and `geTwoV` has exactly two niches. The
statement is about `ExtEnum 2 geTwoV`, the shape of `Option<Option<bool>>`; it is not
transported to `Option (Opt geTwoV)`. -/
theorem opt_opt_two_niches_one_byte :
    Lawful (nicheLayoutK geTwoV geTwoTags) ∧ numInvalid geTwoV = 2 :=
  ⟨ex_nicheLayoutK, numInvalid_geTwoV⟩

theorem nv_opt_opt_nonZero (n : Nat) : Nonempty (Layout (Option (Opt (nonZeroV n))) n) :=
  ⟨⟨fun _ => zeroPat n, fun _ => none⟩⟩

/-! ## Two-level option over `NonZero`: what 257 values in 2 bytes do and do not exclude -/

theorem mem_valList {n : Nat} (V : Validity n) (v : Val V) : v ∈ Counting.valList V := by
  unfold Counting.valList
  rw [List.mem_pmap]
  exact ⟨v.1, List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using v.2⟩, rfl⟩

/-- Counting bound for the two-level option over `V`: if a layout of `Option (Opt V)` in `m`
bytes is canonical and every pattern decodes, then the encoder is onto all `256 ^ m`
patterns, so `256 ^ m` is at most the number of values `2 + (256 ^ n - numInvalid V)`. -/
theorem optOpt_card_bound_of_canonical_of_fromBytes {n m : Nat} (V : Validity n)
    (L : Layout (Option (Opt V)) m) (hcan : Canonical L) (hfb : FromBytes L) :
    256 ^ m + numInvalid V ≤ 256 ^ n + 2 := by
  let elems : List (Option (Opt V)) :=
    none :: some none :: (Counting.valList V).map (fun v => some (some v))
  have hall : ∀ x, x ∈ elems := by
    intro x
    match x with
    | none => exact List.mem_cons_self ..
    | some none => exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    | some (some v) =>
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨v, mem_valList V v, rfl⟩))
  have hsub : ∀ p ∈ List.finRange (256 ^ m), p ∈ elems.map L.enc := by
    intro p _
    obtain ⟨x, hx⟩ := hfb p
    exact List.mem_map.mpr ⟨x, hall x, hcan p x hx⟩
  have hle := Counting.nodup_length_le_of_subset (List.nodup_finRange _) hsub
  simp only [List.length_finRange, List.length_map, elems, List.length_cons,
    Counting.valList_length] at hle
  have hsum := Counting.numValid_add_numInvalid V
  omega

/-- With canonical decoding, no 2-byte layout of the two-level option over the 1-byte
`NonZero` payload (257 values) makes every one of the 65536 patterns decode. -/
theorem optOptNonZero_two_bytes_not_canonical_and_fromBytes
    (L : Layout (Option (Opt (nonZeroV 1))) 2) : ¬ (Canonical L ∧ FromBytes L) := by
  rintro ⟨hcan, hfb⟩
  have h := optOpt_card_bound_of_canonical_of_fromBytes (nonZeroV 1) L hcan hfb
  rw [numInvalid_nonZeroV] at h
  have h2 : (256 : Nat) ^ 2 = 65536 := rfl
  have h1 : (256 : Nat) ^ 1 = 256 := rfl
  omega

/-- A 2-byte layout of the two-level option over the 1-byte `NonZero` payload: the tagged
layout over the niche-filled inner option, except that every pattern the tagged layout
rejects decodes as the outer `None`. -/
def optOptNonZeroTwoByteLoose : Layout (Option (Opt (nonZeroV 1))) 2 where
  enc := (taggedLayout (nicheLayout (nonZeroV 1) (zeroPat 1))).enc
  dec p :=
    match (taggedLayout (nicheLayout (nonZeroV 1) (zeroPat 1))).dec p with
    | some x => some x
    | none => some none

/-- Without canonical decoding the counting bound gives nothing: `optOptNonZeroTwoByteLoose`
satisfies decode-after-encode and every pattern decodes, but decoding is not canonical. -/
theorem optOptNonZeroTwoByteLoose_decEnc_fromBytes_not_canonical :
    DecEnc optOptNonZeroTwoByteLoose ∧ FromBytes optOptNonZeroTwoByteLoose ∧
      ¬ Canonical optOptNonZeroTwoByteLoose := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have h := (taggedLayout_decEnc (nicheLayout_nonZero_lawful 1).1) x
    simp only [optOptNonZeroTwoByteLoose, h]
  · intro p
    simp only [optOptNonZeroTwoByteLoose]
    cases h : (taggedLayout (nicheLayout (nonZeroV 1) (zeroPat 1))).dec p with
    | some x => exact ⟨x, rfl⟩
    | none => exact ⟨none, rfl⟩
  · intro hcan
    have hd : optOptNonZeroTwoByteLoose.dec 2 = some none := by decide
    have he := hcan 2 none hd
    exact absurd he (by decide)

end Toy.Niche
