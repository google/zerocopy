import Toy.Niche.Counting

/-!
# Main results

Result groups:

1. Niche filling: a niche-filled layout with `None ↦ q` is lawful iff `q` is a niche;
   with the payload-to-option transmute (`DecSomeTransparent`) and decode-after-encode,
   `None` must sit on a niche; Some-transparent lawful layouts in the payload's size are
   exactly the niche-filled ones.
2. What the documented guarantee buys (the `NonZero` case) and which hypotheses each
   conclusion actually uses.
3. What validity alone does not buy (the `bool`-like payload).
4. Cardinality: `k` extra dataless variants fit in the payload's `n` bytes under some
   lawful layout iff `k ≤ numInvalid V`, with the witness layout exposed.
-/

namespace Toy.Niche

variable {α β : Type} {m n : Nat}

/-! ## Result group 1: niche filling -/

/-- If every valid payload pattern decodes to `Some` of itself (the payload-to-option
transmute) and decode-after-encode holds, then the pattern of `None` is a niche (invalid
for the payload). Any encoder for `Some` and any decoder are allowed; the layout has the
payload's size `n` (fixed by the type of `L`). -/
theorem isNiche_enc_none_of_decSomeTransparent_of_decEnc {V : Validity n}
    (L : Layout (Opt V) n) (hdst : DecSomeTransparent L) (hde : DecEnc L) :
    IsNiche V (L.enc none) := by
  unfold IsNiche
  cases hv : V (L.enc none) with
  | false => rfl
  | true =>
    exfalso
    have h1 := hdst ⟨L.enc none, hv⟩
    rw [hde none] at h1
    cases h1

/-- Niche-filling characterization: the niche-filled layout with `None ↦ q` is lawful iff
`q` is invalid for the payload. -/
theorem nicheLayout_lawful_iff_isNiche (V : Validity n) (q : Pat n) :
    Lawful (nicheLayout V q) ↔ IsNiche V q := by
  constructor
  · intro h
    exact isNiche_enc_none_of_decSomeTransparent_of_decEnc (nicheLayout V q)
      (decSomeTransparent_of_someTransparent_of_decEnc (nicheLayout_someTransparent V q) h.1)
      h.1
  · intro hq
    exact ⟨nicheLayout_decEnc_of_isNiche hq, nicheLayout_canonical V q⟩

/-- Classification: a layout of `Opt V` in the payload's size is Some-transparent and lawful
iff `None`'s pattern is a niche and the layout *is* the niche-filled layout at that niche.
(For lawful layouts `SomeTransparent` and `DecSomeTransparent` coincide:
`someTransparent_iff_decSomeTransparent_of_lawful`.) -/
theorem someTransparent_lawful_iff_eq_nicheLayout {V : Validity n} (L : Layout (Opt V) n) :
    (SomeTransparent L ∧ Lawful L) ↔
      (IsNiche V (L.enc none) ∧ L = nicheLayout V (L.enc none)) := by
  constructor
  · rintro ⟨hst, hde, hcan⟩
    have hdst := decSomeTransparent_of_someTransparent_of_decEnc hst hde
    have hq := isNiche_enc_none_of_decSomeTransparent_of_decEnc L hdst hde
    refine ⟨hq, ?_⟩
    apply Layout.ext
    · funext x
      cases x with
      | none => rfl
      | some v => exact hst v
    · funext p
      show L.dec p = if p = L.enc none then some none
        else if h : V p = true then some (some ⟨p, h⟩) else none
      by_cases hpq : p = L.enc none
      · rw [ite_eq_left hpq, hpq]
        exact hde none
      · rw [ite_eq_right hpq]
        by_cases hv : V p = true
        · rw [dite_eq_left hv]
          exact hdst ⟨p, hv⟩
        · rw [dite_eq_right hv]
          cases hd : L.dec p with
          | none => rfl
          | some x =>
            exfalso
            have he := hcan p x hd
            cases x with
            | none => exact hpq he.symm
            | some v =>
              rw [hst] at he
              apply hv
              rw [← he]
              exact v.2
  · rintro ⟨hq, hL⟩
    generalize hq' : L.enc none = q at hq hL
    subst hL
    exact ⟨fun _ => rfl, (nicheLayout_lawful_iff_isNiche V q).mpr hq⟩

/-! ## Result group 2: what the documented guarantee buys -/

/-- Pigeonhole core of group 2: if a layout of `Opt V` has the payload's size `n`, the
payload has at most one niche, and decode-after-encode holds, then the encoder is a
bijection onto all `256 ^ n` patterns, so decoding is canonical and every pattern decodes.
Neither the pattern of `None` nor canonical decoding is assumed. -/
theorem opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc
    (V : Validity n) (L : Layout (Opt V) m) (hsize : m = n) (hV : numInvalid V ≤ 1)
    (hde : DecEnc L) : Canonical L ∧ FromBytes L := by
  subst hsize
  have hinj := enc_injective_of_decEnc hde
  -- The encoder maps the `1 + #valid` values injectively into the `256 ^ m` patterns,
  -- and `1 + #valid ≥ #valid + numInvalid V = 256 ^ m`, so it is onto.
  let elems : List (Opt V) := none :: (Counting.valList V).map some
  have hnd_elems : elems.Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, ?_⟩
    · intro h; rw [List.mem_map] at h; obtain ⟨_, _, h⟩ := h; cases h
    · exact Counting.nodup_map_of_injOn (fun a _ b _ h => by cases h; rfl)
        (Counting.valList_nodup V)
  have hnd_img : (elems.map L.enc).Nodup :=
    Counting.nodup_map_of_injOn (fun a _ b _ hab => hinj a b hab) hnd_elems
  have hsum := Counting.numValid_add_numInvalid V
  have hlen_ge : (List.finRange (256 ^ m)).length ≤ (elems.map L.enc).length := by
    simp only [List.length_finRange, List.length_map, elems, List.length_cons,
      Counting.valList_length]
    omega
  have hsurj : ∀ p : Pat m, ∃ x : Opt V, L.enc x = p := by
    intro p
    have hp := Counting.mem_of_nodup_of_length_ge hnd_img (fun q _ => List.mem_finRange q)
      hlen_ge p (List.mem_finRange p)
    obtain ⟨x, _, hx⟩ := List.mem_map.mp hp
    exact ⟨x, hx⟩
  refine ⟨?_, ?_⟩
  · intro p x hpx
    obtain ⟨y, rfl⟩ := hsurj p
    rw [hde y] at hpx
    cases hpx
    rfl
  · intro p
    obtain ⟨x, rfl⟩ := hsurj p
    exact ⟨x, hde x⟩

/-- Zero is exactly `None`, from the `None ↦ 0` pin and both laws (any payload type, any
size). A reference point: compare the canonical-free version
`dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc`. -/
theorem dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical
    (L : Layout (Option β) m) (hnone : NonePinned L (zeroPat m)) (hde : DecEnc L)
    (hcan : Canonical L) : ∀ p, L.dec p = some none ↔ p = zeroPat m := by
  intro p
  constructor
  · intro h
    rw [← hnone]
    exact (hcan p none h).symm
  · intro h
    rw [h, ← hnone]
    exact hde none

/-- Zero is exactly `None` without assuming canonical decoding: from the `None ↦ 0` pin, the
size pin, at most one payload niche, and decode-after-encode (canonicity is then forced by
`opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc`). -/
theorem dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc
    (V : Validity n) (L : Layout (Opt V) m) (hsize : m = n) (hV : numInvalid V ≤ 1)
    (hde : DecEnc L) (hnone : NonePinned L (zeroPat m)) :
    ∀ p, L.dec p = some none ↔ p = zeroPat m :=
  dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_decEnc_of_canonical L hnone hde
    (opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc V L hsize hV hde).1

/-- The documented-guarantee form: under `NichePinned L 0` (size `n`, `None ↦ 0`), with at
most one payload niche and decode-after-encode, every pattern decodes and the zero pattern
is exactly `None`. The identity of the payload's niche is not used; for `NonZero` payloads
`numInvalid V ≤ 1` follows from "zero is the only niche"
(`numInvalid_le_one_of_only_niche_zero`). -/
theorem opt_fromBytes_and_zero_iff_none_of_nichePinned_zero_of_numInvalid_le_one_of_decEnc
    (V : Validity n) (L : Layout (Opt V) m) (hpin : NichePinned L (zeroPat m))
    (hV : numInvalid V ≤ 1) (hde : DecEnc L) :
    FromBytes L ∧ ∀ p, L.dec p = some none ↔ p = zeroPat m :=
  ⟨(opt_canonical_and_fromBytes_of_size_eq_of_numInvalid_le_one_of_decEnc V L hpin.1 hV hde).2,
    dec_eq_some_none_iff_eq_zero_of_nonePinned_zero_of_size_eq_of_numInvalid_le_one_of_decEnc
      V L hpin.1 hV hde hpin.2⟩

/-- For a `NonZero` payload, the payload-to-option transmute (`DecSomeTransparent`) and
decode-after-encode force `None ↦ 0` (so the `None ↦ 0` pin is derivable from them). -/
theorem nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc
    (L : Layout (Opt (nonZeroV n)) n) (hdst : DecSomeTransparent L) (hde : DecEnc L) :
    NonePinned L (zeroPat n) :=
  (isNiche_nonZeroV_iff _).mp (isNiche_enc_none_of_decSomeTransparent_of_decEnc L hdst hde)

/-- For a `NonZero` payload, the payload-to-option transmute (`DecSomeTransparent`) and
decode-after-encode determine the whole layout: it is the niche-filled layout with
`None ↦ 0`. Neither canonical decoding nor encoder-side transparency is assumed. -/
theorem nonZero_layout_eq_nicheLayout_zero_of_decSomeTransparent_of_decEnc
    (L : Layout (Opt (nonZeroV n)) n) (hdst : DecSomeTransparent L) (hde : DecEnc L) :
    L = nicheLayout (nonZeroV n) (zeroPat n) := by
  have hz : L.enc none = zeroPat n :=
    nonePinned_zero_of_nonZero_of_decSomeTransparent_of_decEnc L hdst hde
  have hdec : ∀ p : Pat n, L.dec p = (nicheLayout (nonZeroV n) (zeroPat n)).dec p := by
    intro p
    show L.dec p = if p = zeroPat n then some none
      else if h : nonZeroV n p = true then some (some ⟨p, h⟩) else none
    by_cases hp : p = zeroPat n
    · rw [ite_eq_left hp, hp, ← hz]
      exact hde none
    · rw [ite_eq_right hp]
      have hv : nonZeroV n p = true := by
        cases hw : nonZeroV n p with
        | true => rfl
        | false => exact absurd ((isNiche_nonZeroV_iff p).mp hw) hp
      rw [dite_eq_left hv]
      exact hdst ⟨p, hv⟩
  apply Layout.ext
  · funext x
    cases x with
    | none => exact hz
    | some v =>
      have h1 := hde (some v)
      rw [hdec] at h1
      simp only [nicheLayout] at h1
      split at h1
      · cases h1
      · split at h1
        · exact congrArg Subtype.val (Option.some.inj (Option.some.inj h1))
        · cases h1
  · funext p
    exact hdec p

/-! ## Result group 3: what validity alone does not buy (`bool`-like payload) -/

/-- The `bool`-like payload (valid patterns `0`, `1` of 256) has a lawful niche-filled
layout in 1 byte (`None ↦ 2`) and a lawful separately tagged layout in 2 bytes. -/
theorem opt_bool_lawful_layouts_in_one_and_two_bytes :
    Lawful (nicheLayout boolV 2) ∧ Lawful (taggedLayout (payloadLayout boolV)) :=
  ⟨(nicheLayout_lawful_iff_isNiche _ _).mpr (by decide),
    taggedLayout_lawful (payloadLayout_lawful _)⟩

/-- No pattern is forced to be `None`'s for the `bool`-like payload, even among 1-byte
layouts that are lawful and Some-transparent. -/
theorem opt_bool_none_pattern_not_forced_by_someTransparent_lawful (q : Pat 1) :
    ¬ ∀ L : Layout (Opt boolV) 1, SomeTransparent L → Lawful L → NonePinned L q := by
  intro h
  by_cases hq : q = 2
  · have h3 := h (nicheLayout boolV 3) (fun _ => rfl)
      ((nicheLayout_lawful_iff_isNiche _ _).mpr (by decide))
    unfold NonePinned at h3
    rw [hq] at h3
    exact absurd h3 (by decide)
  · have h2 := h (nicheLayout boolV 2) (fun _ => rfl)
      ((nicheLayout_lawful_iff_isNiche _ _).mpr (by decide))
    exact hq h2.symm

/-! ## Result group 4: cardinality -/

/-- `k`-variant niche filling is lawful iff the tag patterns are pairwise distinct niches. -/
theorem nicheLayoutK_lawful_iff_injective_and_isNiche {k : Nat} (V : Validity n)
    (t : Fin k → Pat n) :
    Lawful (nicheLayoutK V t) ↔ (Function.Injective t ∧ ∀ i, IsNiche V (t i)) := by
  constructor
  · intro hL
    have hinj := enc_injective_of_decEnc hL.1
    refine ⟨fun i j hij => by cases hinj (.inl i) (.inl j) hij; rfl, fun i => ?_⟩
    unfold IsNiche
    cases hv : V (t i) with
    | false => rfl
    | true => exfalso; cases hinj (.inl i) (.inr ⟨t i, hv⟩) rfl
  · rintro ⟨ht, hniche⟩
    refine ⟨?_, ?_⟩
    · intro x
      cases x with
      | inl i =>
        simp only [nicheLayoutK]
        cases hf : (List.finRange k).find? (fun j => t j == t i) with
        | some j =>
          have hmem := List.find?_some hf
          simp only [beq_iff_eq] at hmem
          rw [ht hmem]
        | none =>
          exfalso
          have := List.find?_eq_none.mp hf i (List.mem_finRange i)
          simp at this
      | inr v =>
        simp only [nicheLayoutK]
        cases hf : (List.finRange k).find? (fun j => t j == v.val) with
        | some j =>
          exfalso
          have hmem := List.find?_some hf
          simp only [beq_iff_eq] at hmem
          have hv := v.2
          rw [← hmem] at hv
          unfold IsNiche at hniche
          rw [hniche j] at hv
          cases hv
        | none => simp [v.2]
    · intro p x hp
      simp only [nicheLayoutK] at hp
      split at hp
      · rename_i i hf
        cases hp
        have hmem := List.find?_some hf
        simp only [beq_iff_eq] at hmem
        exact hmem
      · split at hp
        · cases hp; rfl
        · cases hp

/-- Pigeonhole: a decode-after-encode layout of an enum with `k` extra dataless variants over
`V`, in at most the payload's size, needs `k ≤ numInvalid V`. -/
theorem le_numInvalid_of_decEnc_of_size_le {k : Nat} (V : Validity n)
    (L : Layout (ExtEnum k V) m) (hsize : m ≤ n) (hde : DecEnc L) : k ≤ numInvalid V := by
  have hinj := enc_injective_of_decEnc hde
  -- The encoder maps the `k + #valid` values injectively into `256 ^ m ≤ 256 ^ n` patterns.
  let elems : List (ExtEnum k V) :=
    (List.finRange k).map Sum.inl ++ (Counting.valList V).map Sum.inr
  have hnd_elems : elems.Nodup := by
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact Counting.nodup_map_of_injOn (fun a _ b _ h => by cases h; rfl)
        (List.nodup_finRange k)
    · exact Counting.nodup_map_of_injOn (fun a _ b _ h => by cases h; rfl)
        (Counting.valList_nodup V)
    · intro x hx y hy hxy
      rw [List.mem_map] at hx hy
      obtain ⟨a, _, rfl⟩ := hx
      obtain ⟨b, _, rfl⟩ := hy
      cases hxy
  have hnd_img : (elems.map L.enc).Nodup :=
    Counting.nodup_map_of_injOn (fun a _ b _ hab => hinj a b hab) hnd_elems
  have hle := Counting.nodup_length_le_of_subset hnd_img (fun p _ => List.mem_finRange p)
  simp only [List.length_map, elems, List.length_append, List.length_finRange,
    Counting.valList_length] at hle
  have hsum := Counting.numValid_add_numInvalid V
  have hpow : 256 ^ m ≤ 256 ^ n := Nat.pow_le_pow_right (by decide) hsize
  omega

/-- Cardinality characterization with the witness exposed: `k ≤ numInvalid V` holds iff `k`
extra dataless variants over `V` have some lawful layout in the payload's `n` bytes, iff the
specific layout `nicheLayoutK V (firstNiches V k)` (the first `k` niches as tags) is
lawful. -/
theorem le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches
    (V : Validity n) (k : Nat) :
    (k ≤ numInvalid V ↔ ∃ L : Layout (ExtEnum k V) n, Lawful L) ∧
      (k ≤ numInvalid V ↔ Lawful (nicheLayoutK V (firstNiches V k))) := by
  have hwit : k ≤ numInvalid V → Lawful (nicheLayoutK V (firstNiches V k)) := fun hk =>
    (nicheLayoutK_lawful_iff_injective_and_isNiche V _).mpr
      (firstNiches_injective_and_isNiche_of_le_numInvalid V k hk)
  refine ⟨⟨fun hk => ⟨_, hwit hk⟩, ?_⟩, ⟨hwit, ?_⟩⟩
  · rintro ⟨L, hL⟩
    exact le_numInvalid_of_decEnc_of_size_le V L (Nat.le_refl n) hL.1
  · intro hL
    exact le_numInvalid_of_decEnc_of_size_le V _ (Nat.le_refl n) hL.1

/-- The two-level option over an `n`-byte `NonZero` payload (`2 + (256 ^ n - 1)` values) has
no decode-after-encode layout in `n` bytes. For `n = 1` this is
`Option<Option<NonZeroU8>>` in one byte (257 values, 256 patterns). -/
theorem opt_opt_nonZero_no_decEnc_layout_in_payload_size
    (L : Layout (Option (Opt (nonZeroV n))) n) : ¬ DecEnc L := by
  intro hde
  let f : ExtEnum 2 (nonZeroV n) → Option (Opt (nonZeroV n))
    | .inl i => if i.val = 0 then none else some none
    | .inr v => some (some v)
  let g : Option (Opt (nonZeroV n)) → ExtEnum 2 (nonZeroV n)
    | none => .inl 0
    | some none => .inl 1
    | some (some v) => .inr v
  have hgf : ∀ b, g (f b) = b := by
    intro b
    cases b with
    | inl i =>
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    | inr v => rfl
  have hk := le_numInvalid_of_decEnc_of_size_le (nonZeroV n) (L.comap f g) (Nat.le_refl n)
    (comap_decEnc hgf hde)
  rw [numInvalid_nonZeroV] at hk
  omega

end Toy.Niche
