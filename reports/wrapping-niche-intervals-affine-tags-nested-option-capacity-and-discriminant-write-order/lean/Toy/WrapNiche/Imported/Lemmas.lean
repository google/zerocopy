/-
Imported module (not a result of this package).

Copied from the published corpus package `enum-niche-layout-guarantees-and-validity-invariants`
(repository `google/zerocopy`, branch `reference`, published at commit
`00c8f874bf1e70c933b7a2ea2572a76c1baa7327`; Lean sources unchanged at the latest correction
commit `f9bee82a6d3f8bb6698b4c9e716138018db94d4d`), file
`reports/enum-niche-layout-guarantees-and-validity-invariants/lean/Toy/Niche/Lemmas.lean`,
whose SHA-256 at both commits is
`b3b977d1e5444ff7c72fc1bab2b4624eb93974f290c423a64bd6685357e751c0`.
The only edits are the namespace (`Toy.Niche` renamed to `Toy.WrapNiche.Imported`) and this
header. Declaration names, statements and proofs are otherwise verbatim.
-/

import Toy.WrapNiche.Imported.Defs

/-!
# Supporting lemmas (fully proved)

Lawfulness of the constructions, transport along `Layout.comap`, the byte-level reading
of the zero pattern, and the niche count of `NonZero` validity.
-/

namespace Toy.WrapNiche.Imported

variable {α β : Type} {m n : Nat}

/-! ## Basic consequences of the laws -/

/-- `DecEnc` makes the encoder injective. -/
theorem enc_injective_of_decEnc {L : Layout α m} (h : DecEnc L) :
    ∀ x y, L.enc x = L.enc y → x = y := by
  intro x y hxy
  have hx := h x
  rw [hxy, h y] at hx
  exact (Option.some.inj hx).symm

/-! ## Byte-level reading of patterns -/

theorem div_div_256 (x i : Nat) : x / 256 ^ (i + 1) = x / 256 / 256 ^ i := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- The all-zero pattern is exactly the pattern all of whose bytes are zero, so `zeroPat n`
faithfully represents `[0u8; n]`. -/
theorem eq_zeroPat_iff_bytes_zero (p : Pat n) : p = zeroPat n ↔ ∀ i : Fin n, byteAt p i = 0 := by
  constructor
  · intro h i
    subst h
    simp [byteAt, zeroPat]
  · induction n with
    | zero =>
      intro _
      apply Fin.ext
      have h1 : p.val < 1 := p.isLt
      show p.val = 0
      omega
    | succ k ih =>
      intro h
      have h0 := h ⟨0, by omega⟩
      simp only [byteAt, Fin.ext_iff, Nat.pow_zero, Nat.div_one] at h0
      have hlt : p.val / 256 < 256 ^ k := tag_dec_lt p
      have hq := ih ⟨p.val / 256, hlt⟩ (by
        intro i
        have hi := h ⟨i.val + 1, by omega⟩
        simp only [byteAt, Fin.ext_iff] at hi ⊢
        rw [div_div_256] at hi
        exact hi)
      simp only [zeroPat, Fin.ext_iff] at hq ⊢
      have := Nat.mod_add_div p.val 256
      omega

/-! ## Encoder-side and decoder-side transparency -/

/-- Encoder-side transparency plus decode-after-encode give decoder-side transparency:
a valid payload pattern decodes to `Some` of itself. -/
theorem decSomeTransparent_of_someTransparent_of_decEnc {V : Validity n} {L : Layout (Opt V) n}
    (hst : SomeTransparent L) (hde : DecEnc L) : DecSomeTransparent L := by
  intro v
  have := hde (some v)
  rwa [hst] at this

/-- Decoder-side transparency plus canonical decoding give encoder-side transparency. -/
theorem someTransparent_of_decSomeTransparent_of_canonical {V : Validity n}
    {L : Layout (Opt V) n} (hdst : DecSomeTransparent L) (hcan : Canonical L) :
    SomeTransparent L :=
  fun v => hcan _ _ (hdst v)

/-- For lawful layouts the two transparency notions coincide. -/
theorem someTransparent_iff_decSomeTransparent_of_lawful {V : Validity n}
    {L : Layout (Opt V) n} (hL : Lawful L) : SomeTransparent L ↔ DecSomeTransparent L :=
  ⟨fun h => decSomeTransparent_of_someTransparent_of_decEnc h hL.1,
   fun h => someTransparent_of_decSomeTransparent_of_canonical h hL.2⟩

/-! ## The payload layout -/

theorem payloadLayout_lawful (V : Validity n) : Lawful (payloadLayout V) := by
  constructor
  · intro v
    simp [payloadLayout, v.2]
  · intro p v hp
    simp only [payloadLayout] at hp
    split at hp
    · cases hp; rfl
    · cases hp

/-! ## Niche filling for one extra variant -/

theorem nicheLayout_decEnc_of_isNiche {V : Validity n} {q : Pat n} (hq : IsNiche V q) :
    DecEnc (nicheLayout V q) := by
  intro x
  cases x with
  | none => simp [nicheLayout]
  | some v =>
    have hne : v.val ≠ q := by
      intro h; have := v.2; rw [h] at this; unfold IsNiche at hq; rw [hq] at this; cases this
    simp [nicheLayout, hne, v.2]

theorem nicheLayout_canonical (V : Validity n) (q : Pat n) : Canonical (nicheLayout V q) := by
  intro p x hp
  simp only [nicheLayout] at hp
  split at hp
  · cases hp; simp [nicheLayout, *]
  · split at hp
    · cases hp; rfl
    · cases hp

theorem nicheLayout_someTransparent (V : Validity n) (q : Pat n) :
    SomeTransparent (nicheLayout V q) := fun _ => rfl

theorem nicheLayout_decSomeTransparent_of_isNiche {V : Validity n} {q : Pat n}
    (hq : IsNiche V q) : DecSomeTransparent (nicheLayout V q) :=
  decSomeTransparent_of_someTransparent_of_decEnc (nicheLayout_someTransparent V q)
    (nicheLayout_decEnc_of_isNiche hq)

/-! ## Separate-tag layouts -/

theorem taggedLayout_decEnc {L : Layout α n} (h : DecEnc L) : DecEnc (taggedLayout L) := by
  intro x
  cases x with
  | none => simp [taggedLayout, zeroPat]
  | some a =>
    have h1 : (1 + 256 * (L.enc a).val) % 256 = 1 := by omega
    have h2 : (1 + 256 * (L.enc a).val) / 256 = (L.enc a).val := by omega
    have h3 : (⟨(1 + 256 * (L.enc a).val) / 256, tag_dec_lt ⟨1 + 256 * (L.enc a).val,
        tag_enc_lt _ (L.enc a).isLt⟩⟩ : Pat n) = L.enc a := Fin.ext h2
    have hne : ¬ (1 + 256 * (L.enc a).val = 0) := by omega
    simp only [taggedLayout]
    rw [ite_eq_right hne, ite_eq_left h1, h3, h a]
    rfl

theorem taggedLayout_canonical {L : Layout α n} (h : Canonical L) :
    Canonical (taggedLayout L) := by
  intro p x hp
  simp only [taggedLayout] at hp
  split at hp
  · cases hp; apply Fin.ext; simp [taggedLayout, zeroPat]; omega
  · split at hp
    · rw [Option.map_eq_some_iff] at hp
      obtain ⟨a, ha, rfl⟩ := hp
      have he := h _ _ ha
      apply Fin.ext
      simp only [taggedLayout, he]
      have := Nat.mod_add_div p.val 256
      omega
    · cases hp

theorem taggedLayout_lawful {L : Layout α n} (h : Lawful L) : Lawful (taggedLayout L) :=
  ⟨taggedLayout_decEnc h.1, taggedLayout_canonical h.2⟩

theorem taggedLooseLayout_decEnc {L : Layout α n} (h : DecEnc L) :
    DecEnc (taggedLooseLayout L) := by
  intro x
  cases x with
  | none => simp [taggedLooseLayout, taggedLayout, zeroPat]
  | some a =>
    have h1 : (1 + 256 * (L.enc a).val) % 256 = 1 := by omega
    have h2 : (1 + 256 * (L.enc a).val) / 256 = (L.enc a).val := by omega
    have h3 : (⟨(1 + 256 * (L.enc a).val) / 256, tag_dec_lt ⟨1 + 256 * (L.enc a).val,
        tag_enc_lt _ (L.enc a).isLt⟩⟩ : Pat n) = L.enc a := Fin.ext h2
    have hne : ¬ ((1 + 256 * (L.enc a).val) % 256 = 0) := by omega
    simp only [taggedLooseLayout, taggedLayout]
    rw [ite_eq_right hne, ite_eq_left h1, h3, h a]
    rfl

/-! ## Transport -/

theorem comap_decEnc {f : β → α} {g : α → β} {L : Layout α m} (hgf : ∀ b, g (f b) = b)
    (h : DecEnc L) : DecEnc (L.comap f g) := by
  intro b
  simp [Layout.comap, h (f b), hgf b]

theorem comap_canonical {f : β → α} {g : α → β} {L : Layout α m} (hfg : ∀ a, f (g a) = a)
    (h : Canonical L) : Canonical (L.comap f g) := by
  intro p b hp
  simp only [Layout.comap, Option.map_eq_some_iff] at hp
  obtain ⟨a, ha, rfl⟩ := hp
  simp only [Layout.comap, hfg a]
  exact h _ _ ha

theorem comap_lawful {f : β → α} {g : α → β} {L : Layout α m} (hgf : ∀ b, g (f b) = b)
    (hfg : ∀ a, f (g a) = a) (h : Lawful L) : Lawful (L.comap f g) :=
  ⟨comap_decEnc hgf h.1, comap_canonical hfg h.2⟩

theorem ext1ToOpt_optToExt1 {V : Validity n} (x : Opt V) : ext1ToOpt (optToExt1 x) = x := by
  cases x <;> rfl

theorem optToExt1_ext1ToOpt {V : Validity n} (y : ExtEnum 1 V) : optToExt1 (ext1ToOpt y) = y := by
  cases y with
  | inl i => cases i using Fin.cases with
    | zero => rfl
    | succ j => exact j.elim0
  | inr v => rfl

/-! ## Niche counts -/

theorem countP_val_eq_zero_finRange (N : Nat) (hN : 0 < N) :
    ((List.finRange N).filter (fun p : Fin N => !(p.val != 0))).length = 1 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [List.finRange_succ, List.filter_cons]
  have hnil : (List.map Fin.succ (List.finRange M)).filter
      (fun p : Fin (M + 1) => !(p.val != 0)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    simp
  have h0 : (!((0 : Fin (M + 1)).val != 0)) = true := by simp
  rw [ite_eq_left h0, hnil]
  rfl

/-- `NonZero` validity has exactly one niche (the all-zero pattern). -/
theorem numInvalid_nonZeroV (n : Nat) : numInvalid (nonZeroV n) = 1 :=
  countP_val_eq_zero_finRange (256 ^ n) (pat_card_pos n)

/-- The only niche of `NonZero` validity is the all-zero pattern. -/
theorem isNiche_nonZeroV_iff (p : Pat n) : IsNiche (nonZeroV n) p ↔ p = zeroPat n := by
  unfold IsNiche nonZeroV
  rw [bne_eq_false_iff_eq, Fin.ext_iff]
  rfl

/-- If the payload's only niche is the zero pattern, it is the `NonZero` validity set. -/
theorem eq_nonZeroV_of_only_niche_zero (V : Validity n)
    (honly : ∀ p, IsNiche V p ↔ p = zeroPat n) : V = nonZeroV n := by
  funext p
  have h1 := honly p
  have h2 := isNiche_nonZeroV_iff p
  unfold IsNiche at h1 h2
  cases hv : V p <;> cases hw : nonZeroV n p <;> simp_all

/-- "The zero pattern is the only niche" implies "at most one niche". -/
theorem numInvalid_le_one_of_only_niche_zero (V : Validity n)
    (honly : ∀ p, IsNiche V p ↔ p = zeroPat n) : numInvalid V ≤ 1 := by
  rw [eq_nonZeroV_of_only_niche_zero V honly, numInvalid_nonZeroV]
  exact Nat.le_refl 1

/-! ## The first `k` niches -/

theorem nodup_getElem_inj {γ : Type} {l : List γ} (h : l.Nodup)
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (heq : l[i] = l[j]) : i = j := by
  induction l generalizing i j with
  | nil => cases hi
  | cons a t ih =>
    rw [List.nodup_cons] at h
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact absurd (heq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)) h.1
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact absurd (heq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)) h.1
      | succ j' =>
        simp only [List.getElem_cons_succ] at heq
        exact congrArg Nat.succ (ih h.2 _ _ heq)

/-- If `k ≤ numInvalid V`, the first `k` niches of `V` (`firstNiches V k`) are pairwise
distinct niches. Without `k ≤ numInvalid V` the default value repeats
(`nex_firstNiches`). -/
theorem firstNiches_injective_and_isNiche_of_le_numInvalid (V : Validity n) (k : Nat)
    (hk : k ≤ numInvalid V) :
    Function.Injective (firstNiches V k) ∧ ∀ i, IsNiche V (firstNiches V k i) := by
  have hnodup : (invalidPats V).Nodup := List.Pairwise.filter _ (List.nodup_finRange _)
  have hget : ∀ i : Fin k,
      firstNiches V k i = (invalidPats V)[i.val]'(Nat.lt_of_lt_of_le i.isLt hk) := by
    intro i
    simp only [firstNiches, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (Nat.lt_of_lt_of_le i.isLt hk), Option.getD_some]
    rfl
  refine ⟨?_, ?_⟩
  · intro i j hij
    rw [hget i, hget j] at hij
    exact Fin.ext (nodup_getElem_inj hnodup _ _ hij)
  · intro i
    rw [hget i]
    have hmem : (invalidPats V)[i.val]'(Nat.lt_of_lt_of_le i.isLt hk) ∈ invalidPats V :=
      List.getElem_mem _
    simp only [invalidPats, List.mem_filter, Bool.not_eq_true'] at hmem
    exact hmem.2

end Toy.WrapNiche.Imported
