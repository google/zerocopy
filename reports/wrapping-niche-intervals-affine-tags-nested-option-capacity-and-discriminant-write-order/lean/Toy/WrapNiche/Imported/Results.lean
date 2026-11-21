/-
Imported module (not a result of this package).

Copied from the published corpus package `enum-niche-layout-guarantees-and-validity-invariants`
(repository `google/zerocopy`, branch `reference`, published at commit
`00c8f874bf1e70c933b7a2ea2572a76c1baa7327`; Lean sources unchanged at the latest correction
commit `f9bee82a6d3f8bb6698b4c9e716138018db94d4d`), file
`reports/enum-niche-layout-guarantees-and-validity-invariants/lean/Toy/Niche/Results.lean`,
whose SHA-256 at both commits is
`1cc88a25e188cafaae35db8e9c8cf6c7399d5e6b4005d0465af9bf8032e182ab`.
The edits are: the namespace (`Toy.Niche` renamed to `Toy.WrapNiche.Imported`); the
selection of declarations (only the cited theorems and their prerequisites are kept); and
the upstream module docstring, which is replaced by this header. Declaration names,
statements and proofs of the kept declarations are otherwise verbatim.
-/

import Toy.WrapNiche.Imported.Counting

namespace Toy.WrapNiche.Imported

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

end Toy.WrapNiche.Imported
