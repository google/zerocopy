import Toy.WrapNiche.Results

/-!
# Corollaries (fully proved)

Consequences of the main results that the result cards cite by name: when the contiguous
capacity of a hull equals the niche count, how much room the rotated encoding needs, and the
capacity condition of the natural range for every position of the untagged variant.
-/

namespace Toy.WrapNiche

open Imported

/-- For an interval hull `H` of `V`, the number of values outside `H` equals the niche count of
`V` iff `V` is itself the member set of a wrapping interval (for the empty validity set both
sides are false). -/
theorem sub_size_eq_nichesCount_iff_isWrapIntervalSet_of_isHull {M : Nat} (V : Fin M → Bool)
    (H : WrapInterval M) (hH : IsHull V H) :
    M - H.size = nichesCount V ↔ IsWrapIntervalSet V := by
  have hbase := sub_size_le_nichesCount_and_eq_iff_of_covers V H hH.1
  refine ⟨fun heq => ⟨H, fun x => ⟨hbase.2.mp heq x, hH.1 x⟩⟩, fun ⟨I, hI⟩ => ?_⟩
  have hcovI : Covers I V := fun x hx => (hI x).mpr hx
  have hleHI : H.size ≤ I.size := hH.2 I hcovI
  have hniI : nichesCount V = M - I.size := by
    have : V = intervalV I := by
      funext x; unfold intervalV; cases hv : V x <;> simp [hI x, hv]
    rw [this, nichesCount_intervalV]
  have hIlt : I.size ≤ M := Nat.succ_le_of_lt (offset_lt I.s I.e)
  have hleVH := hbase.1
  omega

/-- For a payload with at least one valid value and an interval hull `H`: some start `ns` makes
the `k - 1` rotated tags all invalid iff `k - 1 ≤ M - H.size` (truncated subtraction `k - 1`; for
`k ≤ 1` both sides hold), whatever the position of the untagged variant. -/
theorem exists_rotTagsInvalid_iff_sub_one_le_sub_size_of_nonempty_of_isHull {M : Nat}
    (V : Fin M → Bool) (H : WrapInterval M) (hne : ∃ x, V x = true) (hH : IsHull V H)
    (k : Nat) :
    (∃ ns : Fin M, RotTagsInvalid V k ns) ↔ k - 1 ≤ M - H.size := by
  by_cases hk : 2 ≤ k
  · have h := exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull V H hne hH
      (k - 2)
    constructor
    · rintro ⟨ns, hns⟩
      have := h.mp ⟨ns, (rotTagsInvalid_iff_tagsDisjoint_sub_two V k ns hk).mp hns⟩
      omega
    · intro hle
      obtain ⟨ns, hns⟩ := h.mpr (by omega)
      exact ⟨ns, (rotTagsInvalid_iff_tagsDisjoint_sub_two V k ns hk).mpr hns⟩
  · obtain ⟨x, _⟩ := hne
    exact ⟨fun _ => by omega, fun _ => ⟨x, fun r hr => by omega⟩⟩

/-- For a payload with at least one valid value, an interval hull `H` and `k ≥ 2`: the natural
range fits (some start makes its `naturalSpan k u + 1` tags all invalid) iff `M - H.size` is at
least `k - 1` when `u = 0` or `u = k - 1`, and at least `k` otherwise (every capacity, not only
`M - H.size = k - 1`). -/
theorem exists_tagsDisjoint_naturalSpan_iff_of_nonempty_of_isHull {M : Nat} (V : Fin M → Bool)
    (H : WrapInterval M) (hne : ∃ x, V x = true) (hH : IsHull V H) (k u : Nat) (hk : 2 ≤ k) :
    (∃ ns : Fin M, TagsDisjoint V ns (naturalSpan k u)) ↔
      (if u = 0 ∨ u = k - 1 then k - 1 else k) ≤ M - H.size := by
  rw [exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull V H hne hH,
    naturalSpan_eq k u hk]
  split <;> omega

end Toy.WrapNiche
