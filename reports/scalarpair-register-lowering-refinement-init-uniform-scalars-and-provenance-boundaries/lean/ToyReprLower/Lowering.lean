import ToyReprLower.Lemmas

/-!
# Lowering to scalars: when `raise ∘ lower` refines the identity

Main results:
* `scalar_roundTrip_refines_iff`: the `Scalar` form of the characterization.
* `pair_roundTrip_refines_iff`: the `ScalarPair` form.
* `union_scalar_roundTrip_refines_iff_outsideExtentsUninit`: `union` scalars need only (a).
* `union_scalar_roundTrip_refines_of_covers_value`: a `union` scalar covering the value refines.
* `memory_roundTrip_refines`: coarsening to `memory` is always a refinement.

No result assumes that a scalar's extent lies inside the value: `seg` truncates at the end of the
value and `place` truncates at `n`, and the characterizations hold with these truncations.
-/

namespace Toy.ReprLower

/-- Per-scalar characterization, for a byte list `bs` no longer than the scalar: raising the
lowered value, cut to the length of `bs`, is at least as defined as `bs` iff the per-scalar forms
of conditions (b), (d) and (c) hold. -/
theorem bytesLe_take_raise_lower_scalar_iff (s : Scalar) (bs : List AByte) (h : bs.length ≤ s.size) :
    BytesLe bs ((raiseScalar s (lowerScalar s bs)).take bs.length) ↔
      (initUniformAt s bs && rangeInclAt s bs && provCoherentAt s bs) = true := by
  unfold BytesLe
  cases s with
  | union p =>
    simp [lowerScalar, raiseScalar, initUniformAt, rangeInclAt, provCoherentAt, bytesLeb_refl]
  | initialized p rng =>
    have hpoison : (raiseScalar (.initialized p rng) .poison).take bs.length =
        List.replicate bs.length .uninit := by
      simp [raiseScalar, List.take_replicate, Nat.min_eq_left h]
    simp only [lowerScalar, initUniformAt, rangeInclAt, provCoherentAt]
    cases hi : allInit bs <;> cases hr : rng (datas bs)
    · simp only [Bool.and_self, Bool.false_eq_true, ↓reduceIte, hpoison,
        bytesLeb_replicate_uninit, Bool.false_or, Bool.not_false, Bool.or_true, Bool.true_or,
        Bool.and_true]
      cases allUninit bs <;> simp
    · simp only [Bool.false_eq_true, ↓reduceIte, hpoison,
        bytesLeb_replicate_uninit, Bool.false_or, Bool.not_false, Bool.or_true, Bool.and_true]
      cases allUninit bs <;> simp
    · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, hpoison,
        bytesLeb_replicate_uninit, Bool.true_or, Bool.not_true, Bool.or_false, Bool.true_and]
      cases allUninit bs <;> simp
    · simp only [Bool.and_self, ↓reduceIte, Bool.true_or, Bool.not_true, Bool.or_false,
        Bool.or_true, Bool.true_and]
      cases p with
      | int w =>
        have hlen : ((datas bs).map AByte.bits).length = bs.length := by simp [datas]
        simp only [raiseScalar, coherentFor, List.take_of_length_le (Nat.le_of_eq hlen)]
        rw [bytesLeb_map_bits_datas hi]
        cases hu : allUninit bs
        · simp
        · simp [allUninit_any_isFrag hu]
      | ptr w =>
        simp only [coherentFor]
        rcases raiseScalar_ptrLower_cases (.initialized (.ptr w) rng) bs with
          ⟨h0, h1⟩ | ⟨q, hf, h0, h1⟩
        · have hlen : ((datas bs).map AByte.bits).length = bs.length := by simp [datas]
          rw [h1, List.take_of_length_le (Nat.le_of_eq hlen), bytesLeb_map_bits_datas hi, h0]
          cases hu : allUninit bs
          · simp
          · simp [allUninit_any_isFrag hu]
        · rw [h1, List.take_length, bytesLeb_refl, h0]
          simp

/-- Unfolding `BytesLe` against a placed byte list. -/
theorem bytesLe_place_iff (x : List AByte) (n : Nat) (cs : List (Nat × List AByte))
    (hx : x.length = n) :
    BytesLe x (place n cs) ↔ ∀ i, i < n → (x.getD i .uninit).leb (chunkAt cs i) = true := by
  unfold BytesLe
  rw [bytesLeb_iff_getD]
  simp only [length_place, hx, true_and]
  constructor
  · intro h i hi
    have := h i hi
    rwa [getD_place, ite_eq_left hi] at this
  · intro h i hi
    rw [getD_place, ite_eq_left hi]
    exact h i hi

/-- `BytesLe` of a segment against a prefix of a list, unfolded pointwise. -/
theorem bytesLe_seg_take_iff (x : List AByte) (o w : Nat) (c : List AByte)
    (hc : (seg x o w).length ≤ c.length) :
    BytesLe (seg x o w) (c.take (seg x o w).length) ↔
      ∀ k, k < (seg x o w).length → (x.getD (o + k) .uninit).leb (c.getD k .uninit) = true := by
  unfold BytesLe
  rw [bytesLeb_iff_getD]
  have htl : (c.take (seg x o w).length).length = (seg x o w).length := by
    simp [List.length_take, Nat.min_eq_left hc]
  simp only [htl, true_and]
  have hseg_le : (seg x o w).length ≤ w := by rw [length_seg]; omega
  constructor
  · intro h k hk
    have := h k hk
    rw [getD_seg, ite_eq_left (by omega)] at this
    simpa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk] using this
  · intro h k hk
    rw [getD_seg, ite_eq_left (by omega)]
    simpa [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk] using h k hk

/-- Per-value form of the `Scalar` characterization (no bound on the scalar's width). -/
theorem scalar_bytesLe_roundTrip_iff (n : Nat) (s : Scalar) (x : List AByte) (hx : x.length = n) :
    BytesLe x (raise n (.scalar s) (lower (.scalar s) x)) ↔
      (∀ i, i < n → (BRepr.scalar s).inExtent i = false → x.getD i .uninit = .uninit) ∧
      (initUniformAt s (seg x 0 s.size) && rangeInclAt s (seg x 0 s.size) &&
        provCoherentAt s (seg x 0 s.size)) = true := by
  have hsegl_eq : (seg x 0 s.size).length = min s.size n := by rw [length_seg, hx]; omega
  have hsegl_le : (seg x 0 s.size).length ≤ s.size := by omega
  have hr_ge := length_le_raiseScalar_lowerScalar s (seg x 0 s.size) hsegl_le
  have hr_le := length_raiseScalar_lowerScalar_le s (seg x 0 s.size) hsegl_le
  rw [← bytesLe_take_raise_lower_scalar_iff s _ hsegl_le, bytesLe_seg_take_iff x 0 s.size _ hr_ge]
  simp only [raise, lower]
  rw [bytesLe_place_iff x n _ hx]
  simp only [chunkAt_one, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero, BRepr.inExtent,
    decide_eq_false_iff_not, Nat.not_lt]
  constructor
  · intro h
    refine ⟨fun i hi hle => ?_, fun k hk => ?_⟩
    · have := h i hi
      rwa [ite_eq_right (by omega), AByte.leb_uninit_iff] at this
    · have := h k (by omega)
      rwa [ite_eq_left (by omega)] at this
  · rintro ⟨h1, h2⟩ i hi
    by_cases hk : i < s.size
    · rw [ite_eq_left (by omega)]
      exact h2 i (by omega)
    · rw [ite_eq_right (by omega), h1 i hi (by omega)]; rfl

/-- **Lowering to a single scalar refines iff (a), (b), (d) and (c) hold.**
Let `V` be a set of byte-level values, each of length exactly `n`, and let the representation be
one scalar `s` of any width. Then `raise ∘ lower` refines the identity on every value of `V`
(`RoundTripRefines`) iff (a) every byte below `n` outside the scalar's extent is `uninit` in
every value of `V`, (b) an `initialized` scalar's bytes are all initialized or all
uninitialized, (d) if they are initialized and non-empty, their data lies in its range, and
(c) unless they are all uninitialized, they are provenance coherent for its primitive. -/
theorem scalar_roundTrip_refines_iff (n : Nat) (s : Scalar) (V : List AByte → Prop)
    (hlen : ∀ x, V x → x.length = n) :
    RoundTripRefines n (.scalar s) V ↔
      OutsideExtentsUninit n (.scalar s) V ∧ InitUniform (.scalar s) V ∧
        RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V := by
  unfold RoundTripRefines OutsideExtentsUninit InitUniform RangeIncl ProvCoherent
  simp only [BRepr.comps, List.all_cons, List.all_nil, Bool.and_true]
  constructor
  · intro h
    have H : ∀ x, V x → (initUniformAt s (seg x 0 s.size) = true ∧
        rangeInclAt s (seg x 0 s.size) = true) ∧ provCoherentAt s (seg x 0 s.size) = true := by
      intro x hx
      have := ((scalar_bytesLe_roundTrip_iff n s x (hlen x hx)).1 (h x hx)).2
      simpa only [Bool.and_eq_true] using this
    exact ⟨fun x hx => ((scalar_bytesLe_roundTrip_iff n s x (hlen x hx)).1 (h x hx)).1,
      fun x hx => (H x hx).1.1, fun x hx => (H x hx).1.2, fun x hx => (H x hx).2⟩
  · rintro ⟨ha, hb, hd, hc⟩ x hx
    rw [scalar_bytesLe_roundTrip_iff n s x (hlen x hx)]
    refine ⟨ha x hx, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨⟨hb x hx, hd x hx⟩, hc x hx⟩

/-- The `→` direction of `scalar_roundTrip_refines_iff` needs no length hypothesis: a value whose
round trip refines it already has length `n`. -/
theorem scalar_conditions_of_roundTrip_refines (n : Nat) (s : Scalar) (V : List AByte → Prop)
    (h : RoundTripRefines n (.scalar s) V) :
    OutsideExtentsUninit n (.scalar s) V ∧ InitUniform (.scalar s) V ∧
      RangeIncl (.scalar s) V ∧ ProvCoherent (.scalar s) V := by
  have hlen : ∀ x, V x → x.length = n := by
    intro x hx
    have := ((bytesLeb_iff_getD _ _).1 (h x hx)).1
    simpa [raise, lower, length_place] using this
  exact (scalar_roundTrip_refines_iff n s V hlen).1 h

/-- Per-value form of the `ScalarPair` characterization (no bound on `b`'s extent). -/
theorem pair_bytesLe_roundTrip_iff (n : Nat) (a b : Scalar) (o : Nat) (x : List AByte)
    (hx : x.length = n) (hab : a.size ≤ o) :
    BytesLe x (raise n (.pair a b o) (lower (.pair a b o) x)) ↔
      (∀ i, i < n → (BRepr.pair a b o).inExtent i = false → x.getD i .uninit = .uninit) ∧
      (initUniformAt a (seg x 0 a.size) && rangeInclAt a (seg x 0 a.size) &&
        provCoherentAt a (seg x 0 a.size)) = true ∧
      (initUniformAt b (seg x o b.size) && rangeInclAt b (seg x o b.size) &&
        provCoherentAt b (seg x o b.size)) = true := by
  have hal_eq : (seg x 0 a.size).length = min a.size n := by rw [length_seg, hx]; omega
  have hbl_eq : (seg x o b.size).length = min b.size (n - o) := by rw [length_seg, hx]
  have hal_le : (seg x 0 a.size).length ≤ a.size := by omega
  have hbl_le : (seg x o b.size).length ≤ b.size := by omega
  have hra_ge := length_le_raiseScalar_lowerScalar a (seg x 0 a.size) hal_le
  have hra_le := length_raiseScalar_lowerScalar_le a (seg x 0 a.size) hal_le
  have hrb_ge := length_le_raiseScalar_lowerScalar b (seg x o b.size) hbl_le
  have hrb_le := length_raiseScalar_lowerScalar_le b (seg x o b.size) hbl_le
  rw [← bytesLe_take_raise_lower_scalar_iff a _ hal_le,
    ← bytesLe_take_raise_lower_scalar_iff b _ hbl_le,
    bytesLe_seg_take_iff x 0 a.size _ hra_ge,
    bytesLe_seg_take_iff x o b.size _ hrb_ge]
  simp only [raise, lower]
  rw [bytesLe_place_iff x n _ hx]
  simp only [chunkAt_two, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero,
    BRepr.inExtent, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Nat.not_lt, Nat.not_le]
  constructor
  · intro h
    refine ⟨fun i hi hle => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · have := h i hi
      rw [ite_eq_right (by omega), ite_eq_right (by omega), AByte.leb_uninit_iff] at this
      exact this
    · have := h k (by omega)
      rwa [ite_eq_left (by omega)] at this
    · have := h (o + k) (by omega)
      rwa [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left] at this
  · rintro ⟨h1, h2, h3⟩ i hi
    by_cases hk : i < a.size
    · rw [ite_eq_left (by omega)]
      exact h2 i (by omega)
    · rw [ite_eq_right (by omega)]
      by_cases hk2 : o ≤ i ∧ i < o + b.size
      · rw [ite_eq_left (by omega)]
        have := h3 (i - o) (by omega)
        rwa [Nat.add_sub_cancel' hk2.1] at this
      · rw [ite_eq_right (by omega), h1 i hi ⟨by omega, by omega⟩]; rfl

/-- **Lowering to a scalar pair refines iff (a), (b), (d) and (c) hold.**
Let the representation be a pair `a`, `b` with `a` at offset `0` and `b` at offset `bOff`, with
disjoint extents (`a.size ≤ bOff`), and let `V` be a set of byte-level values, each of length
exactly `n`. Then `raise ∘ lower` refines the identity on every value of `V` iff (a), (b), (d)
and (c) hold for both scalars. -/
theorem pair_roundTrip_refines_iff (n : Nat) (a b : Scalar) (bOff : Nat) (V : List AByte → Prop)
    (hlen : ∀ x, V x → x.length = n) (hab : a.size ≤ bOff) :
    RoundTripRefines n (.pair a b bOff) V ↔
      OutsideExtentsUninit n (.pair a b bOff) V ∧ InitUniform (.pair a b bOff) V ∧
        RangeIncl (.pair a b bOff) V ∧ ProvCoherent (.pair a b bOff) V := by
  unfold RoundTripRefines OutsideExtentsUninit InitUniform RangeIncl ProvCoherent
  simp only [BRepr.comps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  constructor
  · intro h
    have H : ∀ x, V x → ((initUniformAt a (seg x 0 a.size) = true ∧
        rangeInclAt a (seg x 0 a.size) = true) ∧ provCoherentAt a (seg x 0 a.size) = true) ∧
        ((initUniformAt b (seg x bOff b.size) = true ∧
        rangeInclAt b (seg x bOff b.size) = true) ∧ provCoherentAt b (seg x bOff b.size) = true) := by
      intro x hx
      have := ((pair_bytesLe_roundTrip_iff n a b bOff x (hlen x hx) hab).1 (h x hx)).2
      simpa only [Bool.and_eq_true] using this
    exact ⟨fun x hx => ((pair_bytesLe_roundTrip_iff n a b bOff x (hlen x hx) hab).1
      (h x hx)).1, fun x hx => ⟨(H x hx).1.1.1, (H x hx).2.1.1⟩,
      fun x hx => ⟨(H x hx).1.1.2, (H x hx).2.1.2⟩, fun x hx => ⟨(H x hx).1.2, (H x hx).2.2⟩⟩
  · rintro ⟨ha, hb, hd, hc⟩ x hx
    rw [pair_bytesLe_roundTrip_iff n a b bOff x (hlen x hx) hab]
    simp only [Bool.and_eq_true]
    exact ⟨ha x hx, ⟨⟨(hb x hx).1, (hd x hx).1⟩, (hc x hx).1⟩,
      ⟨⟨(hb x hx).2, (hd x hx).2⟩, (hc x hx).2⟩⟩

/-- The `←` direction of `pair_roundTrip_refines_iff` needs no disjointness: if every value of
`V` has length `n` and the four conditions hold, the round trip refines, even for overlapping
extents. -/
theorem pair_roundTrip_refines_of_conditions (n : Nat) (a b : Scalar) (bOff : Nat)
    (V : List AByte → Prop) (hlen : ∀ x, V x → x.length = n)
    (ha : OutsideExtentsUninit n (.pair a b bOff) V) (hb : InitUniform (.pair a b bOff) V)
    (hd : RangeIncl (.pair a b bOff) V) (hc : ProvCoherent (.pair a b bOff) V) :
    RoundTripRefines n (.pair a b bOff) V := by
  intro x hx
  have hxl : x.length = n := hlen x hx
  have hal_eq : (seg x 0 a.size).length = min a.size n := by rw [length_seg, hxl]; omega
  have hbl_eq : (seg x bOff b.size).length = min b.size (n - bOff) := by rw [length_seg, hxl]
  have hal_le : (seg x 0 a.size).length ≤ a.size := by omega
  have hbl_le : (seg x bOff b.size).length ≤ b.size := by omega
  have hra_ge := length_le_raiseScalar_lowerScalar a (seg x 0 a.size) hal_le
  have hra_le := length_raiseScalar_lowerScalar_le a (seg x 0 a.size) hal_le
  have hrb_ge := length_le_raiseScalar_lowerScalar b (seg x bOff b.size) hbl_le
  have hrb_le := length_raiseScalar_lowerScalar_le b (seg x bOff b.size) hbl_le
  have hba := hb x hx
  have hda := hd x hx
  have hca := hc x hx
  simp only [BRepr.comps, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hba hda hca
  have hA : ∀ k, k < (seg x 0 a.size).length →
      (x.getD (0 + k) .uninit).leb
        ((raiseScalar a (lowerScalar a (seg x 0 a.size))).getD k .uninit) = true :=
    (bytesLe_seg_take_iff x 0 a.size _ hra_ge).1
      ((bytesLe_take_raise_lower_scalar_iff a _ hal_le).2 (by simp [hba.1, hda.1, hca.1]))
  have hB : ∀ k, k < (seg x bOff b.size).length →
      (x.getD (bOff + k) .uninit).leb
        ((raiseScalar b (lowerScalar b (seg x bOff b.size))).getD k .uninit) = true :=
    (bytesLe_seg_take_iff x bOff b.size _ hrb_ge).1
      ((bytesLe_take_raise_lower_scalar_iff b _ hbl_le).2 (by simp [hba.2, hda.2, hca.2]))
  simp only [raise, lower]
  rw [bytesLe_place_iff x n _ hxl]
  intro i hi
  simp only [chunkAt_two, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
  by_cases h1 : i < (raiseScalar a (lowerScalar a (seg x 0 a.size))).length
  · rw [ite_eq_left h1]
    simpa using hA i (by omega)
  · rw [ite_eq_right h1]
    have hia : ¬ i < a.size := by omega
    by_cases h2 : bOff ≤ i ∧ i < bOff + (raiseScalar b (lowerScalar b (seg x bOff b.size))).length
    · rw [ite_eq_left h2]
      have := hB (i - bOff) (by omega)
      rwa [Nat.add_sub_cancel' h2.1] at this
    · rw [ite_eq_right h2]
      have h_out : (BRepr.pair a b bOff).inExtent i = false := by
        simp [BRepr.inExtent, hia]
        omega
      rw [ha x hx i hi h_out]; rfl

/-- The `→` direction of `pair_roundTrip_refines_iff` needs no length hypothesis. -/
theorem pair_conditions_of_roundTrip_refines (n : Nat) (a b : Scalar) (bOff : Nat)
    (V : List AByte → Prop) (hab : a.size ≤ bOff) (h : RoundTripRefines n (.pair a b bOff) V) :
    OutsideExtentsUninit n (.pair a b bOff) V ∧ InitUniform (.pair a b bOff) V ∧
      RangeIncl (.pair a b bOff) V ∧ ProvCoherent (.pair a b bOff) V := by
  have hlen : ∀ x, V x → x.length = n := by
    intro x hx
    have := ((bytesLeb_iff_getD _ _).1 (h x hx)).1
    simpa [raise, lower, length_place] using this
  exact (pair_roundTrip_refines_iff n a b bOff V hlen hab).1 h

/-- **`union` scalars need only condition (a).** For a single `union` scalar of any width and
any set `V` of byte-level values, each of length exactly `n` (partially initialized and
fragment-carrying values included), `raise ∘ lower` refines the identity on `V` iff every byte
below `n` outside the scalar's extent is `uninit` in every value of `V`. -/
theorem union_scalar_roundTrip_refines_iff_outsideExtentsUninit (n : Nat) (p : Prim)
    (V : List AByte → Prop) (hlen : ∀ x, V x → x.length = n) :
    RoundTripRefines n (.scalar (.union p)) V ↔ OutsideExtentsUninit n (.scalar (.union p)) V := by
  rw [scalar_roundTrip_refines_iff n (.union p) V hlen]
  simp [InitUniform, RangeIncl, ProvCoherent, BRepr.comps, initUniformAt, rangeInclAt,
    provCoherentAt]

/-- **A `union` scalar covering the whole value always refines.** For a `union` scalar of width
at least `n` and any set `V` of byte-level values, each of length exactly `n` (partially
initialized and fragment-carrying values included), `raise ∘ lower` refines the identity on
`V`. -/
theorem union_scalar_roundTrip_refines_of_covers_value (n : Nat) (p : Prim)
    (V : List AByte → Prop) (hlen : ∀ x, V x → x.length = n) (hcov : n ≤ p.size) :
    RoundTripRefines n (.scalar (.union p)) V := by
  rw [union_scalar_roundTrip_refines_iff_outsideExtentsUninit n p V hlen]
  intro x _ i hi hout
  have hlt : i < p.size := by omega
  simp [BRepr.inExtent, Scalar.size, Scalar.prim, hlt] at hout

/-- **Coarsening to `memory` is always a refinement**: for every size `n` and every set `V` of
byte-level values, `raise n memory ∘ lower memory` is the identity, so it refines the identity on
`V`. -/
theorem memory_roundTrip_refines (n : Nat) (V : List AByte → Prop) :
    RoundTripRefines n .memory V := by
  intro x _
  exact bytesLe_refl x

end Toy.ReprLower
