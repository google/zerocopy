/-!
# Formalization of `rustc` `TagEncoding::Niche` Wrapping Modular Tag Arithmetic,
# Niche Capacity Non-Monotonicity, and `StatementKind::SetDiscriminant` Semantics

Self-contained kernel-checked Lean 4 (`v4.34.1`) constructive mechanization
(elementary `Nat` proofs only; zero unproved obligations, zero classical axioms,
zero SMT/bitblasting/native reflection or non-terminating recursion).

Mirrors the exact algorithms in `rust-lang/rust`:
- `compiler/rustc_abi/src/wrapping_range.rs` (`WrappingRange::contains`, `is_full_for`)
- `compiler/rustc_abi/src/lib.rs` (`Niche::available`, `Niche::reserve`, `TagEncoding::Niche`)
- `compiler/rustc_abi/src/layout/enum_layout.rs` (`calculate_niche_filling_layout`)
- `compiler/rustc_const_eval/src/interpret/discriminant.rs`
  (`write_discriminant`, `read_discriminant`, `tag_for_variant`)
- `compiler/rustc_codegen_ssa/src/mir/place.rs` (`codegen_set_discr`, `codegen_tag_value`)
-/

namespace RustcNicheLayout

/-! ## Section 1: Bit-Width Modular Wrapping Arithmetic -/

/-- Modulus `2^w` for a `w`-bit unsigned scalar tag (`w = 8 * size.bytes()`). -/
def modulus (w : Nat) : Nat := 2 ^ w

theorem modulus_pos (w : Nat) : 0 < modulus w :=
  Nat.pow_pos (by decide : 0 < 2)

/-- Wrapping addition modulo `2^w`: `(a + b) mod 2^w`. -/
def wrapAdd (w a b : Nat) : Nat := (a + b) % modulus w

/-- Wrapping subtraction modulo `2^w`: `(a - b) mod 2^w` implemented totally on `Nat`. -/
def wrapSub (w a b : Nat) : Nat :=
  (a % modulus w + (modulus w - b % modulus w)) % modulus w

theorem wrapAdd_lt (w a b : Nat) : wrapAdd w a b < modulus w :=
  Nat.mod_lt _ (modulus_pos w)

theorem wrapSub_lt (w a b : Nat) : wrapSub w a b < modulus w :=
  Nat.mod_lt _ (modulus_pos w)

theorem wrapAdd_comm (w a b : Nat) : wrapAdd w a b = wrapAdd w b a := by
  unfold wrapAdd
  rw [Nat.add_comm]

private theorem add_mod_eq_sub_of_ge {m x : Nat} (hge : m ≤ x) (hlt : x < m + m) :
    x % m = x - m := by
  have hlt' : x - m < m := Nat.sub_lt_left_of_lt_add hge hlt
  calc
    x % m = ((x - m) + m) % m := by rw [Nat.sub_add_cancel hge]
    _ = (x - m) % m := Nat.add_mod_right (x - m) m
    _ = x - m := Nat.mod_eq_of_lt hlt'

private theorem sub_add_sub_cancel {a b c : Nat} (h1 : b ≤ a) (h2 : c ≤ b) :
    (a - b) + (b - c) = a - c := by
  have hle : c ≤ a := Nat.le_trans h2 h1
  apply Nat.add_right_cancel (m := c)
  rw [Nat.add_assoc, Nat.sub_add_cancel h2, Nat.sub_add_cancel h1, Nat.sub_add_cancel hle]

private theorem eval_wrapSub_ge {w a b : Nat} (ha : a < modulus w) (hb : b < modulus w)
    (hba : b ≤ a) : wrapSub w a b = a - b := by
  unfold wrapSub
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have hEq : a + (modulus w - b) = (a - b) + modulus w := by
    calc
      a + (modulus w - b) = (a - b + b) + (modulus w - b) := by rw [Nat.sub_add_cancel hba]
      _ = (a - b) + (b + (modulus w - b)) := Nat.add_assoc _ _ _
      _ = (a - b) + modulus w := by rw [Nat.add_sub_of_le (Nat.le_of_lt hb)]
  have hlt : a - b < modulus w := Nat.lt_of_le_of_lt (Nat.sub_le a b) ha
  rw [hEq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]

private theorem eval_wrapSub_lt {w a b : Nat} (ha : a < modulus w) (hb : b < modulus w)
    (hab : a < b) : wrapSub w a b = a + (modulus w - b) := by
  unfold wrapSub
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  have hsum : a + (modulus w - b) < modulus w := by
    have h1 : a + (modulus w - b) < b + (modulus w - b) := Nat.add_lt_add_right hab _
    rw [Nat.add_sub_of_le (Nat.le_of_lt hb)] at h1
    exact h1
  rw [Nat.mod_eq_of_lt hsum]

/-- Fundamental modular cancellation: `((s + x) mod 2^w - s) mod 2^w = x`
for all `x < 2^w` and `s < 2^w`. -/
theorem wrapSub_wrapAdd_cancel (w s x : Nat) (hs : s < modulus w) (hx : x < modulus w) :
    wrapSub w (wrapAdd w s x) s = x := by
  unfold wrapSub wrapAdd
  rw [Nat.mod_mod, Nat.mod_eq_of_lt hs]
  by_cases hlt : s + x < modulus w
  · rw [Nat.mod_eq_of_lt hlt]
    have hEq : s + x + (modulus w - s) = x + modulus w := by
      rw [Nat.add_comm s x, Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_lt hs)]
    rw [hEq, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
  · have hge : modulus w ≤ s + x := Nat.le_of_not_lt hlt
    have h2m : s + x < modulus w + modulus w := Nat.add_lt_add hs hx
    rw [add_mod_eq_sub_of_ge hge h2m]
    have hEq : (s + x - modulus w) + (modulus w - s) = x := by
      have h1 := sub_add_sub_cancel hge (Nat.le_of_lt hs)
      rw [h1, Nat.add_sub_cancel_left]
    rw [hEq, Nat.mod_eq_of_lt hx]

/-- Reverse modular cancellation: `(s + ((t - s) mod 2^w)) mod 2^w = t`
for all `t < 2^w` and `s < 2^w`. -/
theorem wrapAdd_wrapSub_cancel (w s t : Nat) (hs : s < modulus w) (ht : t < modulus w) :
    wrapAdd w s (wrapSub w t s) = t := by
  by_cases hle : s ≤ t
  · rw [eval_wrapSub_ge ht hs hle]
    unfold wrapAdd
    rw [Nat.add_sub_of_le hle, Nat.mod_eq_of_lt ht]
  · have hlt : t < s := Nat.lt_of_not_le hle
    rw [eval_wrapSub_lt ht hs hlt]
    unfold wrapAdd
    have hEq : s + (t + (modulus w - s)) = t + modulus w := by
      rw [Nat.add_left_comm, Nat.add_sub_of_le (Nat.le_of_lt hs)]
    rw [hEq, Nat.add_mod_right, Nat.mod_eq_of_lt ht]

/-- Modular subtraction shift: `wrapSub w t s = 0 ↔ t = s` for `t, s < 2^w`. -/
theorem wrapSub_eq_zero_iff (w t s : Nat) (ht : t < modulus w) (hs : s < modulus w) :
    wrapSub w t s = 0 ↔ t = s := by
  constructor
  · intro h0
    have h := wrapAdd_wrapSub_cancel w s t hs ht
    rw [h0] at h
    unfold wrapAdd at h
    rw [Nat.add_zero, Nat.mod_eq_of_lt hs] at h
    exact h.symm
  · intro heq
    subst heq
    have h := wrapSub_wrapAdd_cancel w t 0 ht (modulus_pos w)
    unfold wrapAdd at h
    rw [Nat.add_zero, Nat.mod_eq_of_lt ht] at h
    exact h

/-- Injectivity of `wrapAdd w s` on `[0, 2^w)`. -/
theorem wrapAdd_injective (w s x y : Nat) (hs : s < modulus w)
    (hx : x < modulus w) (hy : y < modulus w)
    (h : wrapAdd w s x = wrapAdd w s y) : x = y := by
  have h1 := congrArg (fun z => wrapSub w z s) h
  rw [wrapSub_wrapAdd_cancel w s x hs hx, wrapSub_wrapAdd_cancel w s y hs hy] at h1
  exact h1

/-- Modular associativity for `wrapAdd`: `wrapAdd w (wrapAdd w a b) c = wrapAdd w a (wrapAdd w b c)`. -/
theorem wrapAdd_assoc (w a b c : Nat) :
    wrapAdd w (wrapAdd w a b) c = wrapAdd w a (wrapAdd w b c) := by
  unfold wrapAdd
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

/-- Decomposition of `wrapSub` across an intermediate point along a modular arc:
if `x + y < 2^w`, then `wrapSub w (wrapAdd w s (x + y)) (wrapAdd w s x) = y`. -/
theorem wrapSub_arc (w s x y : Nat) (hxy : x + y < modulus w) :
    wrapSub w (wrapAdd w s (x + y)) (wrapAdd w s x) = y := by
  have hy : y < modulus w := Nat.lt_of_le_of_lt (Nat.le_add_left y x) hxy
  have h1 : wrapAdd w s (x + y) = wrapAdd w (wrapAdd w s x) y := by
    unfold wrapAdd
    rw [Nat.mod_add_mod, Nat.add_assoc]
  rw [h1]
  exact wrapSub_wrapAdd_cancel w (wrapAdd w s x) y (wrapAdd_lt w s x) hy

/-! ## Section 2: `WrappingRange w` (Mirroring `rustc_abi::WrappingRange`) -/

/-- Inclusive wrap-around scalar validity range on `[0, 2^w)`.
When `start ≤ end_`, represents `{ v | start ≤ v ≤ end_ }`.
When `start > end_`, represents `{ v | start ≤ v < 2^w } ∪ { v | 0 ≤ v ≤ end_ }`.
Mirrors `compiler/rustc_abi/src/wrapping_range.rs:19-63`. -/
structure WrappingRange (w : Nat) where
  start : Nat
  end_ : Nat
  deriving DecidableEq, Repr

namespace WrappingRange

/-- Both endpoints lie in `[0, 2^w)`. -/
abbrev inBounds (r : WrappingRange w) : Prop :=
  r.start < modulus w ∧ r.end_ < modulus w

/-- Exact mirror of `WrappingRange::contains` (`wrapping_range.rs:57-63`). -/
def contains (r : WrappingRange w) (v : Nat) : Bool :=
  if r.start ≤ r.end_ then
    decide (r.start ≤ v ∧ v ≤ r.end_)
  else
    decide (r.start ≤ v ∨ v ≤ r.end_)

/-- Exact mirror of `WrappingRange::is_full_for` (`wrapping_range.rs:112-116`). -/
def isFull (r : WrappingRange w) : Bool :=
  decide (r.start = (r.end_ + 1) % modulus w)

/-- Number of valid values in `r`: `((end_ - start) mod 2^w) + 1 ∈ [1, 2^w]`. -/
def validCount (r : WrappingRange w) : Nat :=
  wrapSub w r.end_ r.start + 1

/-- Exact mirror of `Niche::available` (`compiler/rustc_abi/src/lib.rs:2128-2137`):
count of invalid bit-patterns outside `r`, namely `wrapSub w r.start ((r.end_ + 1) mod 2^w)`. -/
def availableNiches (r : WrappingRange w) : Nat :=
  wrapSub w r.start (wrapAdd w r.end_ 1)

/-- Containment characterization via modular distance from `r.start`:
for an in-bounds `r` and `v < 2^w`, `r.contains v = true ↔ wrapSub w v r.start ≤ wrapSub w r.end_ r.start`. -/
theorem contains_iff_wrapSub_le {w : Nat} (r : WrappingRange w) (hr : r.inBounds)
    (v : Nat) (hv : v < modulus w) :
    r.contains v = true ↔ wrapSub w v r.start ≤ wrapSub w r.end_ r.start := by
  rcases hr with ⟨hs, he⟩
  unfold contains
  by_cases hse : r.start ≤ r.end_
  · simp only [hse, ↓reduceIte, decide_eq_true_eq]
    rw [eval_wrapSub_ge he hs hse]
    by_cases hvs : r.start ≤ v
    · rw [eval_wrapSub_ge hv hs hvs]
      constructor
      · rintro ⟨_, hve⟩
        exact Nat.sub_le_sub_right hve r.start
      · intro hsub
        refine ⟨hvs, ?_⟩
        have h1 := Nat.add_le_add_right hsub r.start
        rw [Nat.sub_add_cancel hvs, Nat.sub_add_cancel hse] at h1
        exact h1
    · have hlt_vs : v < r.start := Nat.lt_of_not_le hvs
      rw [eval_wrapSub_lt hv hs hlt_vs]
      constructor
      · intro h; exact False.elim (hvs h.1)
      · intro hle
        have hgt : r.end_ - r.start < v + (modulus w - r.start) := by
          have h1 : r.end_ - r.start < modulus w - r.start :=
            Nat.sub_lt_sub_right hse he
          exact Nat.lt_of_lt_of_le h1 (Nat.le_add_left _ v)
        exact False.elim (Nat.not_lt_of_ge hle hgt)
  · have hes : r.end_ < r.start := Nat.lt_of_not_le hse
    simp only [hse, ↓reduceIte, decide_eq_true_eq]
    rw [eval_wrapSub_lt he hs hes]
    by_cases hvs : r.start ≤ v
    · rw [eval_wrapSub_ge hv hs hvs]
      constructor
      · intro _
        have h1 : v - r.start ≤ modulus w - r.start := Nat.sub_le_sub_right (Nat.le_of_lt hv) _
        exact Nat.le_trans h1 (Nat.le_add_left _ r.end_)
      · intro _; exact Or.inl hvs
    · have hlt_vs : v < r.start := Nat.lt_of_not_le hvs
      rw [eval_wrapSub_lt hv hs hlt_vs]
      constructor
      · intro hor
        cases hor with
        | inl h => exact False.elim (hvs h)
        | inr hve => exact Nat.add_le_add_right hve (modulus w - r.start)
      · intro hle
        exact Or.inr (Nat.le_of_add_le_add_right hle)

/-- Conservation law: for every in-bounds `WrappingRange w`,
`r.validCount + r.availableNiches = 2^w`. -/
theorem validCount_add_availableNiches {w : Nat} (r : WrappingRange w) (hr : r.inBounds) :
    r.validCount + r.availableNiches = modulus w := by
  rcases hr with ⟨hs, he⟩
  unfold validCount availableNiches
  let d := wrapSub w r.end_ r.start
  change (d + 1) + wrapSub w r.start (wrapAdd w r.end_ 1) = modulus w
  have hd_lt : d < modulus w := wrapSub_lt w r.end_ r.start
  have h_end : wrapAdd w r.start d = r.end_ := wrapAdd_wrapSub_cancel w r.start r.end_ hs he
  have h_end1 : wrapAdd w r.end_ 1 = wrapAdd w r.start (d + 1) := by
    rw [← h_end]
    unfold wrapAdd
    rw [Nat.mod_add_mod, Nat.add_assoc]
  rw [h_end1]
  by_cases hfull : d + 1 = modulus w
  · have h_eq_start : wrapAdd w r.start (d + 1) = r.start := by
      unfold wrapAdd
      rw [hfull, Nat.add_mod_right, Nat.mod_eq_of_lt hs]
    rw [h_eq_start]
    have h0 : wrapSub w r.start r.start = 0 :=
      (wrapSub_eq_zero_iff w r.start r.start hs hs).mpr rfl
    rw [h0, Nat.add_zero, hfull]
  · have hd1_lt : d + 1 < modulus w :=
      Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hd_lt) hfull
    have hsub : wrapSub w r.start (wrapAdd w r.start (d + 1)) = modulus w - (d + 1) := by
      let t := wrapAdd w r.start (d + 1)
      change wrapSub w r.start t = modulus w - (d + 1)
      have ht_lt : t < modulus w := wrapAdd_lt w r.start (d + 1)
      have h_rem_lt : modulus w - (d + 1) < modulus w :=
        Nat.sub_lt (modulus_pos w) (Nat.succ_pos d)
      have h_sum : wrapAdd w t (modulus w - (d + 1)) = r.start := by
        change wrapAdd w (wrapAdd w r.start (d + 1)) (modulus w - (d + 1)) = r.start
        unfold wrapAdd
        rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_lt hd1_lt),
            Nat.add_mod_right, Nat.mod_eq_of_lt hs]
      rw [← h_sum]
      exact wrapSub_wrapAdd_cancel w t (modulus w - (d + 1)) ht_lt h_rem_lt
    rw [hsub, Nat.add_sub_of_le (Nat.le_of_lt hd1_lt)]

/-- Consequently, `availableNiches < 2^w` because every `WrappingRange` is non-empty (`validCount ≥ 1`). -/
theorem availableNiches_lt_modulus {w : Nat} (r : WrappingRange w) (hr : r.inBounds) :
    r.availableNiches < modulus w := by
  have hcons := validCount_add_availableNiches r hr
  have hv_pos : 0 < r.validCount := Nat.succ_pos _
  have hlt : r.availableNiches < r.validCount + r.availableNiches := by
    rw [Nat.add_comm]
    exact Nat.lt_add_of_pos_right hv_pos
  rw [hcons] at hlt
  exact hlt

/-- Extending `r` upward by `count` niches (`move_end` in `Niche::reserve`,
`compiler/rustc_abi/src/lib.rs:2169-2173`): returns `(nicheStart, extendedRange)` iff
`0 < count ∧ count ≤ r.availableNiches`. -/
def reserveFromEnd (r : WrappingRange w) (count : Nat) : Option (Nat × WrappingRange w) :=
  if 0 < count ∧ count ≤ r.availableNiches then
    let nStart := wrapAdd w r.end_ 1
    let newEnd := wrapAdd w r.end_ count
    some (nStart, { start := r.start, end_ := newEnd })
  else
    none

/-- Extending `r` downward by `count` niches (`move_start` in `Niche::reserve`,
`compiler/rustc_abi/src/lib.rs:2165-2168`): returns `(nicheStart, extendedRange)` iff
`0 < count ∧ count ≤ r.availableNiches`. -/
def reserveFromStart (r : WrappingRange w) (count : Nat) : Option (Nat × WrappingRange w) :=
  if 0 < count ∧ count ≤ r.availableNiches then
    let nStart := wrapSub w r.start count
    some (nStart, { start := nStart, end_ := r.end_ })
  else
    none

/-- Exact `move_end` geometric properties: reserved niche tags are strictly outside `r`,
inside the extended `tagRange`, and every element of `tagRange` is either in `r` or in
the reserved niche arc `[nStart, nStart + count) mod 2^w`. -/
theorem reserveFromEnd_spec {w : Nat} (r : WrappingRange w) (hr : r.inBounds)
    (count nStart : Nat) (tagRange : WrappingRange w)
    (hres : r.reserveFromEnd count = some (nStart, tagRange)) :
    0 < count ∧
    count ≤ r.availableNiches ∧
    nStart < modulus w ∧
    tagRange.inBounds ∧
    (∀ k, k < count →
      r.contains (wrapAdd w nStart k) = false ∧
      tagRange.contains (wrapAdd w nStart k) = true) ∧
    (∀ p, p < modulus w → r.contains p = true →
      tagRange.contains p = true ∧ count ≤ wrapSub w p nStart) ∧
    (∀ t, t < modulus w → tagRange.contains t = true →
      r.contains t = true ∨ wrapSub w t nStart < count) := by
  unfold reserveFromEnd at hres
  by_cases hcond : 0 < count ∧ count ≤ r.availableNiches
  · simp only [hcond] at hres
    injection hres with hpair
    injection hpair with hnStart htagR
    subst hnStart htagR
    rcases hr with ⟨hs, he⟩
    have hcons := validCount_add_availableNiches r ⟨hs, he⟩
    let d := wrapSub w r.end_ r.start
    have hvc : r.validCount = d + 1 := rfl
    have hdc_lt : d + count < modulus w := by
      have h1 : (d + 1) + count ≤ (d + 1) + r.availableNiches := Nat.add_le_add_left hcond.2 _
      rw [← hvc, hcons] at h1
      have h2 : d + count + 1 ≤ modulus w := by
        rw [Nat.add_right_comm]; exact h1
      exact Nat.lt_of_succ_le h2
    have h_end_eq : wrapAdd w r.start d = r.end_ := wrapAdd_wrapSub_cancel w r.start r.end_ hs he
    have h_nStart_eq : wrapAdd w r.end_ 1 = wrapAdd w r.start (d + 1) := by
      rw [← h_end_eq]; unfold wrapAdd; rw [Nat.mod_add_mod, Nat.add_assoc]
    have h_newEnd_eq : wrapAdd w r.end_ count = wrapAdd w r.start (d + count) := by
      rw [← h_end_eq]; unfold wrapAdd; rw [Nat.mod_add_mod, Nat.add_assoc]
    have h_newEnd_dist : wrapSub w (wrapAdd w r.end_ count) r.start = d + count := by
      rw [h_newEnd_eq]
      exact wrapSub_wrapAdd_cancel w r.start (d + count) hs hdc_lt
    have htag_inb : WrappingRange.inBounds (w := w) { start := r.start, end_ := wrapAdd w r.end_ count } :=
      ⟨hs, wrapAdd_lt w r.end_ count⟩
    refine ⟨hcond.1, hcond.2, wrapAdd_lt w r.end_ 1, htag_inb, ?_, ?_, ?_⟩
    · intro k hk
      have h_tag_eq : wrapAdd w (wrapAdd w r.end_ 1) k = wrapAdd w r.start (d + 1 + k) := by
        rw [h_nStart_eq]; unfold wrapAdd; rw [Nat.mod_add_mod, Nat.add_assoc]
      have hdk_le : d + 1 + k ≤ d + count := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
        exact Nat.add_le_add_left (Nat.succ_le_of_lt hk) d
      have hdk_lt : d + 1 + k < modulus w := Nat.lt_of_le_of_lt hdk_le hdc_lt
      have hdist : wrapSub w (wrapAdd w (wrapAdd w r.end_ 1) k) r.start = d + 1 + k := by
        rw [h_tag_eq]
        exact wrapSub_wrapAdd_cancel w r.start (d + 1 + k) hs hdk_lt
      constructor
      · cases hcont : r.contains (wrapAdd w (wrapAdd w r.end_ 1) k) with
        | false => rfl
        | true =>
          have hle := (contains_iff_wrapSub_le r ⟨hs, he⟩ _ (wrapAdd_lt _ _ _)).mp hcont
          change wrapSub w (wrapAdd w (wrapAdd w r.end_ 1) k) r.start ≤ d at hle
          rw [hdist] at hle
          have hgt : d < d + 1 + k := Nat.lt_of_lt_of_le (Nat.lt_succ_self d) (Nat.le_add_right _ k)
          exact False.elim (Nat.not_lt_of_ge hle hgt)
      · rw [contains_iff_wrapSub_le _ htag_inb _ (wrapAdd_lt _ _ _)]
        dsimp only
        rw [hdist, h_newEnd_dist]
        exact hdk_le
    · intro p hp hcont
      have hle_d : wrapSub w p r.start ≤ d :=
        (contains_iff_wrapSub_le r ⟨hs, he⟩ p hp).mp hcont
      constructor
      · rw [contains_iff_wrapSub_le _ htag_inb p hp]
        dsimp only
        rw [h_newEnd_dist]
        exact Nat.le_trans hle_d (Nat.le_add_right d count)
      · by_cases hlt_c : wrapSub w p (wrapAdd w r.end_ 1) < count
        · let k := wrapSub w p (wrapAdd w r.end_ 1)
          have hk_lt : k < count := hlt_c
          have hp_eq : wrapAdd w (wrapAdd w r.end_ 1) k = p :=
            wrapAdd_wrapSub_cancel w (wrapAdd w r.end_ 1) p (wrapAdd_lt w r.end_ 1) hp
          have h_tag_eq : wrapAdd w (wrapAdd w r.end_ 1) k = wrapAdd w r.start (d + 1 + k) := by
            rw [h_nStart_eq]; unfold wrapAdd; rw [Nat.mod_add_mod, Nat.add_assoc]
          have hdk_le : d + 1 + k ≤ d + count := by
            rw [Nat.add_assoc, Nat.add_comm 1 k]
            exact Nat.add_le_add_left (Nat.succ_le_of_lt hk_lt) d
          have hdk_lt : d + 1 + k < modulus w := Nat.lt_of_le_of_lt hdk_le hdc_lt
          have hdist : wrapSub w p r.start = d + 1 + k := by
            rw [← hp_eq, h_tag_eq]
            exact wrapSub_wrapAdd_cancel w r.start (d + 1 + k) hs hdk_lt
          rw [hdist] at hle_d
          have hgt : d < d + 1 + k := Nat.lt_of_lt_of_le (Nat.lt_succ_self d) (Nat.le_add_right _ k)
          exact False.elim (Nat.not_lt_of_ge hle_d hgt)
        · exact Nat.le_of_not_lt hlt_c
    · intro t ht hcont_tag
      have hle_dc : wrapSub w t r.start ≤ d + count := by
        have h := (contains_iff_wrapSub_le _ htag_inb t ht).mp hcont_tag
        dsimp only at h
        rw [h_newEnd_dist] at h
        exact h
      by_cases hle_d : wrapSub w t r.start ≤ d
      · exact Or.inl ((contains_iff_wrapSub_le r ⟨hs, he⟩ t ht).mpr hle_d)
      · right
        have hgt_d : d + 1 ≤ wrapSub w t r.start := Nat.succ_le_of_lt (Nat.lt_of_not_le hle_d)
        let m := wrapSub w t r.start
        have hm_lt : m < modulus w := wrapSub_lt w t r.start
        have hm_ge : d + 1 ≤ m := hgt_d
        have hm_le : m ≤ d + count := hle_dc
        have hk_lt : m - (d + 1) < count := by
          have h1 : (m - (d + 1)) + (d + 1) = m := Nat.sub_add_cancel hm_ge
          have h2 : (m - (d + 1)) + (d + 1) < count + (d + 1) := by
            rw [h1]
            have h3 : d + count < count + (d + 1) := by
              rw [Nat.add_comm count (d + 1), Nat.add_right_comm]
              exact Nat.lt_succ_self (d + count)
            exact Nat.lt_of_le_of_lt hm_le h3
          exact Nat.lt_of_add_lt_add_right h2
        have ht_eq : t = wrapAdd w r.start ((d + 1) + (m - (d + 1))) := by
          rw [Nat.add_comm (d + 1), Nat.sub_add_cancel hm_ge]
          exact (wrapAdd_wrapSub_cancel w r.start t hs ht).symm
        have hsum_lt : (d + 1) + (m - (d + 1)) < modulus w := by
          rw [Nat.add_comm (d + 1), Nat.sub_add_cancel hm_ge]
          exact hm_lt
        have hrel : wrapSub w t (wrapAdd w r.end_ 1) = m - (d + 1) := by
          rw [ht_eq, h_nStart_eq]
          exact wrapSub_arc w r.start (d + 1) (m - (d + 1)) hsum_lt
        rw [hrel]
        exact hk_lt
  · simp only [hcond, ↓reduceIte] at hres
    cases hres

/-- Exact `move_start` geometric properties (mirroring `Niche::reserve`'s `move_start`
closure, `compiler/rustc_abi/src/lib.rs:2165-2168`). -/
theorem reserveFromStart_spec {w : Nat} (r : WrappingRange w) (hr : r.inBounds)
    (count nStart : Nat) (tagRange : WrappingRange w)
    (hres : r.reserveFromStart count = some (nStart, tagRange)) :
    0 < count ∧
    count ≤ r.availableNiches ∧
    nStart < modulus w ∧
    tagRange.inBounds ∧
    (∀ k, k < count →
      r.contains (wrapAdd w nStart k) = false ∧
      tagRange.contains (wrapAdd w nStart k) = true) ∧
    (∀ p, p < modulus w → r.contains p = true →
      tagRange.contains p = true ∧ count ≤ wrapSub w p nStart) ∧
    (∀ t, t < modulus w → tagRange.contains t = true →
      r.contains t = true ∨ wrapSub w t nStart < count) := by
  unfold reserveFromStart at hres
  by_cases hcond : 0 < count ∧ count ≤ r.availableNiches
  · simp only [hcond] at hres
    injection hres with hpair
    injection hpair with hnStart htagR
    subst hnStart htagR
    rcases hr with ⟨hs, he⟩
    have hcons := validCount_add_availableNiches r ⟨hs, he⟩
    let d := wrapSub w r.end_ r.start
    have hvc : r.validCount = d + 1 := rfl
    have hc_lt : count < modulus w :=
      Nat.lt_of_le_of_lt hcond.2 (availableNiches_lt_modulus r ⟨hs, he⟩)
    have hdc_lt : count + d < modulus w := by
      have h1 : (d + 1) + count ≤ (d + 1) + r.availableNiches := Nat.add_le_add_left hcond.2 _
      rw [← hvc, hcons] at h1
      have h2 : count + d + 1 ≤ modulus w := by
        rw [Nat.add_comm count d, Nat.add_right_comm]; exact h1
      exact Nat.lt_of_succ_le h2
    let ns := wrapSub w r.start count
    have hns_lt : ns < modulus w := wrapSub_lt w r.start count
    have h_start_eq : wrapAdd w ns count = r.start := by
      change wrapAdd w (wrapSub w r.start count) count = r.start
      rw [wrapAdd_comm]
      exact wrapAdd_wrapSub_cancel w count r.start hc_lt hs
    have h_end_eq : wrapAdd w ns (count + d) = r.end_ := by
      have h1 : wrapAdd w ns (count + d) = wrapAdd w (wrapAdd w ns count) d := by
        unfold wrapAdd; rw [Nat.mod_add_mod, Nat.add_assoc]
      rw [h1, h_start_eq]
      exact wrapAdd_wrapSub_cancel w r.start r.end_ hs he
    have h_end_dist : wrapSub w r.end_ ns = count + d := by
      rw [← h_end_eq]
      exact wrapSub_wrapAdd_cancel w ns (count + d) hns_lt hdc_lt
    have htag_inb : WrappingRange.inBounds (w := w) { start := ns, end_ := r.end_ } :=
      ⟨hns_lt, he⟩
    refine ⟨hcond.1, hcond.2, hns_lt, htag_inb, ?_, ?_, ?_⟩
    · intro k hk
      have hk_lt : k < modulus w := Nat.lt_trans hk hc_lt
      have hdist_ns : wrapSub w (wrapAdd w ns k) ns = k :=
        wrapSub_wrapAdd_cancel w ns k hns_lt hk_lt
      constructor
      · cases hcont : r.contains (wrapAdd w ns k) with
        | false => rfl
        | true =>
          have hle_d := (contains_iff_wrapSub_le r ⟨hs, he⟩ _ (wrapAdd_lt _ _ _)).mp hcont
          let q := wrapSub w (wrapAdd w ns k) r.start
          have hq_le : q ≤ d := hle_d
          have h_cq_lt : count + q < modulus w := Nat.lt_of_le_of_lt (Nat.add_le_add_left hq_le count) hdc_lt
          have h_eq : wrapAdd w ns (count + q) = wrapAdd w ns k := by
            have h1 : wrapAdd w ns (count + q) = wrapAdd w (wrapAdd w ns count) q := by
              unfold wrapAdd; rw [Nat.mod_add_mod, Nat.add_assoc]
            rw [h1, h_start_eq]
            exact wrapAdd_wrapSub_cancel w r.start (wrapAdd w ns k) hs (wrapAdd_lt _ _ _)
          have h_inj := wrapAdd_injective w ns (count + q) k hns_lt h_cq_lt hk_lt h_eq
          have hge : count ≤ k := by rw [← h_inj]; exact Nat.le_add_right count q
          exact False.elim (Nat.not_lt_of_ge hge hk)
      · rw [contains_iff_wrapSub_le _ htag_inb _ (wrapAdd_lt _ _ _)]
        dsimp only
        change wrapSub w (wrapAdd w ns k) ns ≤ wrapSub w r.end_ ns
        rw [hdist_ns, h_end_dist]
        exact Nat.le_trans (Nat.le_of_lt hk) (Nat.le_add_right count d)
    · intro p hp hcont
      have hle_d : wrapSub w p r.start ≤ d :=
        (contains_iff_wrapSub_le r ⟨hs, he⟩ p hp).mp hcont
      let q := wrapSub w p r.start
      have h_cq_lt : count + q < modulus w :=
        Nat.lt_of_le_of_lt (Nat.add_le_add_left hle_d count) hdc_lt
      have hp_eq : wrapAdd w ns (count + q) = p := by
        have h1 : wrapAdd w ns (count + q) = wrapAdd w (wrapAdd w ns count) q := by
          unfold wrapAdd; rw [Nat.mod_add_mod, Nat.add_assoc]
        rw [h1, h_start_eq]
        exact wrapAdd_wrapSub_cancel w r.start p hs hp
      have hdist_ns : wrapSub w p ns = count + q := by
        rw [← hp_eq]
        exact wrapSub_wrapAdd_cancel w ns (count + q) hns_lt h_cq_lt
      constructor
      · rw [contains_iff_wrapSub_le _ htag_inb p hp]
        dsimp only
        change wrapSub w p ns ≤ wrapSub w r.end_ ns
        rw [hdist_ns, h_end_dist]
        exact Nat.add_le_add_left hle_d count
      · change count ≤ wrapSub w p ns
        rw [hdist_ns]
        exact Nat.le_add_right count q
    · intro t ht hcont_tag
      have hle_cd : wrapSub w t ns ≤ count + d := by
        have h := (contains_iff_wrapSub_le _ htag_inb t ht).mp hcont_tag
        dsimp only at h
        change wrapSub w t ns ≤ wrapSub w r.end_ ns at h
        rw [h_end_dist] at h
        exact h
      by_cases hlt_c : wrapSub w t ns < count
      · exact Or.inr hlt_c
      · left
        have hge_c : count ≤ wrapSub w t ns := Nat.le_of_not_lt hlt_c
        let m := wrapSub w t ns
        have hm_lt : m < modulus w := wrapSub_lt w t ns
        have hm_ge : count ≤ m := hge_c
        have hm_le : m ≤ count + d := hle_cd
        have ht_eq : t = wrapAdd w ns (count + (m - count)) := by
          rw [Nat.add_comm count, Nat.sub_add_cancel hm_ge]
          exact (wrapAdd_wrapSub_cancel w ns t hns_lt ht).symm
        have hsum_lt : count + (m - count) < modulus w := by
          rw [Nat.add_comm count, Nat.sub_add_cancel hm_ge]
          exact hm_lt
        have hdist_s : wrapSub w t r.start = m - count := by
          rw [ht_eq, ← h_start_eq]
          exact wrapSub_arc w ns count (m - count) hsum_lt
        rw [contains_iff_wrapSub_le r ⟨hs, he⟩ t ht, hdist_s]
        have h1 : (m - count) + count ≤ d + count := by
          rw [Nat.sub_add_cancel hm_ge, Nat.add_comm d count]
          exact hm_le
        exact Nat.le_of_add_le_add_right h1
  · simp only [hcond, ↓reduceIte] at hres
    cases hres

end WrappingRange

/-! ## Section 3: `NicheLayout w`, Tag Encoding/Decoding, and `SetDiscriminant` Semantics -/

/-- Exact structural model of `rustc_abi::TagEncoding::Niche` at scalar bit width `w`.
Mirrors `TagEncoding::Niche { untagged_variant, niche_variants, niche_start }` paired
with the payload scalar's `validPayloadRange` and outer enum tag's `tagValidRange`. -/
structure NicheLayout (w : Nat) where
  numVariants : Nat
  validPayloadRange : WrappingRange w
  untaggedVariant : Nat
  nicheVariantsStart : Nat
  nicheVariantsEnd : Nat
  nicheStart : Nat
  tagValidRange : WrappingRange w
  deriving DecidableEq, Repr

namespace NicheLayout

/-- Contiguous span `count = (niche_variants.last - niche_variants.start) + 1`
(`compiler/rustc_abi/src/layout/enum_layout.rs:611`). -/
def nicheSpan (L : NicheLayout w) : Nat :=
  L.nicheVariantsEnd - L.nicheVariantsStart + 1

/-- Maximum relative variant offset `relative_max = niche_variants.last - niche_variants.start`
(`compiler/rustc_codegen_ssa/src/mir/operand.rs:556`). -/
def nicheMaxRel (L : NicheLayout w) : Nat :=
  L.nicheVariantsEnd - L.nicheVariantsStart

/-- Predicate identifying inhabited non-untagged variants encoded via explicit niche tags. -/
def isNichedVariant (L : NicheLayout w) (v : Nat) : Prop :=
  L.nicheVariantsStart ≤ v ∧ v ≤ L.nicheVariantsEnd ∧ v ≠ L.untaggedVariant

/-- Well-formedness invariant guaranteed by `calculate_niche_filling_layout` +
`Niche::reserve` + `layout_sanity_check`. -/
structure WellFormed (L : NicheLayout w) : Prop where
  payloadInBounds : L.validPayloadRange.inBounds
  tagInBounds : L.tagValidRange.inBounds
  nicheStartLt : L.nicheStart < modulus w
  untaggedLt : L.untaggedVariant < L.numVariants
  nicheRangeValid : L.nicheVariantsStart ≤ L.nicheVariantsEnd ∧ L.nicheVariantsEnd < L.numVariants
  capacityOk : L.nicheSpan ≤ L.validPayloadRange.availableNiches
  nicheArcOutsidePayload :
    ∀ k, k < L.nicheSpan →
      L.validPayloadRange.contains (wrapAdd w L.nicheStart k) = false ∧
      L.tagValidRange.contains (wrapAdd w L.nicheStart k) = true
  payloadInsideTagAndOutsideArc :
    ∀ p, p < modulus w → L.validPayloadRange.contains p = true →
      L.tagValidRange.contains p = true ∧ L.nicheSpan ≤ wrapSub w p L.nicheStart
  tagCoveredByPayloadOrArc :
    ∀ t, t < modulus w → L.tagValidRange.contains t = true →
      L.validPayloadRange.contains t = true ∨ wrapSub w t L.nicheStart < L.nicheSpan

/-- Constructive builder from `reserveFromEnd`: automatically proves `WellFormed`. -/
def mkFromReserveEnd (numVariants untagged vStart vEnd : Nat)
    (payloadRange : WrappingRange w) (hpr : payloadRange.inBounds)
    (huntagged : untagged < numVariants)
    (hrange : vStart ≤ vEnd ∧ vEnd < numVariants)
    (nStart : Nat) (tagRange : WrappingRange w)
    (hres : payloadRange.reserveFromEnd (vEnd - vStart + 1) = some (nStart, tagRange)) :
    { L : NicheLayout w // L.WellFormed } :=
  let L : NicheLayout w := {
    numVariants := numVariants
    validPayloadRange := payloadRange
    untaggedVariant := untagged
    nicheVariantsStart := vStart
    nicheVariantsEnd := vEnd
    nicheStart := nStart
    tagValidRange := tagRange
  }
  ⟨L, by
    have hspec := WrappingRange.reserveFromEnd_spec payloadRange hpr (vEnd - vStart + 1) nStart tagRange hres
    rcases hspec with ⟨_, hcap, hns, htinb, harc, hpay, hcov⟩
    exact {
      payloadInBounds := hpr
      tagInBounds := htinb
      nicheStartLt := hns
      untaggedLt := huntagged
      nicheRangeValid := hrange
      capacityOk := hcap
      nicheArcOutsidePayload := harc
      payloadInsideTagAndOutsideArc := hpay
      tagCoveredByPayloadOrArc := hcov
    }⟩

/-- Constructive builder from `reserveFromStart`: automatically proves `WellFormed`. -/
def mkFromReserveStart (numVariants untagged vStart vEnd : Nat)
    (payloadRange : WrappingRange w) (hpr : payloadRange.inBounds)
    (huntagged : untagged < numVariants)
    (hrange : vStart ≤ vEnd ∧ vEnd < numVariants)
    (nStart : Nat) (tagRange : WrappingRange w)
    (hres : payloadRange.reserveFromStart (vEnd - vStart + 1) = some (nStart, tagRange)) :
    { L : NicheLayout w // L.WellFormed } :=
  let L : NicheLayout w := {
    numVariants := numVariants
    validPayloadRange := payloadRange
    untaggedVariant := untagged
    nicheVariantsStart := vStart
    nicheVariantsEnd := vEnd
    nicheStart := nStart
    tagValidRange := tagRange
  }
  ⟨L, by
    have hspec := WrappingRange.reserveFromStart_spec payloadRange hpr (vEnd - vStart + 1) nStart tagRange hres
    rcases hspec with ⟨_, hcap, hns, htinb, harc, hpay, hcov⟩
    exact {
      payloadInBounds := hpr
      tagInBounds := htinb
      nicheStartLt := hns
      untaggedLt := huntagged
      nicheRangeValid := hrange
      capacityOk := hcap
      nicheArcOutsidePayload := harc
      payloadInsideTagAndOutsideArc := hpay
      tagCoveredByPayloadOrArc := hcov
    }⟩

theorem nicheSpan_lt_modulus {w : Nat} (L : NicheLayout w) (hwf : L.WellFormed) :
    L.nicheSpan < modulus w :=
  Nat.lt_of_le_of_lt hwf.capacityOk
    (WrappingRange.availableNiches_lt_modulus L.validPayloadRange hwf.payloadInBounds)

/-- Exact mirror of `tag_for_variant` (`discriminant.rs:291-325`) and `codegen_tag_value`
(`place.rs:508-536`): returns `none` for `untaggedVariant` (or out-of-range variant) and
`some ((v - nicheVariantsStart + nicheStart) mod 2^w)` for niched variants. -/
def encodeVariantTag (L : NicheLayout w) (v : Nat) : Option Nat :=
  if v = L.untaggedVariant then
    none
  else if L.nicheVariantsStart ≤ v ∧ v ≤ L.nicheVariantsEnd then
    some (wrapAdd w L.nicheStart (v - L.nicheVariantsStart))
  else
    none

/-- Result of `read_discriminant` on a `TagEncoding::Niche` tag byte/word. -/
inductive DecodeResult where
  | ok (variant : Nat)
  | ubInvalidTag (tag : Nat)
  deriving DecidableEq, Repr

/-- Exact mirror of `read_discriminant` (`compiler/rustc_const_eval/src/interpret/discriminant.rs:163-203`):
1. Compute `rel = (tag - nicheStart) mod 2^w`.
2. If `rel ≤ nicheVariantsEnd - nicheVariantsStart`:
   - `v = nicheVariantsStart + rel`;
   - If `v == untaggedVariant`, throw `InvalidTag` (`discriminant.rs:188-193`);
   - Verify `tagValidRange.contains tag`, else `InvalidTag`;
   - Return `.ok v`.
3. Else:
   - Verify `tagValidRange.contains tag` (`discriminant.rs:198-200`), else `InvalidTag`;
   - Return `.ok untaggedVariant`. -/
def decodeNicheTag (L : NicheLayout w) (tag : Nat) : DecodeResult :=
  let rel := wrapSub w tag L.nicheStart
  if rel ≤ L.nicheMaxRel then
    let v := L.nicheVariantsStart + rel
    if v = L.untaggedVariant then
      .ubInvalidTag tag
    else if L.tagValidRange.contains tag then
      .ok v
    else
      .ubInvalidTag tag
  else
    if L.tagValidRange.contains tag then
      .ok L.untaggedVariant
    else
      .ubInvalidTag tag

/-- State of the tag scalar storage slot in memory. -/
inductive TagSlot where
  | uninit
  | init (bits : Nat)
  deriving DecidableEq, Repr

/-- Failure modes of `write_discriminant` (`discriminant.rs:20-46`). -/
inductive SetDiscrError where
  | invalidVariant
  | ubUninitRead
  | ubInvalidTag (tag : Nat)
  | ubInvalidNichedEnumVariantWritten (expected actual : Nat)
  deriving DecidableEq, Repr

/-- Outcome of operational `StatementKind::SetDiscriminant` evaluation. -/
inductive SetDiscrResult where
  | ok (nextSlot : TagSlot)
  | err (e : SetDiscrError)
  deriving DecidableEq, Repr

/-- Exact operational model of `InterpCx::write_discriminant` (`discriminant.rs:20-46`)
for `TagEncoding::Niche`:
- For `untaggedVariant`: performs the validation read (`read_discriminant`); faults
  `ubUninitRead` if the slot is uninitialized, `ubInvalidTag` if the bits are an invalid tag,
  or `ubInvalidNichedEnumVariantWritten` if `actual ≠ untaggedVariant`!
- For a niched variant: directly writes `encodeVariantTag L v` without reading prior memory. -/
def evalSetDiscriminant (L : NicheLayout w) (v : Nat) (slot : TagSlot) : SetDiscrResult :=
  if v = L.untaggedVariant then
    match slot with
    | .uninit => .err .ubUninitRead
    | .init bits =>
      match L.decodeNicheTag bits with
      | .ubInvalidTag t => .err (.ubInvalidTag t)
      | .ok actual =>
        if actual = v then
          .ok (.init bits)
        else
          .err (.ubInvalidNichedEnumVariantWritten v actual)
  else
    match L.encodeVariantTag v with
    | some tag => .ok (.init tag)
    | none => .err .invalidVariant

/-- Exact codegen model of `PlaceRef::codegen_set_discr` (`place.rs:262-279`):
for `untaggedVariant`, emits ZERO instructions (leaves `slot` untouched with no validation read);
for a niched variant, stores `encodeVariantTag L v`. -/
def evalCodegenSetDiscr (L : NicheLayout w) (v : Nat) (slot : TagSlot) : TagSlot :=
  match L.encodeVariantTag v with
  | some tag => .init tag
  | none => slot

/-! ## Section 4: Theorem 1 — Bijective Encode/Decode Round-Trip Over Wrapping Ranges -/

/-- Forward round-trip for niched variants: encoding a niched variant `v` yields a tag `t < 2^w`
that `decodeNicheTag` decodes back to `.ok v`. -/
theorem encode_decode_niched_roundtrip {w : Nat} (L : NicheLayout w) (hwf : L.WellFormed)
    (v : Nat) (hv : L.isNichedVariant v) :
    ∃ tag, tag < modulus w ∧ L.encodeVariantTag v = some tag ∧ L.decodeNicheTag tag = .ok v := by
  rcases hv with ⟨hge, hle, hne⟩
  let k := v - L.nicheVariantsStart
  have hk_le_max : k ≤ L.nicheMaxRel := Nat.sub_le_sub_right hle L.nicheVariantsStart
  have hk_lt_span : k < L.nicheSpan := Nat.lt_succ_of_le hk_le_max
  have hk_lt_mod : k < modulus w := Nat.lt_trans hk_lt_span (nicheSpan_lt_modulus L hwf)
  let tag := wrapAdd w L.nicheStart k
  refine ⟨tag, wrapAdd_lt w L.nicheStart k, ?_, ?_⟩
  · unfold encodeVariantTag
    simp only [hne, hge, hle, and_self, ↓reduceIte]
    rfl
  · unfold decodeNicheTag
    dsimp only
    have hrel : wrapSub w tag L.nicheStart = k :=
      wrapSub_wrapAdd_cancel w L.nicheStart k hwf.nicheStartLt hk_lt_mod
    have hadd : L.nicheVariantsStart + k = v := by
      change L.nicheVariantsStart + (v - L.nicheVariantsStart) = v
      rw [Nat.add_comm, Nat.sub_add_cancel hge]
    have htag_valid : L.tagValidRange.contains tag = true :=
      (hwf.nicheArcOutsidePayload k hk_lt_span).2
    simp only [hrel, hk_le_max, hadd, hne, htag_valid, ↓reduceIte]

/-- Forward round-trip for the untagged variant: every valid payload bit-pattern `p < 2^w`
with `validPayloadRange.contains p = true` decodes to `.ok L.untaggedVariant`. -/
theorem decode_untagged_payload_roundtrip {w : Nat} (L : NicheLayout w) (hwf : L.WellFormed)
    (p : Nat) (hp : p < modulus w) (hvalid : L.validPayloadRange.contains p = true) :
    L.decodeNicheTag p = .ok L.untaggedVariant := by
  have ⟨htag_valid, hge_span⟩ := hwf.payloadInsideTagAndOutsideArc p hp hvalid
  have hnot_le : ¬ (wrapSub w p L.nicheStart ≤ L.nicheMaxRel) := by
    intro hle
    have hlt : wrapSub w p L.nicheStart < L.nicheSpan := Nat.lt_succ_of_le hle
    exact Nat.not_lt_of_ge hge_span hlt
  unfold decodeNicheTag
  dsimp only
  simp only [hnot_le, htag_valid, ↓reduceIte]

/-- Backward round-trip / bijection theorem: if `tag < 2^w` decodes to `.ok v`, then
EITHER `v = L.untaggedVariant` and `L.validPayloadRange.contains tag = true`,
OR `L.isNichedVariant v` and `L.encodeVariantTag v = some tag`. -/
theorem decode_ok_iff_encoded_or_payload {w : Nat} (L : NicheLayout w) (hwf : L.WellFormed)
    (tag : Nat) (htag : tag < modulus w) (v : Nat) :
    L.decodeNicheTag tag = .ok v ↔
      (v = L.untaggedVariant ∧ L.validPayloadRange.contains tag = true) ∨
      (L.isNichedVariant v ∧ L.encodeVariantTag v = some tag) := by
  constructor
  · intro hdec
    unfold decodeNicheTag at hdec
    dsimp only at hdec
    by_cases hrel : wrapSub w tag L.nicheStart ≤ L.nicheMaxRel
    · simp only [hrel, ↓reduceIte] at hdec
      let k := wrapSub w tag L.nicheStart
      change (if L.nicheVariantsStart + k = L.untaggedVariant then DecodeResult.ubInvalidTag tag
              else if L.tagValidRange.contains tag = true then DecodeResult.ok (L.nicheVariantsStart + k)
              else DecodeResult.ubInvalidTag tag) = DecodeResult.ok v at hdec
      by_cases hu : L.nicheVariantsStart + k = L.untaggedVariant
      · simp only [hu, ↓reduceIte] at hdec; cases hdec
      · simp only [hu, ↓reduceIte] at hdec
        cases htv : L.tagValidRange.contains tag with
        | false => simp only [htv, Bool.false_eq_true, ↓reduceIte] at hdec; cases hdec
        | true =>
          simp only [htv, ↓reduceIte] at hdec
          injection hdec with hv_eq
          subst hv_eq
          right
          have hge : L.nicheVariantsStart ≤ L.nicheVariantsStart + k := Nat.le_add_right _ _
          have hle : L.nicheVariantsStart + k ≤ L.nicheVariantsEnd := by
            have h1 : L.nicheVariantsStart + k ≤ L.nicheVariantsStart + (L.nicheVariantsEnd - L.nicheVariantsStart) :=
              Nat.add_le_add_left hrel _
            rw [Nat.add_sub_of_le hwf.nicheRangeValid.1] at h1
            exact h1
          refine ⟨⟨hge, hle, hu⟩, ?_⟩
          unfold encodeVariantTag
          simp only [hu, hge, hle, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
          exact congrArg some (wrapAdd_wrapSub_cancel w L.nicheStart tag hwf.nicheStartLt htag)
    · simp only [hrel, ↓reduceIte] at hdec
      cases htv : L.tagValidRange.contains tag with
      | false => simp only [htv, Bool.false_eq_true, ↓reduceIte] at hdec; cases hdec
      | true =>
        simp only [htv, ↓reduceIte] at hdec
        injection hdec with hv_eq
        subst hv_eq
        left
        refine ⟨rfl, ?_⟩
        cases hwf.tagCoveredByPayloadOrArc tag htag htv with
        | inl hpay => exact hpay
        | inr hlt_span =>
          exact False.elim (hrel (Nat.le_of_lt_succ hlt_span))
  · intro hor
    cases hor with
    | inl hpay =>
      rw [hpay.1]
      exact decode_untagged_payload_roundtrip L hwf tag htag hpay.2
    | inr hnic =>
      rcases encode_decode_niched_roundtrip L hwf v hnic.1 with ⟨tag', _, henc', hdec'⟩
      rw [hnic.2] at henc'
      injection henc' with hteq
      rw [hteq]
      exact hdec'

/-- Injectivity of niche encoding: distinct niched variants never share a tag bit-pattern. -/
theorem encodeVariantTag_injective {w : Nat} (L : NicheLayout w) (hwf : L.WellFormed)
    (v1 v2 tag : Nat) (h1 : L.encodeVariantTag v1 = some tag)
    (h2 : L.encodeVariantTag v2 = some tag) : v1 = v2 := by
  have extract : ∀ v, L.encodeVariantTag v = some tag → L.isNichedVariant v ∧ tag < modulus w := by
    intro v hv
    unfold encodeVariantTag at hv
    by_cases hu : v = L.untaggedVariant
    · simp only [hu, ↓reduceIte] at hv; cases hv
    · simp only [hu, ↓reduceIte] at hv
      by_cases hr : L.nicheVariantsStart ≤ v ∧ v ≤ L.nicheVariantsEnd
      · simp only [hr] at hv
        injection hv with hteq
        subst hteq
        exact ⟨⟨hr.1, hr.2, hu⟩, wrapAdd_lt _ _ _⟩
      · simp only [hr, ↓reduceIte] at hv; cases hv
  have ⟨hn1, ht⟩ := extract v1 h1
  have ⟨hn2, _⟩ := extract v2 h2
  have hd1 := (decode_ok_iff_encoded_or_payload L hwf tag ht v1).mpr (Or.inr ⟨hn1, h1⟩)
  have hd2 := (decode_ok_iff_encoded_or_payload L hwf tag ht v2).mpr (Or.inr ⟨hn2, h2⟩)
  rw [hd1] at hd2
  injection hd2

/-- Dead-slot theorem: whenever `untaggedVariant` falls inside `nicheVariantsStart..=nicheVariantsEnd`,
its corresponding niche tag `wrapAdd w nicheStart (untaggedVariant - nicheVariantsStart)` is
INSIDE `tagValidRange` yet ALWAYS triggers `.ubInvalidTag` in `decodeNicheTag`!
Mirrors `discriminant.rs:188-193` and `operand.rs:606-615`. -/
theorem dead_middle_slot_triggers_invalid_tag {w : Nat} (L : NicheLayout w) (hwf : L.WellFormed)
    (hge : L.nicheVariantsStart ≤ L.untaggedVariant)
    (hle : L.untaggedVariant ≤ L.nicheVariantsEnd) :
    let deadTag := wrapAdd w L.nicheStart (L.untaggedVariant - L.nicheVariantsStart)
    L.tagValidRange.contains deadTag = true ∧
    L.validPayloadRange.contains deadTag = false ∧
    L.decodeNicheTag deadTag = .ubInvalidTag deadTag := by
  dsimp only
  let k := L.untaggedVariant - L.nicheVariantsStart
  have hk_le : k ≤ L.nicheMaxRel := Nat.sub_le_sub_right hle L.nicheVariantsStart
  have hk_lt_span : k < L.nicheSpan := Nat.lt_succ_of_le hk_le
  have hk_lt_mod : k < modulus w := Nat.lt_trans hk_lt_span (nicheSpan_lt_modulus L hwf)
  let deadTag := wrapAdd w L.nicheStart k
  have ⟨hout, hin⟩ := hwf.nicheArcOutsidePayload k hk_lt_span
  refine ⟨hin, hout, ?_⟩
  unfold decodeNicheTag
  dsimp only
  have hrel : wrapSub w (wrapAdd w L.nicheStart (L.untaggedVariant - L.nicheVariantsStart)) L.nicheStart = k :=
    wrapSub_wrapAdd_cancel w L.nicheStart k hwf.nicheStartLt hk_lt_mod
  have hadd : L.nicheVariantsStart + k = L.untaggedVariant := by
    change L.nicheVariantsStart + (L.untaggedVariant - L.nicheVariantsStart) = L.untaggedVariant
    rw [Nat.add_comm, Nat.sub_add_cancel hge]
  simp only [hrel, hk_le, hadd, ↓reduceIte]

/-! ## Section 5: Theorem 2 — Necessary-and-Sufficient Niche Capacity & Variant-Order Non-Monotonicity -/

/-- Exact contiguous niche variant range `[start, last]` computed by
`calculate_niche_filling_layout` (`compiler/rustc_abi/src/layout/enum_layout.rs:604-611`)
when all `numVariants ≥ 2` variants are inhabited and `untagged < numVariants`. -/
def computeNicheVariantBounds (numVariants untagged : Nat) : Nat × Nat :=
  let start := if untagged = 0 then 1 else 0
  let last := if untagged + 1 = numVariants then numVariants - 2 else numVariants - 1
  (start, last)

/-- Required niche count `count = last - start + 1` (`enum_layout.rs:611`). -/
def requiredNicheCount (numVariants untagged : Nat) : Nat :=
  let (start, last) := computeNicheVariantBounds numVariants untagged
  last - start + 1

/-- Necessary-and-sufficient capacity theorem for `Niche::reserve` (`lib.rs:2148-2150`):
both `reserveFromEnd` and `reserveFromStart` succeed if and only if
`(vEnd - vStart + 1) ≤ r.availableNiches`. -/
theorem niche_capacity_iff {w : Nat} (r : WrappingRange w) (vStart vEnd : Nat) :
    (r.reserveFromEnd (vEnd - vStart + 1)).isSome = true ↔
      (vEnd - vStart + 1) ≤ r.availableNiches := by
  unfold WrappingRange.reserveFromEnd
  have hpos : 0 < vEnd - vStart + 1 := Nat.succ_pos _
  by_cases hle : vEnd - vStart + 1 ≤ r.availableNiches
  · simp only [hpos, hle, and_self, ↓reduceIte, Option.isSome_some]
  · have hnot : ¬ (0 < vEnd - vStart + 1 ∧ vEnd - vStart + 1 ≤ r.availableNiches) :=
      fun h => hle h.2
    simp only [hnot, ↓reduceIte, Option.isSome_none, Bool.false_eq_true]
    exact ⟨False.elim, hle⟩

theorem niche_capacity_start_iff {w : Nat} (r : WrappingRange w) (vStart vEnd : Nat) :
    (r.reserveFromStart (vEnd - vStart + 1)).isSome = true ↔
      (vEnd - vStart + 1) ≤ r.availableNiches := by
  unfold WrappingRange.reserveFromStart
  have hpos : 0 < vEnd - vStart + 1 := Nat.succ_pos _
  by_cases hle : vEnd - vStart + 1 ≤ r.availableNiches
  · simp only [hpos, hle, and_self, ↓reduceIte, Option.isSome_some]
  · have hnot : ¬ (0 < vEnd - vStart + 1 ∧ vEnd - vStart + 1 ≤ r.availableNiches) :=
      fun h => hle h.2
    simp only [hnot, ↓reduceIte, Option.isSome_none, Bool.false_eq_true]
    exact ⟨False.elim, hle⟩

/-- General Variant-Order Non-Monotonicity Theorem:
For ANY enum with `n ≥ 3` inhabited variants:
- Placing the untagged variant at either edge (`untagged = 0` or `untagged = n - 1`)
  requires `n - 1` niches;
- Placing the untagged variant in the interior (`0 < untagged` and `untagged + 1 < n`)
  requires `n` niches — strictly 1 extra niche slot to span and skip `untagged`! -/
theorem edge_vs_interior_required_niches (n untagged : Nat) (hn : 3 ≤ n) :
    (untagged = 0 → requiredNicheCount n untagged = n - 1) ∧
    (untagged + 1 = n → requiredNicheCount n untagged = n - 1) ∧
    (0 < untagged → untagged + 1 < n → requiredNicheCount n untagged = n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    subst h0
    unfold requiredNicheCount computeNicheVariantBounds
    dsimp only
    have hne1 : ¬ (0 + 1 = n) := by
      intro heq
      rw [← heq] at hn
      cases hn with | step h => cases h
    simp only [↓reduceIte, hne1]
    have h2 : 1 ≤ n - 1 := by
      have h1 : 1 + 1 ≤ n := Nat.le_trans (by decide : 2 ≤ 3) hn
      exact Nat.le_sub_of_add_le h1
    exact Nat.sub_add_cancel h2
  · intro hlast
    unfold requiredNicheCount computeNicheVariantBounds
    dsimp only
    have hne0 : untagged ≠ 0 := by
      intro h0
      rw [h0] at hlast
      rw [← hlast] at hn
      cases hn with | step h => cases h
    simp only [hne0, hlast, ↓reduceIte, Nat.sub_zero]
    have hge2 : 2 ≤ n := Nat.le_trans (by decide : 2 ≤ 3) hn
    have h1 : n - 2 + 1 + 1 = n := by
      rw [Nat.add_assoc]; exact Nat.sub_add_cancel hge2
    calc
      n - 2 + 1 = (n - 2 + 1 + 1) - 1 := (Nat.add_sub_cancel _ 1).symm
      _ = n - 1 := by rw [h1]
  · intro hgt0 hlt
    unfold requiredNicheCount computeNicheVariantBounds
    dsimp only
    have hne0 : untagged ≠ 0 := Nat.ne_of_gt hgt0
    have hneLast : untagged + 1 ≠ n := Nat.ne_of_lt hlt
    simp only [hne0, hneLast, ↓reduceIte, Nat.sub_zero]
    have hge1 : 1 ≤ n := Nat.le_trans (by decide : 1 ≤ 3) hn
    exact Nat.sub_add_cancel hge1

/-- Exact 3-Variant / 2-Niche Size Dichotomy:
For a 3-variant enum whose payload has `availableNiches = 2` (like `Inner1To254`),
niche filling succeeds (yielding `1 B` layout) IF AND ONLY IF the untagged payload
variant is declared at an edge (`untagged = 0` or `untagged = 2`), and fails (forcing
a `2 B` `TagEncoding::Direct` fallback) when declared in the middle (`untagged = 1`). -/
theorem three_variant_two_niche_dichotomy {w : Nat} (r : WrappingRange w)
    (h2 : r.availableNiches = 2) (untagged : Nat) (hu : untagged < 3) :
    let (vStart, vEnd) := computeNicheVariantBounds 3 untagged
    (r.reserveFromEnd (vEnd - vStart + 1)).isSome = true ↔ (untagged = 0 ∨ untagged = 2) := by
  dsimp only
  rw [niche_capacity_iff, h2]
  match untagged with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | n + 3 =>
    exfalso
    exact Nat.not_lt_of_ge (Nat.le_add_left 3 n) hu

/-! ## Section 6: Theorem 3 — Payload-Write-Before-`SetDiscriminant` Soundness & Codegen Refinement -/

/-- Operational Soundness of Payload-Write-Before-`SetDiscriminant`:
Starting from ANY `TagSlot` (including `.uninit` or a stale niched tag such as `None`),
writing a valid untagged payload `p < 2^w` first (`slot₁ := .init p`) and THEN executing
`evalSetDiscriminant L L.untaggedVariant slot₁` ALWAYS succeeds with `.ok (.init p)`,
preserves `decodeNicheTag L p = .ok L.untaggedVariant`, and agrees with `evalCodegenSetDiscr`. -/
theorem payload_write_before_set_discriminant_sound {w : Nat} (L : NicheLayout w)
    (hwf : L.WellFormed) (p : Nat) (hp : p < modulus w)
    (hvalid : L.validPayloadRange.contains p = true) :
    L.evalSetDiscriminant L.untaggedVariant (.init p) = .ok (.init p) ∧
    L.decodeNicheTag p = .ok L.untaggedVariant ∧
    L.evalCodegenSetDiscr L.untaggedVariant (.init p) = .init p := by
  have hdec := decode_untagged_payload_roundtrip L hwf p hp hvalid
  refine ⟨?_, hdec, ?_⟩
  · unfold evalSetDiscriminant
    simp only [↓reduceIte, hdec]
  · unfold evalCodegenSetDiscr encodeVariantTag
    simp only [↓reduceIte]

/-- Operational Soundness of `SetDiscriminant` for Niched Variants:
For any niched variant `v`, executing `evalSetDiscriminant L v slot` succeeds from ANY
initial `slot` (including `.uninit`), produces a tag `t < 2^w` that decodes to `.ok v`,
and agrees with `evalCodegenSetDiscr`. -/
theorem niched_set_discriminant_sound {w : Nat} (L : NicheLayout w) (hwf : L.WellFormed)
    (v : Nat) (hv : L.isNichedVariant v) (slot : TagSlot) :
    ∃ tag, tag < modulus w ∧
      L.evalSetDiscriminant v slot = .ok (.init tag) ∧
      L.decodeNicheTag tag = .ok v ∧
      L.evalCodegenSetDiscr v slot = .init tag := by
  rcases encode_decode_niched_roundtrip L hwf v hv with ⟨tag, hlt, henc, hdec⟩
  refine ⟨tag, hlt, ?_, hdec, ?_⟩
  · unfold evalSetDiscriminant
    simp only [hv.2.2, ↓reduceIte, henc]
  · unfold evalCodegenSetDiscr
    rw [henc]

/-- Refinement Theorem (`codegen_set_discr` refines `InterpCx::write_discriminant`):
Whenever operational `evalSetDiscriminant` does NOT trigger UB (returns `.ok nextSlot`),
`evalCodegenSetDiscr` produces the exact same post-state `nextSlot`! -/
theorem codegen_set_discr_refines_miri {w : Nat} (L : NicheLayout w) (v : Nat)
    (slot nextSlot : TagSlot)
    (hok : L.evalSetDiscriminant v slot = .ok nextSlot) :
    L.evalCodegenSetDiscr v slot = nextSlot := by
  unfold evalSetDiscriminant at hok
  unfold evalCodegenSetDiscr
  by_cases hu : v = L.untaggedVariant
  · simp only [hu, ↓reduceIte] at hok
    unfold encodeVariantTag
    simp only [hu, ↓reduceIte]
    cases slot with
    | uninit => cases hok
    | init bits =>
      dsimp only at hok
      cases hdec : L.decodeNicheTag bits with
      | ubInvalidTag _ => rw [hdec] at hok; cases hok
      | ok actual =>
        rw [hdec] at hok
        dsimp only at hok
        by_cases heq : actual = L.untaggedVariant
        · simp only [heq, ↓reduceIte] at hok
          injection hok
        · simp only [heq, ↓reduceIte] at hok
          cases hok
  · simp only [hu, ↓reduceIte] at hok
    cases henc : L.encodeVariantTag v with
    | none => rw [henc] at hok; cases hok
    | some tag =>
      rw [henc] at hok
      injection hok

end NicheLayout

/-! ## Section 7: Three Constructive Sharpness Counterexamples -/

/-- `Inner1To254` scalar validity range `1..=254` on `u8` (`w = 8`): 2 wrapping niches `{255, 0}`. -/
def inner1To254Range : WrappingRange 8 := { start := 1, end_ := 254 }

/-- `Inner1To253` scalar validity range `1..=253` on `u8` (`w = 8`): 3 wrapping niches `{254, 255, 0}`. -/
def inner1To253Range : WrappingRange 8 := { start := 1, end_ := 253 }

/-- `OuterThreeEdge { UntaggedPayload(Inner1To254), FirstNiche, SecondNiche }`:
`untagged = 0`, `nicheVariants = 1..=2`, `nicheStart = 255`, `tagValidRange = 1..=0` (full). -/
def outerThreeEdgeLayout : NicheLayout 8 := {
  numVariants := 3
  validPayloadRange := inner1To254Range
  untaggedVariant := 0
  nicheVariantsStart := 1
  nicheVariantsEnd := 2
  nicheStart := 255
  tagValidRange := { start := 1, end_ := 0 }
}

theorem outerThreeEdgeLayout_wellFormed : outerThreeEdgeLayout.WellFormed :=
  (NicheLayout.mkFromReserveEnd 3 0 1 2 inner1To254Range (by decide) (by decide) (by decide)
    255 { start := 1, end_ := 0 } (by decide)).property

/-- `OuterThreeMiddle3Niches { FirstNiche, UntaggedPayload(Inner1To253), SecondNiche }`:
`untagged = 1`, `nicheVariants = 0..=2`, `nicheStart = 254`, `tagValidRange = 1..=0` (full),
leaving byte `255` (`0xff`) as an impossible dead middle niche slot inside `tagValidRange`! -/
def outerThreeMiddle3NichesLayout : NicheLayout 8 := {
  numVariants := 3
  validPayloadRange := inner1To253Range
  untaggedVariant := 1
  nicheVariantsStart := 0
  nicheVariantsEnd := 2
  nicheStart := 254
  tagValidRange := { start := 1, end_ := 0 }
}

theorem outerThreeMiddle3NichesLayout_wellFormed : outerThreeMiddle3NichesLayout.WellFormed :=
  (NicheLayout.mkFromReserveEnd 3 1 0 2 inner1To253Range (by decide) (by decide) (by decide)
    254 { start := 1, end_ := 0 } (by decide)).property

/-- `Option<NonZero<u8>>`: `validPayloadRange = 1..=255`, `untagged = 1` (`Some`),
`nicheVariants = 0..=0` (`None`), `nicheStart = 0`, `tagValidRange = 0..=255`. -/
def optionNonZeroU8Layout : NicheLayout 8 := {
  numVariants := 2
  validPayloadRange := { start := 1, end_ := 255 }
  untaggedVariant := 1
  nicheVariantsStart := 0
  nicheVariantsEnd := 0
  nicheStart := 0
  tagValidRange := { start := 0, end_ := 255 }
}

theorem optionNonZeroU8Layout_wellFormed : optionNonZeroU8Layout.WellFormed :=
  (NicheLayout.mkFromReserveStart 2 1 0 0 { start := 1, end_ := 255 } (by decide) (by decide) (by decide)
    0 { start := 0, end_ := 255 } (by decide)).property

/-- `Option<bool>`: `validPayloadRange = 0..=1`, `untagged = 1` (`Some`),
`nicheVariants = 0..=0` (`None`), `nicheStart = 2`, `tagValidRange = 0..=2`. -/
def optionBoolLayout : NicheLayout 8 := {
  numVariants := 2
  validPayloadRange := { start := 0, end_ := 1 }
  untaggedVariant := 1
  nicheVariantsStart := 0
  nicheVariantsEnd := 0
  nicheStart := 2
  tagValidRange := { start := 0, end_ := 2 }
}

theorem optionBoolLayout_wellFormed : optionBoolLayout.WellFormed :=
  (NicheLayout.mkFromReserveEnd 2 1 0 0 { start := 0, end_ := 1 } (by decide) (by decide) (by decide)
    2 { start := 0, end_ := 2 } (by decide)).property

/-- **Counterexample 1 (`ce1_middle_untagged_variant_exceeds_two_niche_capacity`)**:
For `Inner1To254` (`availableNiches = 2`), `OuterThreeEdge` (`untagged = 0`, `nicheVariants = 1..=2`,
span `2`) fits in `1 B` with wrapping niche tags `FirstNiche = 255` and `SecondNiche = 0`,
whereas reordering the same variants to `OuterThreeMiddle` (`untagged = 1`, `nicheVariants = 0..=2`,
span `3`) exceeds the `2`-niche budget so BOTH `reserveFromEnd` and `reserveFromStart` fail (`none`),
forcing `rustc` to fall back to `2 B` `TagEncoding::Direct`. -/
theorem ce1_middle_untagged_variant_exceeds_two_niche_capacity :
    inner1To254Range.availableNiches = 2 ∧
    NicheLayout.requiredNicheCount 3 0 = 2 ∧
    NicheLayout.requiredNicheCount 3 1 = 3 ∧
    inner1To254Range.reserveFromEnd 2 = some (255, { start := 1, end_ := 0 }) ∧
    outerThreeEdgeLayout.encodeVariantTag 1 = some 255 ∧
    outerThreeEdgeLayout.encodeVariantTag 2 = some 0 ∧
    outerThreeEdgeLayout.decodeNicheTag 255 = .ok 1 ∧
    outerThreeEdgeLayout.decodeNicheTag 0 = .ok 2 ∧
    outerThreeEdgeLayout.decodeNicheTag 42 = .ok 0 ∧
    inner1To254Range.reserveFromEnd 3 = none ∧
    inner1To254Range.reserveFromStart 3 = none := by
  decide

/-- **Counterexample 2 (`ce2_set_discriminant_before_payload_triggers_niched_ub`)**:
On `Option<NonZero<u8>>`:
- Reordering `SetDiscriminant(RET, 1)` BEFORE writing payload `7` over a `None`-initialized
  slot (`.init 0`) triggers `.err (.ubInvalidNichedEnumVariantWritten 1 0)` in Miri,
- Reordering `SetDiscriminant(RET, 1)` BEFORE writing payload `7` over an uninitialized slot
  (`.uninit`) triggers `.err .ubUninitRead` in Miri,
- Yet `evalCodegenSetDiscr` (which emits zero instructions for `untaggedVariant = 1`) leaves
  both reordered executions producing `.init 7` after the payload store — identical to the
  valid payload-before-`SetDiscriminant` order (`.ok (.init 7)`). -/
theorem ce2_set_discriminant_before_payload_triggers_niched_ub :
    optionNonZeroU8Layout.evalSetDiscriminant 1 (.init 0) =
      .err (.ubInvalidNichedEnumVariantWritten 1 0) ∧
    optionNonZeroU8Layout.evalSetDiscriminant 1 .uninit =
      .err .ubUninitRead ∧
    optionNonZeroU8Layout.evalCodegenSetDiscr 1 (.init 0) = .init 0 ∧
    optionNonZeroU8Layout.evalCodegenSetDiscr 1 .uninit = .uninit ∧
    optionNonZeroU8Layout.evalSetDiscriminant 1 (.init 7) = .ok (.init 7) ∧
    optionNonZeroU8Layout.decodeNicheTag 7 = .ok 1 := by
  decide

/-- **Counterexample 3 (`ce3_unassigned_niche_hole_triggers_invalid_tag_ub`)**:
Demonstrates BOTH `InvalidTag` UB branches in `read_discriminant`:
1. `Option<bool>` byte `3` lies outside `tagValidRange = 0..=2` (`discriminant.rs:198-200`)
   and faults `.ubInvalidTag 3`.
2. `OuterThreeMiddle3Niches` byte `255` (`0xff`) lies INSIDE `tagValidRange = 1..=0` (full)
   AND inside `niche_variants = 0..=2`, yet maps to `v = 1 = untaggedVariant` (`discriminant.rs:188-193`)
   and faults `.ubInvalidTag 255`. -/
theorem ce3_unassigned_niche_hole_triggers_invalid_tag_ub :
    optionBoolLayout.tagValidRange.contains 3 = false ∧
    optionBoolLayout.decodeNicheTag 3 = .ubInvalidTag 3 ∧
    outerThreeMiddle3NichesLayout.encodeVariantTag 0 = some 254 ∧
    outerThreeMiddle3NichesLayout.encodeVariantTag 2 = some 0 ∧
    outerThreeMiddle3NichesLayout.tagValidRange.contains 255 = true ∧
    outerThreeMiddle3NichesLayout.validPayloadRange.contains 255 = false ∧
    outerThreeMiddle3NichesLayout.decodeNicheTag 255 = .ubInvalidTag 255 := by
  decide

end RustcNicheLayout
