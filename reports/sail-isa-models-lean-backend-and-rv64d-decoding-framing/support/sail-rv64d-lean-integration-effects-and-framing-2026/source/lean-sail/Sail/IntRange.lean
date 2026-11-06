-- Inclusive ranges

structure IntRange where
  start : Int := 0
  stop  : Int
  step  : Int := 1
  step_pos : step ≠ 0 := by omega

namespace IntRange

instance instMemIntRange : Membership Int IntRange where
  mem r i := (if r.step > 0 then r.start ≤ i ∧ i ≤ r.stop else r.stop ≤ i ∧ i ≤ r.start ) ∧ (i - r.start) % r.step = 0

instance : DecidableRel (fun (i : Int) (r : IntRange) => i ∈ r) := fun i r => by
  simp only [Membership.mem]
  infer_instance

theorem toNat_le {n : Nat} : Int.toNat m ≤ n ↔ m ≤ n := by
  rw [Int.ofNat_le.symm, Int.toNat_eq_max, Int.max_le]; exact and_iff_left (Int.natCast_nonneg _)

theorem lt_toNat {m : Nat} : m < Int.toNat n ↔ (m : Int) < n := by rw [← Int.not_le, ← Nat.not_le, toNat_le]

-- Copied from Mathlib
theorem toNat_lt_toNat {a b : Int} (hb : 0 < b) : Int.toNat a < Int.toNat b ↔ a < b where
  mp h := by cases a; exact lt_toNat.1 h; exact Int.lt_trans (Int.neg_of_sign_eq_neg_one rfl) hb
  mpr h := by rw [lt_toNat]; cases a; exact h; exact hb

@[inline] protected def forIn' [Monad m] (range : IntRange) (init : β)
    (f : (i : Int) → i ∈ range → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (b : β) (i : Int)
      (hs : (i - range.start) % range.step = 0) : m β := do
    if h : i ∈ range then
      match (← f i h b) with
      | .done b  => pure b
      | .yield b =>
        have := range.step_pos
        loop b (i + range.step) (by rw [Int.add_comm, Int.add_sub_assoc]; simp_all)
    else
      pure b
  termination_by if range.step > 0 then (range.stop - i + 1).toNat else (i - range.stop + 1).toNat
  decreasing_by
    split
    · rw [toNat_lt_toNat]
      · omega
      · simp_all [Membership.mem]
        omega
    · simp_all only [Membership.mem, gt_iff_lt, ite_false, and_true, ne_eq]; rw [toNat_lt_toNat]
      · omega
      · omega

  have := range.step_pos
  loop init range.start (by simp)

instance [Monad m] : ForIn' m IntRange Int inferInstance where
  forIn' := IntRange.forIn'

-- No separate `ForIn` instance is required because it can be derived from `ForIn'`.

@[inline] protected def forM [Monad m] (range : IntRange) (f : Int → m PUnit) : m PUnit :=
  let rec @[specialize] loop (i : Int): m PUnit := do
    if i ∈ range then
      f i
      have := range.step_pos
      loop (i + range.step)
    else
      pure ⟨⟩
  termination_by if range.step > 0 then (range.stop - i + 1).toNat else (i - range.stop + 1).toNat
  decreasing_by
    split
    · rw [toNat_lt_toNat]
      · lia
      · simp_all [Membership.mem]
        lia
    · simp_all only [Membership.mem, gt_iff_lt, ite_false, ne_eq]; rw [toNat_lt_toNat]
      · omega
      · lia
  have := range.step_pos
  loop range.start

instance [Monad m] : ForM m IntRange Int where
  forM := IntRange.forM

syntax:max "[" withoutPosition(":" term) "]i" : term
syntax:max "[" withoutPosition(term ":" term) "]i" : term
syntax:max "[" withoutPosition(":" term ":" term) "]i" : term
syntax:max "[" withoutPosition(term ":" term ":" term) "]i" : term

macro_rules
  | `([ : $stop]i) => `({ stop := $stop, step_pos := Nat.zero_lt_one : IntRange })
  | `([ $start : $stop ]i) => `({ start := $start, stop := $stop, step_pos := Nat.zero_lt_one : IntRange })
  | `([ $start : $stop : $step ]i) => `({ start := $start, stop := $stop, step := $step : IntRange })
  | `([ : $stop : $step ]i) => `({ stop := $stop, step := $step : IntRange })

end IntRange
