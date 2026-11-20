import Toy.MachInt.Defs
import Toy.MachInt.Examples

/-!
# Proof-support lemmas (`Toy.MachInt`)

Auxiliary lemmas used only inside the proofs of the main results in
`Toy.MachInt.Statements`. Nothing here changes a definition from `Toy.MachInt.Defs`.
-/

namespace Toy.MachInt

/-! ## Result 1 support: wrapping evaluation is `BitVec.ofInt` of integer evaluation -/

/-- Wrapping evaluation equals `BitVec.ofInt n` of integer evaluation, for every integer
    environment `ρ` whose entries reduce to `env` modulo `2^n`. -/
theorem evalWrap_eq_ofInt_evalInt (n : Nat) (env : Nat → BitVec n) (ρ : Nat → Int)
    (hρ : ∀ i, BitVec.ofInt n (ρ i) = env i) (e : RingExpr) :
    evalWrap n env e = BitVec.ofInt n (evalInt ρ e) := by
  induction e with
  | var i => exact (hρ i).symm
  | lit k => rfl
  | neg e ih => rw [evalWrap, evalInt, ih, BitVec.ofInt_neg]
  | add e₁ e₂ ih₁ ih₂ => rw [evalWrap, evalInt, ih₁, ih₂, BitVec.ofInt_add]
  | sub e₁ e₂ ih₁ ih₂ =>
      rw [evalWrap, evalInt, ih₁, ih₂, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
        BitVec.sub_eq_add_neg]
  | mul e₁ e₂ ih₁ ih₂ => rw [evalWrap, evalInt, ih₁, ih₂, BitVec.ofInt_mul]

/-- The unsigned reading `toNat` of a bitvector reduces back to it under `BitVec.ofInt`. -/
theorem ofInt_toNat_cast {n : Nat} (x : BitVec n) : BitVec.ofInt n (x.toNat : Int) = x := by
  simp

/-- The signed reading `toInt` of a bitvector reduces back to it under `BitVec.ofInt`. -/
theorem ofInt_toInt_self {n : Nat} (x : BitVec n) : BitVec.ofInt n x.toInt = x :=
  BitVec.ofInt_toInt

/-! ## Range helpers -/

/-- The root of an expression satisfies the range predicate whenever every subexpression does. -/
theorem subexprsInRange_root {P : Int → Prop} {ρ : Nat → Int} :
    ∀ {e : RingExpr}, SubexprsInRange P ρ e → P (evalInt ρ e)
  | .var _, h => h
  | .lit _, h => h
  | .neg _, h => h.2
  | .add _ _, h => h.2.2
  | .sub _ _, h => h.2.2
  | .mul _ _, h => h.2.2

/-- `2^n` as an integer, for positive `n`, is twice `2^(n-1)`. -/
theorem two_pow_eq_two_mul_two_pow_pred {n : Nat} (hn : 0 < n) :
    ((2 ^ n : Nat) : Int) = 2 * (2 : Int) ^ (n - 1) := by
  have hs : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  have hnat : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc 2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) hs
      _ = 2 ^ (n - 1) * 2 := Nat.pow_succ 2 (n - 1)
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  rw [hnat]
  push_cast
  rfl

/-- At width zero the signed range is `{0}`. -/
theorem inSignedRange_zero_iff (z : Int) : InSignedRange 0 z ↔ z = 0 := by
  unfold InSignedRange sMinVal sMaxVal
  have h1 : (BitVec.intMin 0).toInt = 0 := by decide
  have h2 : (BitVec.intMax 0).toInt = 0 := by decide
  rw [h1, h2]
  omega

/-- At positive width the signed range is `[-2^(n-1), 2^(n-1))`. -/
theorem inSignedRange_iff_of_pos {n : Nat} (hn : 0 < n) (z : Int) :
    InSignedRange n z ↔ (-(2 : Int) ^ (n - 1) ≤ z ∧ z < (2 : Int) ^ (n - 1)) := by
  unfold InSignedRange sMinVal sMaxVal
  rw [BitVec.toInt_intMin_of_pos hn, BitVec.toInt_intMax]
  omega

/-- Every signed reading `x.toInt` lies in `InSignedRange n`. -/
theorem inSignedRange_toInt {n : Nat} (x : BitVec n) : InSignedRange n x.toInt := by
  refine ⟨BitVec.toInt_intMin_le x, ?_⟩
  unfold sMaxVal
  rw [BitVec.toInt_intMax]
  have := @BitVec.toInt_lt n x
  omega

/-- Every unsigned reading `x.toNat` lies in `InUnsignedRange n`. -/
theorem inUnsignedRange_toNat {n : Nat} (x : BitVec n) : InUnsignedRange n (x.toNat : Int) := by
  have := x.isLt
  unfold InUnsignedRange
  omega

/-- Balanced reduction modulo `2^n` fixes every integer in `InSignedRange n`. -/
theorem bmod_eq_self_of_inSignedRange {n : Nat} {z : Int} (h : InSignedRange n z) :
    z.bmod (2 ^ n) = z := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [(inSignedRange_zero_iff z).1 h]
    rfl
  · rw [inSignedRange_iff_of_pos hn] at h
    apply Int.bmod_eq_of_le_mul_two
    · rw [two_pow_eq_two_mul_two_pow_pred hn]; omega
    · rw [two_pow_eq_two_mul_two_pow_pred hn]; omega

/-- Euclidean reduction modulo `2^n` fixes every integer in `InUnsignedRange n`. -/
theorem emod_eq_self_of_inUnsignedRange {n : Nat} {z : Int} (h : InUnsignedRange n z) :
    z % ((2 ^ n : Nat) : Int) = z :=
  Int.emod_eq_of_lt h.1 h.2

/-! ## Unsigned primitive overflow flags vs. integer ranges -/

theorem uaddOverflow_eq_false_iff {n : Nat} (a b : BitVec n) :
    BitVec.uaddOverflow a b = false ↔ InUnsignedRange n ((a.toNat : Int) + (b.toNat : Int)) := by
  unfold BitVec.uaddOverflow InUnsignedRange
  simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]
  omega

theorem usubOverflow_eq_false_iff {n : Nat} (a b : BitVec n) :
    BitVec.usubOverflow a b = false ↔ InUnsignedRange n ((a.toNat : Int) - (b.toNat : Int)) := by
  have := a.isLt
  unfold BitVec.usubOverflow InUnsignedRange
  simp only [decide_eq_false_iff_not, Nat.not_lt]
  omega

theorem umulOverflow_eq_false_iff {n : Nat} (a b : BitVec n) :
    BitVec.umulOverflow a b = false ↔ InUnsignedRange n ((a.toNat : Int) * (b.toNat : Int)) := by
  unfold BitVec.umulOverflow InUnsignedRange
  simp only [decide_eq_false_iff_not, ge_iff_le, Nat.not_le]
  have hc : ((a.toNat * b.toNat : Nat) : Int) = (a.toNat : Int) * (b.toNat : Int) := by push_cast; rfl
  rw [← hc]
  omega

/-! ## Signed primitive overflow flags vs. integer ranges -/

theorem saddOverflow_eq_false_iff {n : Nat} (a b : BitVec n) :
    BitVec.saddOverflow a b = false ↔ InSignedRange n (a.toInt + b.toInt) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [BitVec.eq_nil a, BitVec.eq_nil b]
    decide
  · rw [inSignedRange_iff_of_pos hn]
    unfold BitVec.saddOverflow
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, ge_iff_le, Int.not_le, Int.not_lt]
    omega

theorem ssubOverflow_eq_false_iff {n : Nat} (a b : BitVec n) :
    BitVec.ssubOverflow a b = false ↔ InSignedRange n (a.toInt - b.toInt) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [BitVec.eq_nil a, BitVec.eq_nil b]
    decide
  · rw [inSignedRange_iff_of_pos hn]
    unfold BitVec.ssubOverflow
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, ge_iff_le, Int.not_le, Int.not_lt]
    omega

theorem smulOverflow_eq_false_iff {n : Nat} (a b : BitVec n) :
    BitVec.smulOverflow a b = false ↔ InSignedRange n (a.toInt * b.toInt) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [BitVec.eq_nil a, BitVec.eq_nil b]
    decide
  · rw [inSignedRange_iff_of_pos hn]
    unfold BitVec.smulOverflow
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, ge_iff_le, Int.not_le, Int.not_lt]
    omega

theorem negOverflow_eq_false_iff {n : Nat} (a : BitVec n) :
    BitVec.negOverflow a = false ↔ InSignedRange n (-a.toInt) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [BitVec.eq_nil a]
    decide
  · rw [inSignedRange_iff_of_pos hn]
    have hl := BitVec.le_toInt a
    have hu := @BitVec.toInt_lt n a
    unfold BitVec.negOverflow
    simp only [beq_eq_false_iff_ne, ne_eq]
    omega

/-! ## Result 1 consequences used by Result 2 -/

theorem evalWrap_toNat_cast (n : Nat) (env : Nat → BitVec n) (e : RingExpr) :
    ((evalWrap n env e).toNat : Int) =
      (evalInt (fun i => ((env i).toNat : Int)) e) % ((2 ^ n : Nat) : Int) := by
  rw [evalWrap_eq_ofInt_evalInt n env _ (fun i => ofInt_toNat_cast (env i)) e, BitVec.toNat_ofInt]
  have hpos : (0 : Int) < ((2 ^ n : Nat) : Int) := by
    have := Nat.two_pow_pos n
    omega
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hpos))

theorem evalWrap_toInt_bmod (n : Nat) (env : Nat → BitVec n) (e : RingExpr) :
    (evalWrap n env e).toInt = (evalInt (fun i => (env i).toInt) e).bmod (2 ^ n) := by
  rw [evalWrap_eq_ofInt_evalInt n env _ (fun i => ofInt_toInt_self (env i)) e, BitVec.toInt_ofInt]

/-- If the root value of `e` is in the unsigned range, it equals the unsigned reading of the
    wrapping evaluation. -/
theorem evalInt_eq_evalWrap_toNat_of_inRange (n : Nat) (env : Nat → BitVec n) (e : RingExpr)
    (h : InUnsignedRange n (evalInt (fun i => ((env i).toNat : Int)) e)) :
    evalInt (fun i => ((env i).toNat : Int)) e = ((evalWrap n env e).toNat : Int) := by
  rw [evalWrap_toNat_cast, emod_eq_self_of_inUnsignedRange h]

/-- If the root value of `e` is in the signed range, it equals the signed reading of the
    wrapping evaluation. -/
theorem evalInt_eq_evalWrap_toInt_of_inRange (n : Nat) (env : Nat → BitVec n) (e : RingExpr)
    (h : InSignedRange n (evalInt (fun i => (env i).toInt) e)) :
    evalInt (fun i => (env i).toInt) e = (evalWrap n env e).toInt := by
  rw [evalWrap_toInt_bmod, bmod_eq_self_of_inSignedRange h]

/-! ## Result 2 support: unsigned checked evaluation -/

/-- A successful checked unsigned evaluation returns the wrapping value, and every
    subexpression stayed in range. -/
theorem evalCheckedU_eq_some_imp (n : Nat) (env : Nat → BitVec n) :
    ∀ (e : RingExpr) (v : BitVec n), evalCheckedU n env e = some v →
      v = evalWrap n env e ∧
        SubexprsInRange (InUnsignedRange n) (fun i => ((env i).toNat : Int)) e := by
  intro e
  induction e with
  | var i =>
      intro v h
      simp only [evalCheckedU, Option.some.injEq] at h
      subst h
      exact ⟨rfl, inUnsignedRange_toNat (env i)⟩
  | lit k =>
      intro v h
      simp only [evalCheckedU] at h
      split at h
      · rename_i hk
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, hk⟩
      · cases h
  | neg e ih =>
      intro v h
      simp only [evalCheckedU, Option.bind_eq_some_iff] at h
      obtain ⟨w, hw, hneg⟩ := h
      obtain ⟨hwv, hsub⟩ := ih w hw
      unfold checkedUNeg at hneg
      split at hneg
      · rename_i hz
        simp only [Option.some.injEq] at hneg
        subst hneg
        have hw0 : w = 0#n := by simpa using hz
        have hroot := evalInt_eq_evalWrap_toNat_of_inRange n env e (subexprsInRange_root hsub)
        refine ⟨?_, hsub, ?_⟩
        · show 0#n = -(evalWrap n env e)
          rw [← hwv, hw0]
          simp
        · show InUnsignedRange n (-(evalInt _ e))
          rw [hroot, ← hwv, hw0]
          have := Nat.two_pow_pos n
          unfold InUnsignedRange
          simp only [BitVec.toNat_zero]
          omega
      · cases hneg
  | add e₁ e₂ ih₁ ih₂ =>
      intro v h
      simp only [evalCheckedU, Option.bind_eq_some_iff] at h
      obtain ⟨w₁, hw₁, w₂, hw₂, hop⟩ := h
      obtain ⟨hv₁, hs₁⟩ := ih₁ w₁ hw₁
      obtain ⟨hv₂, hs₂⟩ := ih₂ w₂ hw₂
      have hr₁ := evalInt_eq_evalWrap_toNat_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toNat_of_inRange n env e₂ (subexprsInRange_root hs₂)
      unfold checkedUAdd at hop
      split at hop
      · cases hop
      · rename_i hov
        simp only [Option.some.injEq] at hop
        subst hop
        refine ⟨by rw [hv₁, hv₂]; rfl, hs₁, hs₂, ?_⟩
        show InUnsignedRange n (evalInt _ e₁ + evalInt _ e₂)
        rw [hr₁, hr₂, ← hv₁, ← hv₂]
        exact (uaddOverflow_eq_false_iff w₁ w₂).1 (by simpa using hov)
  | sub e₁ e₂ ih₁ ih₂ =>
      intro v h
      simp only [evalCheckedU, Option.bind_eq_some_iff] at h
      obtain ⟨w₁, hw₁, w₂, hw₂, hop⟩ := h
      obtain ⟨hv₁, hs₁⟩ := ih₁ w₁ hw₁
      obtain ⟨hv₂, hs₂⟩ := ih₂ w₂ hw₂
      have hr₁ := evalInt_eq_evalWrap_toNat_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toNat_of_inRange n env e₂ (subexprsInRange_root hs₂)
      unfold checkedUSub at hop
      split at hop
      · cases hop
      · rename_i hov
        simp only [Option.some.injEq] at hop
        subst hop
        refine ⟨by rw [hv₁, hv₂]; rfl, hs₁, hs₂, ?_⟩
        show InUnsignedRange n (evalInt _ e₁ - evalInt _ e₂)
        rw [hr₁, hr₂, ← hv₁, ← hv₂]
        exact (usubOverflow_eq_false_iff w₁ w₂).1 (by simpa using hov)
  | mul e₁ e₂ ih₁ ih₂ =>
      intro v h
      simp only [evalCheckedU, Option.bind_eq_some_iff] at h
      obtain ⟨w₁, hw₁, w₂, hw₂, hop⟩ := h
      obtain ⟨hv₁, hs₁⟩ := ih₁ w₁ hw₁
      obtain ⟨hv₂, hs₂⟩ := ih₂ w₂ hw₂
      have hr₁ := evalInt_eq_evalWrap_toNat_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toNat_of_inRange n env e₂ (subexprsInRange_root hs₂)
      unfold checkedUMul at hop
      split at hop
      · cases hop
      · rename_i hov
        simp only [Option.some.injEq] at hop
        subst hop
        refine ⟨by rw [hv₁, hv₂]; rfl, hs₁, hs₂, ?_⟩
        show InUnsignedRange n (evalInt _ e₁ * evalInt _ e₂)
        rw [hr₁, hr₂, ← hv₁, ← hv₂]
        exact (umulOverflow_eq_false_iff w₁ w₂).1 (by simpa using hov)

/-- Per-subexpression unsigned range bounds make checked unsigned evaluation succeed with the
    wrapping value. -/
theorem evalCheckedU_eq_some_of_subexprsInRange (n : Nat) (env : Nat → BitVec n) :
    ∀ (e : RingExpr),
      SubexprsInRange (InUnsignedRange n) (fun i => ((env i).toNat : Int)) e →
      evalCheckedU n env e = some (evalWrap n env e) := by
  intro e
  induction e with
  | var i => intro _; rfl
  | lit k =>
      intro h
      have hk : InUnsignedRange n k := h
      simp only [evalCheckedU, hk, ↓reduceIte]
      rfl
  | neg e ih =>
      intro h
      obtain ⟨hs, hr⟩ := h
      have hroot := evalInt_eq_evalWrap_toNat_of_inRange n env e (subexprsInRange_root hs)
      have hr' : InUnsignedRange n (-(evalInt (fun i => ((env i).toNat : Int)) e)) := hr
      rw [hroot] at hr'
      have h0 : (evalWrap n env e).toNat = 0 := by
        unfold InUnsignedRange at hr'
        omega
      have hw0 : evalWrap n env e = 0#n := BitVec.eq_of_toNat_eq (by simpa using h0)
      simp only [evalCheckedU, ih hs, Option.bind_some, checkedUNeg, hw0]
      show (if (0#n == 0#n) = true then some 0#n else none) = some (-(evalWrap n env e))
      rw [hw0]
      simp
  | add e₁ e₂ ih₁ ih₂ =>
      intro h
      obtain ⟨hs₁, hs₂, hr⟩ := h
      have hr₁ := evalInt_eq_evalWrap_toNat_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toNat_of_inRange n env e₂ (subexprsInRange_root hs₂)
      have hr' : InUnsignedRange n (evalInt (fun i => ((env i).toNat : Int)) e₁ +
          evalInt (fun i => ((env i).toNat : Int)) e₂) := hr
      rw [hr₁, hr₂] at hr'
      have hov := (uaddOverflow_eq_false_iff _ _).2 hr'
      simp only [evalCheckedU, ih₁ hs₁, ih₂ hs₂, Option.bind_some, checkedUAdd, hov]
      rfl
  | sub e₁ e₂ ih₁ ih₂ =>
      intro h
      obtain ⟨hs₁, hs₂, hr⟩ := h
      have hr₁ := evalInt_eq_evalWrap_toNat_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toNat_of_inRange n env e₂ (subexprsInRange_root hs₂)
      have hr' : InUnsignedRange n (evalInt (fun i => ((env i).toNat : Int)) e₁ -
          evalInt (fun i => ((env i).toNat : Int)) e₂) := hr
      rw [hr₁, hr₂] at hr'
      have hov := (usubOverflow_eq_false_iff _ _).2 hr'
      simp only [evalCheckedU, ih₁ hs₁, ih₂ hs₂, Option.bind_some, checkedUSub, hov]
      rfl
  | mul e₁ e₂ ih₁ ih₂ =>
      intro h
      obtain ⟨hs₁, hs₂, hr⟩ := h
      have hr₁ := evalInt_eq_evalWrap_toNat_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toNat_of_inRange n env e₂ (subexprsInRange_root hs₂)
      have hr' : InUnsignedRange n (evalInt (fun i => ((env i).toNat : Int)) e₁ *
          evalInt (fun i => ((env i).toNat : Int)) e₂) := hr
      rw [hr₁, hr₂] at hr'
      have hov := (umulOverflow_eq_false_iff _ _).2 hr'
      simp only [evalCheckedU, ih₁ hs₁, ih₂ hs₂, Option.bind_some, checkedUMul, hov]
      rfl

/-! ## Result 2 support: signed checked evaluation -/

/-- A successful checked signed evaluation returns the wrapping value, and every
    subexpression stayed in range. -/
theorem evalCheckedS_eq_some_imp (n : Nat) (env : Nat → BitVec n) :
    ∀ (e : RingExpr) (v : BitVec n), evalCheckedS n env e = some v →
      v = evalWrap n env e ∧
        SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e := by
  intro e
  induction e with
  | var i =>
      intro v h
      simp only [evalCheckedS, Option.some.injEq] at h
      subst h
      exact ⟨rfl, inSignedRange_toInt (env i)⟩
  | lit k =>
      intro v h
      simp only [evalCheckedS] at h
      split at h
      · rename_i hk
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, hk⟩
      · cases h
  | neg e ih =>
      intro v h
      simp only [evalCheckedS, Option.bind_eq_some_iff] at h
      obtain ⟨w, hw, hneg⟩ := h
      obtain ⟨hwv, hsub⟩ := ih w hw
      have hroot := evalInt_eq_evalWrap_toInt_of_inRange n env e (subexprsInRange_root hsub)
      unfold checkedSNeg at hneg
      split at hneg
      · cases hneg
      · rename_i hov
        simp only [Option.some.injEq] at hneg
        subst hneg
        refine ⟨by rw [hwv]; rfl, hsub, ?_⟩
        show InSignedRange n (-(evalInt _ e))
        rw [hroot, ← hwv]
        exact (negOverflow_eq_false_iff w).1 (by simpa using hov)
  | add e₁ e₂ ih₁ ih₂ =>
      intro v h
      simp only [evalCheckedS, Option.bind_eq_some_iff] at h
      obtain ⟨w₁, hw₁, w₂, hw₂, hop⟩ := h
      obtain ⟨hv₁, hs₁⟩ := ih₁ w₁ hw₁
      obtain ⟨hv₂, hs₂⟩ := ih₂ w₂ hw₂
      have hr₁ := evalInt_eq_evalWrap_toInt_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toInt_of_inRange n env e₂ (subexprsInRange_root hs₂)
      unfold checkedSAdd at hop
      split at hop
      · cases hop
      · rename_i hov
        simp only [Option.some.injEq] at hop
        subst hop
        refine ⟨by rw [hv₁, hv₂]; rfl, hs₁, hs₂, ?_⟩
        show InSignedRange n (evalInt _ e₁ + evalInt _ e₂)
        rw [hr₁, hr₂, ← hv₁, ← hv₂]
        exact (saddOverflow_eq_false_iff w₁ w₂).1 (by simpa using hov)
  | sub e₁ e₂ ih₁ ih₂ =>
      intro v h
      simp only [evalCheckedS, Option.bind_eq_some_iff] at h
      obtain ⟨w₁, hw₁, w₂, hw₂, hop⟩ := h
      obtain ⟨hv₁, hs₁⟩ := ih₁ w₁ hw₁
      obtain ⟨hv₂, hs₂⟩ := ih₂ w₂ hw₂
      have hr₁ := evalInt_eq_evalWrap_toInt_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toInt_of_inRange n env e₂ (subexprsInRange_root hs₂)
      unfold checkedSSub at hop
      split at hop
      · cases hop
      · rename_i hov
        simp only [Option.some.injEq] at hop
        subst hop
        refine ⟨by rw [hv₁, hv₂]; rfl, hs₁, hs₂, ?_⟩
        show InSignedRange n (evalInt _ e₁ - evalInt _ e₂)
        rw [hr₁, hr₂, ← hv₁, ← hv₂]
        exact (ssubOverflow_eq_false_iff w₁ w₂).1 (by simpa using hov)
  | mul e₁ e₂ ih₁ ih₂ =>
      intro v h
      simp only [evalCheckedS, Option.bind_eq_some_iff] at h
      obtain ⟨w₁, hw₁, w₂, hw₂, hop⟩ := h
      obtain ⟨hv₁, hs₁⟩ := ih₁ w₁ hw₁
      obtain ⟨hv₂, hs₂⟩ := ih₂ w₂ hw₂
      have hr₁ := evalInt_eq_evalWrap_toInt_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toInt_of_inRange n env e₂ (subexprsInRange_root hs₂)
      unfold checkedSMul at hop
      split at hop
      · cases hop
      · rename_i hov
        simp only [Option.some.injEq] at hop
        subst hop
        refine ⟨by rw [hv₁, hv₂]; rfl, hs₁, hs₂, ?_⟩
        show InSignedRange n (evalInt _ e₁ * evalInt _ e₂)
        rw [hr₁, hr₂, ← hv₁, ← hv₂]
        exact (smulOverflow_eq_false_iff w₁ w₂).1 (by simpa using hov)

/-- Per-subexpression signed range bounds make checked signed evaluation succeed with the
    wrapping value. -/
theorem evalCheckedS_eq_some_of_subexprsInRange (n : Nat) (env : Nat → BitVec n) :
    ∀ (e : RingExpr),
      SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e →
      evalCheckedS n env e = some (evalWrap n env e) := by
  intro e
  induction e with
  | var i => intro _; rfl
  | lit k =>
      intro h
      have hk : InSignedRange n k := h
      simp only [evalCheckedS, hk, ↓reduceIte]
      rfl
  | neg e ih =>
      intro h
      obtain ⟨hs, hr⟩ := h
      have hroot := evalInt_eq_evalWrap_toInt_of_inRange n env e (subexprsInRange_root hs)
      have hr' : InSignedRange n (-(evalInt (fun i => (env i).toInt) e)) := hr
      rw [hroot] at hr'
      have hov := (negOverflow_eq_false_iff _).2 hr'
      simp only [evalCheckedS, ih hs, Option.bind_some, checkedSNeg, hov]
      rfl
  | add e₁ e₂ ih₁ ih₂ =>
      intro h
      obtain ⟨hs₁, hs₂, hr⟩ := h
      have hr₁ := evalInt_eq_evalWrap_toInt_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toInt_of_inRange n env e₂ (subexprsInRange_root hs₂)
      have hr' : InSignedRange n (evalInt (fun i => (env i).toInt) e₁ +
          evalInt (fun i => (env i).toInt) e₂) := hr
      rw [hr₁, hr₂] at hr'
      have hov := (saddOverflow_eq_false_iff _ _).2 hr'
      simp only [evalCheckedS, ih₁ hs₁, ih₂ hs₂, Option.bind_some, checkedSAdd, hov]
      rfl
  | sub e₁ e₂ ih₁ ih₂ =>
      intro h
      obtain ⟨hs₁, hs₂, hr⟩ := h
      have hr₁ := evalInt_eq_evalWrap_toInt_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toInt_of_inRange n env e₂ (subexprsInRange_root hs₂)
      have hr' : InSignedRange n (evalInt (fun i => (env i).toInt) e₁ -
          evalInt (fun i => (env i).toInt) e₂) := hr
      rw [hr₁, hr₂] at hr'
      have hov := (ssubOverflow_eq_false_iff _ _).2 hr'
      simp only [evalCheckedS, ih₁ hs₁, ih₂ hs₂, Option.bind_some, checkedSSub, hov]
      rfl
  | mul e₁ e₂ ih₁ ih₂ =>
      intro h
      obtain ⟨hs₁, hs₂, hr⟩ := h
      have hr₁ := evalInt_eq_evalWrap_toInt_of_inRange n env e₁ (subexprsInRange_root hs₁)
      have hr₂ := evalInt_eq_evalWrap_toInt_of_inRange n env e₂ (subexprsInRange_root hs₂)
      have hr' : InSignedRange n (evalInt (fun i => (env i).toInt) e₁ *
          evalInt (fun i => (env i).toInt) e₂) := hr
      rw [hr₁, hr₂] at hr'
      have hov := (smulOverflow_eq_false_iff _ _).2 hr'
      simp only [evalCheckedS, ih₁ hs₁, ih₂ hs₂, Option.bind_some, checkedSMul, hov]
      rfl

/-! ## Result 4 support: division guards and Euclidean division bounds -/

/-- Under `NonZeroDiv b` and `NoSDivOverflow a b`, the shared guard of the checked signed
    division/remainder operations is `false`. -/
theorem sdivGuard_eq_false {n : Nat} {a b : BitVec n} (hb : NonZeroDiv b)
    (hno : NoSDivOverflow a b) :
    (b == 0#n || (a == BitVec.intMin n && b == -1#n)) = false := by
  unfold NonZeroDiv at hb
  unfold NoSDivOverflow at hno
  by_cases h1 : a = BitVec.intMin n
  · have h2 : b ≠ -1#n := fun h2 => hno ⟨h1, h2⟩
    simp [hb, h2]
  · simp [hb, h1]

/-- `NoSDivOverflow a b` in the disjunctive form used by Lean core's `BitVec.toInt_sdiv_of_ne_or_ne`. -/
theorem ne_or_ne_of_noSDivOverflow {n : Nat} {a b : BitVec n} (hno : NoSDivOverflow a b) :
    a ≠ BitVec.intMin n ∨ b ≠ -1#n := by
  by_cases h1 : a = BitVec.intMin n
  · exact Or.inr (fun h2 => hno ⟨h1, h2⟩)
  · exact Or.inl h1

/-- A nonzero bitvector has a nonzero signed reading. -/
theorem toInt_ne_zero_of_nonZeroDiv {n : Nat} {b : BitVec n} (hb : NonZeroDiv b) : b.toInt ≠ 0 := by
  intro h
  apply hb
  apply BitVec.eq_of_toInt_eq
  rw [h, BitVec.toInt_zero]

/-- For `A ≤ 0` and `k ≤ C`, `A * C ≤ A * k`. -/
theorem mul_le_mul_of_nonpos_left' {A C k : Int} (hA : A ≤ 0) (hk : k ≤ C) : A * C ≤ A * k :=
  Int.mul_le_mul_of_nonpos_left hA hk

/-- Euclidean division `A / B` (Lean's `Int.ediv`) of in-range signed values stays in range,
    except for the excluded pair `(sMinVal n, -1)`. -/
theorem ediv_inSignedRange {n : Nat} {A B : Int} (hA : InSignedRange n A)
    (hB : InSignedRange n B) (hb0 : B ≠ 0) (hno : ¬ (A = sMinVal n ∧ B = -1)) :
    InSignedRange n (A / B) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact absurd ((inSignedRange_zero_iff B).1 hB) hb0
  have hmin : sMinVal n = -(2 : Int) ^ (n - 1) := by
    unfold sMinVal
    rw [BitVec.toInt_intMin_of_pos hn]
  rw [hmin] at hno
  rw [inSignedRange_iff_of_pos hn] at hA hB ⊢
  have hN : (1 : Int) ≤ (2 : Int) ^ (n - 1) := by
    have := Nat.one_le_two_pow (n := n - 1)
    exact_mod_cast this
  generalize hNdef : (2 : Int) ^ (n - 1) = N at *
  rcases Int.lt_or_gt_of_ne hb0 with hBneg | hBpos
  · -- negative divisor: `A / B = -(A / C)` with `C = -B > 0`
    have hC : 0 < -B := by omega
    have hdiv : A / B = -(A / -B) := by
      rw [← Int.ediv_neg, Int.neg_neg]
    rw [hdiv]
    rcases (show 0 ≤ A ∨ A < 0 by omega) with hA0 | hA0
    · have h1 : 0 ≤ A / -B := Int.ediv_nonneg hA0 (by omega)
      have h2 : A / -B ≤ A := Int.ediv_le_self _ hA0
      omega
    · have h1 : A / -B ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg (by omega) hC
      have h2 : A ≤ A / -B := by
        rw [Int.le_ediv_iff_mul_le hC]
        have := mul_le_mul_of_nonpos_left' (A := A) (C := -B) (k := 1) (by omega) (by omega)
        omega
      by_cases hAmin : A = -N
      · have hB1 : B ≠ -1 := fun h => hno ⟨hAmin, h⟩
        have h3 : A + 1 ≤ A / -B := by
          rw [Int.le_ediv_iff_mul_le hC]
          have := mul_le_mul_of_nonpos_left' (A := A) (C := -B) (k := 2) (by omega) (by omega)
          rw [Int.add_mul, Int.one_mul]
          omega
        omega
      · omega
  · -- positive divisor
    rcases (show 0 ≤ A ∨ A < 0 by omega) with hA0 | hA0
    · have h1 : 0 ≤ A / B := Int.ediv_nonneg hA0 (by omega)
      have h2 : A / B ≤ A := Int.ediv_le_self _ hA0
      omega
    · have h1 : A / B ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg (by omega) hBpos
      have h2 : A ≤ A / B := by
        rw [Int.le_ediv_iff_mul_le hBpos]
        have := mul_le_mul_of_nonpos_left' (A := A) (C := B) (k := 1) (by omega) (by omega)
        omega
      omega

/-- Euclidean remainder `A % B` (Lean's `Int.emod`) by an in-range nonzero signed divisor
    stays in range. -/
theorem emod_inSignedRange {n : Nat} {A B : Int} (hB : InSignedRange n B) (hb0 : B ≠ 0) :
    InSignedRange n (A % B) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact absurd ((inSignedRange_zero_iff B).1 hB) hb0
  rw [inSignedRange_iff_of_pos hn] at hB ⊢
  have h1 := Int.emod_nonneg A hb0
  have h2 := Int.emod_lt A hb0
  omega

/-- Signed readings of bitvectors excluded by `NoSDivOverflow`. -/
theorem not_toInt_sMin_negOne_of_noSDivOverflow {n : Nat} {a b : BitVec n} (hn : 0 < n)
    (hno : NoSDivOverflow a b) : ¬ (a.toInt = sMinVal n ∧ b.toInt = -1) := by
  rintro ⟨ha, hb⟩
  apply hno
  constructor
  · exact BitVec.eq_of_toInt_eq ha
  · apply BitVec.eq_of_toInt_eq
    rw [hb, BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes]
    simp [hn]

/-- `Rust`'s `div_euclid` on bitvectors (`sdivEuclid`) computes `Int.ediv` of the signed
    readings whenever the checked guard passes. -/
theorem toInt_sdivEuclid {n : Nat} (a b : BitVec n) (hb : NonZeroDiv b)
    (hno : NoSDivOverflow a b) :
    (sdivEuclid a b).toInt = a.toInt / b.toInt := by
  have hn : 0 < n := posWidth_of_nonZeroDiv hb
  have hsdiv : (a.sdiv b).toInt = a.toInt.tdiv b.toInt :=
    BitVec.toInt_sdiv_of_ne_or_ne a b (ne_or_ne_of_noSDivOverflow hno)
  have hsrem : (a.srem b).toInt = a.toInt.tmod b.toInt := BitVec.toInt_srem a b
  have hB0 : b.toInt ≠ 0 := toInt_ne_zero_of_nonZeroDiv hb
  have hE : InSignedRange n (a.toInt / b.toInt) :=
    ediv_inSignedRange (inSignedRange_toInt a) (inSignedRange_toInt b) hB0
      (not_toInt_sMin_negOne_of_noSDivOverflow hn hno)
  have hT := Int.tdiv_eq_ediv (a := a.toInt) (b := b.toInt)
  have hR := Int.tmod_eq_emod (a := a.toInt) (b := b.toInt)
  unfold sdivEuclid
  simp only [BitVec.slt_eq_decide, hsrem, BitVec.toInt_zero]
  by_cases hc : 0 ≤ a.toInt ∨ b.toInt ∣ a.toInt
  · simp only [hc, ↓reduceIte] at hT hR
    have hM := Int.emod_nonneg a.toInt hB0
    have hRnn : ¬ (a.toInt.tmod b.toInt < 0) := by omega
    simp only [hRnn, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [hsdiv, hT, Int.add_zero]
  · simp only [hc, ↓reduceIte] at hT hR
    have hndvd : ¬ b.toInt ∣ a.toInt := fun h => hc (Or.inr h)
    have hM0 : a.toInt % b.toInt ≠ 0 := fun h => hndvd (Int.dvd_iff_emod_eq_zero.2 h)
    have hM := Int.emod_nonneg a.toInt hB0
    have hMlt := Int.emod_lt a.toInt hB0
    have hRneg : a.toInt.tmod b.toInt < 0 := by omega
    simp only [hRneg, decide_true, ↓reduceIte]
    rcases Int.lt_or_gt_of_ne hB0 with hBneg | hBpos
    · have hnotpos : ¬ (0 < b.toInt) := by omega
      simp only [hnotpos, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [Int.sign_eq_neg_one_of_neg hBneg] at hT
      rw [BitVec.toInt_add, hsdiv, BitVec.toInt_ofNat', Int.add_bmod_bmod]
      have : a.toInt.tdiv b.toInt + ((1 : Nat) : Int) = a.toInt / b.toInt := by omega
      rw [this, bmod_eq_self_of_inSignedRange hE]
    · simp only [hBpos, decide_true, ↓reduceIte]
      rw [Int.sign_eq_one_of_pos hBpos] at hT
      rw [BitVec.toInt_sub, hsdiv, BitVec.toInt_ofNat', Int.sub_bmod_bmod]
      have : a.toInt.tdiv b.toInt - ((1 : Nat) : Int) = a.toInt / b.toInt := by omega
      rw [this, bmod_eq_self_of_inSignedRange hE]

/-- `Rust`'s `rem_euclid` on bitvectors (`sremEuclid`) computes `Int.emod` of the signed
    readings for every nonzero divisor. -/
theorem toInt_sremEuclid {n : Nat} (a b : BitVec n) (hb : NonZeroDiv b) :
    (sremEuclid a b).toInt = a.toInt % b.toInt := by
  have hsrem : (a.srem b).toInt = a.toInt.tmod b.toInt := BitVec.toInt_srem a b
  have hB0 : b.toInt ≠ 0 := toInt_ne_zero_of_nonZeroDiv hb
  have hM : InSignedRange n (a.toInt % b.toInt) := emod_inSignedRange (inSignedRange_toInt b) hB0
  have hR := Int.tmod_eq_emod (a := a.toInt) (b := b.toInt)
  unfold sremEuclid
  simp only [BitVec.slt_eq_decide, hsrem, BitVec.toInt_zero]
  by_cases hc : 0 ≤ a.toInt ∨ b.toInt ∣ a.toInt
  · simp only [hc, ↓reduceIte] at hR
    have hMnn := Int.emod_nonneg a.toInt hB0
    have hRnn : ¬ (a.toInt.tmod b.toInt < 0) := by omega
    simp only [hRnn, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [hsrem, hR]
    simp
  · simp only [hc, ↓reduceIte] at hR
    have hndvd : ¬ b.toInt ∣ a.toInt := fun h => hc (Or.inr h)
    have hM0 : a.toInt % b.toInt ≠ 0 := fun h => hndvd (Int.dvd_iff_emod_eq_zero.2 h)
    have hMnn := Int.emod_nonneg a.toInt hB0
    have hMlt := Int.emod_lt a.toInt hB0
    have hRneg : a.toInt.tmod b.toInt < 0 := by omega
    simp only [hRneg, decide_true, ↓reduceIte]
    rw [BitVec.toInt_add, hsrem, BitVec.abs_eq]
    rcases Int.lt_or_gt_of_ne hB0 with hBneg | hBpos
    · have hmsb : b.msb = true := by rw [BitVec.msb_eq_toInt]; simp [hBneg]
      simp only [hmsb, ↓reduceIte]
      rw [BitVec.toInt_neg, Int.add_bmod_bmod]
      have : a.toInt.tmod b.toInt + -b.toInt = a.toInt % b.toInt := by omega
      rw [this, bmod_eq_self_of_inSignedRange hM]
    · have hmsb : b.msb = false := by rw [BitVec.msb_eq_toInt]; simp; omega
      simp only [hmsb, Bool.false_eq_true, ↓reduceIte]
      have : a.toInt.tmod b.toInt + b.toInt = a.toInt % b.toInt := by omega
      rw [this, bmod_eq_self_of_inSignedRange hM]

end Toy.MachInt
