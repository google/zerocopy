prelude
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Tactics

/-!
# F2-Linear and F2-Bilinear GMP Unit-Basis Symbolic Evaluators for SIMD & Carryless Multiply

Self-contained `prelude` + `Init.*`-only Lean `v4.34.1` mechanization proving:
1. `checkF2Linear1_sound` / `checkF2Linear2_sound`: Universal equivalence over `BitVec w`
   (`∀ x, L1 x = L2 x` and `∀ x y, L1 x y = L2 x y`) from `w` (resp. `2w`) GMP unit-basis checks,
   covering `vpshufb` constant byte permutes, split-nibble GF(2^8) SIMD table lookups vs
   polynomial multiplication (`0x11b`), and constant-polynomial `pclmulqdq` CRC/GHASH folding.
2. `checkF2Bilinear_sound`: Universal 2-variable bilinear equivalence (`∀ x y : BitVec 64,
   B1 x y = B2 x y`) as a 2-pass corollary of `checkF2Linear1_sound`, discharging 64x64 -> 128-bit
   `pclmulqdq` Karatsuba vs schoolbook carryless multiplication where CDCL SAT bit-blasting stalls.
-/

namespace F2SimdCert

/-- Structure witnessing that `f : BitVec wIn → BitVec wOut` is linear over F_2. -/
structure IsF2Linear1 {wIn wOut : Nat} (f : BitVec wIn → BitVec wOut) : Prop where
  map_zero : f (0#wIn) = 0#wOut
  map_xor  : ∀ a b : BitVec wIn, f (a ^^^ b) = f a ^^^ f b

/-- Structure witnessing that `f : BitVec w1 → BitVec w2 → BitVec wOut` is jointly F_2-linear. -/
structure IsF2Linear2 {w1 w2 wOut : Nat} (f : BitVec w1 → BitVec w2 → BitVec wOut) : Prop where
  map_zero : f (0#w1) (0#w2) = 0#wOut
  map_xor  : ∀ a1 a2 : BitVec w1, ∀ b1 b2 : BitVec w2,
    f (a1 ^^^ a2) (b1 ^^^ b2) = f a1 b1 ^^^ f a2 b2

/-- Structure witnessing that `B : BitVec w1 → BitVec w2 → BitVec wOut` is F_2-bilinear
    (e.g., 64x64 -> 128-bit `pclmulqdq` carryless polynomial multiplication). -/
structure IsF2Bilinear {w1 w2 wOut : Nat} (B : BitVec w1 → BitVec w2 → BitVec wOut) : Prop where
  zero_left  : ∀ y : BitVec w2, B (0#w1) y = 0#wOut
  xor_left   : ∀ a1 a2 : BitVec w1, ∀ y : BitVec w2, B (a1 ^^^ a2) y = B a1 y ^^^ B a2 y
  zero_right : ∀ x : BitVec w1, B x (0#w2) = 0#wOut
  xor_right  : ∀ x : BitVec w1, ∀ b1 b2 : BitVec w2, B x (b1 ^^^ b2) = B x b1 ^^^ B x b2

/-- Reconstructs the lowest `n` bits of `x : BitVec w` as an F_2 sum of unit basis vectors `1#w <<< k`. -/
def bvBasisPrefix {w : Nat} (x : BitVec w) : Nat → BitVec w
  | 0 => 0#w
  | Nat.succ k =>
    let prev := bvBasisPrefix x k
    match x.getLsbD k with
    | false => prev
    | true  => prev ^^^ (1#w <<< k)

theorem getLsbD_one_shiftLeft {w k i : Nat} (hi : i < w) :
    (1#w <<< k).getLsbD i = decide (i = k) := by
  rw [BitVec.getLsbD_shiftLeft]
  simp only [hi, decide_true, Bool.true_and]
  cases hlt : decide (i < k) with
  | true =>
    rw [Bool.not_true, Bool.false_and]
    have hne : ¬(i = k) := by
      rw [decide_eq_true_eq] at hlt
      omega
    exact (decide_eq_false hne).symm
  | false =>
    rw [Bool.not_false, Bool.true_and, BitVec.getLsbD_one]
    have hle : k ≤ i := by
      rw [decide_eq_false_iff_not] at hlt
      omega
    have hw : 0 < w := by omega
    simp only [hw, decide_true, Bool.true_and]
    cases hik : decide (i = k) with
    | true =>
      rw [decide_eq_true_eq] at hik
      subst hik
      simp
    | false =>
      rw [decide_eq_false_iff_not] at hik
      exact decide_eq_false (by omega)

theorem bvBasisPrefix_getLsbD {w : Nat} (x : BitVec w) :
    ∀ (n i : Nat), i < w →
      (bvBasisPrefix x n).getLsbD i = (decide (i < n) && x.getLsbD i)
  | 0, i, _ => by
    simp [bvBasisPrefix]
  | Nat.succ k, i, hi => by
    unfold bvBasisPrefix
    cases hxk : x.getLsbD k with
    | false =>
      dsimp only
      rw [bvBasisPrefix_getLsbD x k i hi]
      cases hik : decide (i = k) with
      | true =>
        rw [decide_eq_true_eq] at hik
        subst hik
        simp [hxk]
      | false =>
        rw [decide_eq_false_iff_not] at hik
        have hlt_eq : decide (i < Nat.succ k) = decide (i < k) := by
          cases h1 : decide (i < k) with
          | true =>
            rw [decide_eq_true_eq] at h1
            exact decide_eq_true (Nat.lt_succ_of_lt h1)
          | false =>
            rw [decide_eq_false_iff_not] at h1
            apply decide_eq_false
            intro h2
            cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h2) with
            | inl hlt => exact h1 hlt
            | inr heq => exact hik heq
        rw [hlt_eq]
    | true =>
      dsimp only
      rw [BitVec.getLsbD_xor, bvBasisPrefix_getLsbD x k i hi, getLsbD_one_shiftLeft hi]
      cases hik : decide (i = k) with
      | true =>
        rw [decide_eq_true_eq] at hik
        subst hik
        simp [hxk]
      | false =>
        rw [decide_eq_false_iff_not] at hik
        have hlt_eq : decide (i < Nat.succ k) = decide (i < k) := by
          cases h1 : decide (i < k) with
          | true =>
            rw [decide_eq_true_eq] at h1
            exact decide_eq_true (Nat.lt_succ_of_lt h1)
          | false =>
            rw [decide_eq_false_iff_not] at h1
            apply decide_eq_false
            intro h2
            cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h2) with
            | inl hlt => exact h1 hlt
            | inr heq => exact hik heq
        simp [hlt_eq]

theorem bvBasisPrefix_full {w : Nat} (x : BitVec w) : bvBasisPrefix x w = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bvBasisPrefix_getLsbD x w i hi]
  simp [hi]

/-- Checks `f (1#wIn <<< k) == g (1#wIn <<< k)` for all `k < n` in C++ GMP. -/
def checkBasis1Aux {wIn wOut : Nat} (f g : BitVec wIn → BitVec wOut) : Nat → Bool
  | 0 => true
  | Nat.succ k =>
    match checkBasis1Aux f g k with
    | false => false
    | true  => f (1#wIn <<< k) == g (1#wIn <<< k)

theorem checkBasis1Aux_prefix_eq {wIn wOut : Nat}
    {f g : BitVec wIn → BitVec wOut}
    (hf : IsF2Linear1 f) (hg : IsF2Linear1 g) (x : BitVec wIn) :
    ∀ n : Nat, checkBasis1Aux f g n = true → f (bvBasisPrefix x n) = g (bvBasisPrefix x n)
  | 0, _ => by
    unfold bvBasisPrefix
    rw [hf.map_zero, hg.map_zero]
  | Nat.succ k, hchk => by
    unfold checkBasis1Aux at hchk
    cases hprev : checkBasis1Aux f g k with
    | false =>
      rw [hprev] at hchk
      contradiction
    | true =>
      rw [hprev] at hchk
      have ih := checkBasis1Aux_prefix_eq hf hg x k hprev
      have hk : f (1#wIn <<< k) = g (1#wIn <<< k) := eq_of_beq hchk
      unfold bvBasisPrefix
      cases x.getLsbD k with
      | false => exact ih
      | true =>
        dsimp only
        rw [hf.map_xor, hg.map_xor, ih, hk]

def checkF2Linear1 {wIn wOut : Nat} (f g : BitVec wIn → BitVec wOut) : Bool :=
  checkBasis1Aux f g wIn

theorem checkF2Linear1_sound {wIn wOut : Nat}
    {f g : BitVec wIn → BitVec wOut}
    (hf : IsF2Linear1 f) (hg : IsF2Linear1 g)
    (hcert : checkF2Linear1 f g = true) :
    ∀ x : BitVec wIn, f x = g x := by
  intro x
  rw [← bvBasisPrefix_full x]
  exact checkBasis1Aux_prefix_eq hf hg x wIn hcert

/-- Two-input F_2-linear checker (`w1 + w2` unit basis checks in GMP). -/
def checkF2Linear2 {w1 w2 wOut : Nat} (f g : BitVec w1 → BitVec w2 → BitVec wOut) : Bool :=
  checkF2Linear1 (fun x => f x (0#w2)) (fun x => g x (0#w2)) &&
  checkF2Linear1 (fun y => f (0#w1) y) (fun y => g (0#w1) y)

theorem checkF2Linear2_sound {w1 w2 wOut : Nat}
    {f g : BitVec w1 → BitVec w2 → BitVec wOut}
    (hf : IsF2Linear2 f) (hg : IsF2Linear2 g)
    (hcert : checkF2Linear2 f g = true) :
    ∀ (x : BitVec w1) (y : BitVec w2), f x y = g x y := by
  intro x y
  unfold checkF2Linear2 at hcert
  cases h1 : checkF2Linear1 (fun a => f a (0#w2)) (fun a => g a (0#w2)) with
  | false => rw [h1] at hcert; contradiction
  | true =>
    rw [h1, Bool.true_and] at hcert
    have hfL : IsF2Linear1 (fun a => f a (0#w2)) := {
      map_zero := hf.map_zero
      map_xor := fun a1 a2 => by
        have h := hf.map_xor a1 a2 (0#w2) (0#w2)
        simpa using h
    }
    have hgL : IsF2Linear1 (fun a => g a (0#w2)) := {
      map_zero := hg.map_zero
      map_xor := fun a1 a2 => by
        have h := hg.map_xor a1 a2 (0#w2) (0#w2)
        simpa using h
    }
    have hfR : IsF2Linear1 (fun b => f (0#w1) b) := {
      map_zero := hf.map_zero
      map_xor := fun b1 b2 => by
        have h := hf.map_xor (0#w1) (0#w1) b1 b2
        simpa using h
    }
    have hgR : IsF2Linear1 (fun b => g (0#w1) b) := {
      map_zero := hg.map_zero
      map_xor := fun b1 b2 => by
        have h := hg.map_xor (0#w1) (0#w1) b1 b2
        simpa using h
    }
    have eqX := checkF2Linear1_sound hfL hgL h1 x
    have eqY := checkF2Linear1_sound hfR hgR hcert y
    have splitF : f x y = f x (0#w2) ^^^ f (0#w1) y := by
      have h := hf.map_xor x (0#w1) (0#w2) y
      simpa using h
    have splitG : g x y = g x (0#w2) ^^^ g (0#w1) y := by
      have h := hg.map_xor x (0#w1) (0#w2) y
      simpa using h
    rw [splitF, splitG, eqX, eqY]

/-- Two-variable F_2-bilinear basis checker (`w1 * w2` unit basis checks in GMP). -/
def checkBilinearRows {w1 w2 wOut : Nat} (B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut) : Nat → Bool
  | 0 => true
  | Nat.succ i =>
    match checkBilinearRows B1 B2 i with
    | false => false
    | true  => checkF2Linear1 (fun y => B1 (1#w1 <<< i) y) (fun y => B2 (1#w1 <<< i) y)

def checkF2Bilinear {w1 w2 wOut : Nat} (B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut) : Bool :=
  checkBilinearRows B1 B2 w1

theorem checkBilinearRows_sound_aux {w1 w2 wOut : Nat}
    {B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut}
    (h1 : IsF2Bilinear B1) (h2 : IsF2Bilinear B2) (y : BitVec w2) :
    ∀ n : Nat, checkBilinearRows B1 B2 n = true → checkBasis1Aux (fun x => B1 x y) (fun x => B2 x y) n = true
  | 0, _ => rfl
  | Nat.succ i, hchk => by
    unfold checkBilinearRows at hchk
    cases hp : checkBilinearRows B1 B2 i with
    | false => rw [hp] at hchk; contradiction
    | true =>
      rw [hp] at hchk
      have ih := checkBilinearRows_sound_aux h1 h2 y i hp
      have hB1R : IsF2Linear1 (fun b => B1 (1#w1 <<< i) b) := ⟨h1.zero_right _, h1.xor_right _⟩
      have hB2R : IsF2Linear1 (fun b => B2 (1#w1 <<< i) b) := ⟨h2.zero_right _, h2.xor_right _⟩
      have rowEq := checkF2Linear1_sound hB1R hB2R hchk y
      unfold checkBasis1Aux
      rw [ih]
      exact beq_iff_eq.mpr rowEq

theorem checkF2Bilinear_sound {w1 w2 wOut : Nat}
    {B1 B2 : BitVec w1 → BitVec w2 → BitVec wOut}
    (h1 : IsF2Bilinear B1) (h2 : IsF2Bilinear B2)
    (hcert : checkF2Bilinear B1 B2 = true) :
    ∀ (x : BitVec w1) (y : BitVec w2), B1 x y = B2 x y := by
  intro x y
  have hL1 : IsF2Linear1 (fun a => B1 a y) := ⟨h1.zero_left y, fun a1 a2 => h1.xor_left a1 a2 y⟩
  have hL2 : IsF2Linear1 (fun a => B2 a y) := ⟨h2.zero_left y, fun a1 a2 => h2.xor_left a1 a2 y⟩
  apply checkF2Linear1_sound hL1 hL2 _ x
  exact checkBilinearRows_sound_aux h1 h2 y w1 hcert

-- ============================================================================
-- Compositional F_2-Linear Circuit Combinators + Automatic Linearity Proofs
-- ============================================================================

inductive F2Circuit : Nat → Nat → Type where
  | id       {w : Nat} : F2Circuit w w
  | zero     {wIn wOut : Nat} : F2Circuit wIn wOut
  | xor      {wIn wOut : Nat} : F2Circuit wIn wOut → F2Circuit wIn wOut → F2Circuit wIn wOut
  | andConst {wIn wOut : Nat} : F2Circuit wIn wOut → BitVec wOut → F2Circuit wIn wOut
  | shlConst {wIn wOut : Nat} : F2Circuit wIn wOut → Nat → F2Circuit wIn wOut
  | lshrConst {wIn wOut : Nat} : F2Circuit wIn wOut → Nat → F2Circuit wIn wOut
  | extract  {wIn wMid : Nat} (lo len : Nat) : F2Circuit wIn wMid → F2Circuit wIn len
  | concat   {wIn wHi wLo : Nat} : F2Circuit wIn wHi → F2Circuit wIn wLo → F2Circuit wIn (wHi + wLo)
  | comp     {w1 w2 w3 : Nat} : F2Circuit w2 w3 → F2Circuit w1 w2 → F2Circuit w1 w3

def F2Circuit.eval {wIn wOut : Nat} (c : F2Circuit wIn wOut) (x : BitVec wIn) : BitVec wOut :=
  match c with
  | .id => x
  | .zero => 0#wOut
  | .xor c1 c2 => c1.eval x ^^^ c2.eval x
  | .andConst c1 mask => c1.eval x &&& mask
  | .shlConst c1 k => c1.eval x <<< k
  | .lshrConst c1 k => c1.eval x >>> k
  | .extract lo len c1 => BitVec.extractLsb' lo len (c1.eval x)
  | .concat cHi cLo => BitVec.append (cHi.eval x) (cLo.eval x)
  | .comp c2 c1 => c2.eval (c1.eval x)
termination_by structural c

theorem bitvec_and_xor_distrib_right {w : Nat} (a b m : BitVec w) :
    (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases m.getLsbD i <;> rfl

theorem bitvec_shl_xor_distrib {w : Nat} (a b : BitVec w) (k : Nat) :
    (a ^^^ b) <<< k = (a <<< k) ^^^ (b <<< k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]
  cases (!decide (i < k)) <;> rfl

theorem bitvec_lshr_xor_distrib {w : Nat} (a b : BitVec w) (k : Nat) :
    (a ^^^ b) >>> k = (a >>> k) ^^^ (b >>> k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]

theorem bitvec_extract_xor_distrib {w : Nat} (lo len : Nat) (a b : BitVec w) :
    BitVec.extractLsb' lo len (a ^^^ b) =
      BitVec.extractLsb' lo len a ^^^ BitVec.extractLsb' lo len b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, BitVec.getLsbD_xor]

theorem bitvec_append_xor_distrib {wHi wLo : Nat} (a1 a2 : BitVec wHi) (b1 b2 : BitVec wLo) :
    BitVec.append (a1 ^^^ a2) (b1 ^^^ b2) =
      BitVec.append a1 b1 ^^^ BitVec.append a2 b2 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.append_eq, BitVec.append_eq, BitVec.append_eq]
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor]
  split <;> simp

theorem bitvec_xor_four_rearrange {w : Nat} (p q r s : BitVec w) :
    (p ^^^ q) ^^^ (r ^^^ s) = (p ^^^ r) ^^^ (q ^^^ s) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases p.getLsbD i <;> cases q.getLsbD i <;> cases r.getLsbD i <;> cases s.getLsbD i <;> rfl

theorem bitvec_xor_six_rearrange {w : Nat} (a1 a2 b1 b2 c1 c2 : BitVec w) :
    (a1 ^^^ a2) ^^^ (b1 ^^^ b2) ^^^ (c1 ^^^ c2) =
      (a1 ^^^ b1 ^^^ c1) ^^^ (a2 ^^^ b2 ^^^ c2) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases a1.getLsbD i <;> cases a2.getLsbD i <;>
  cases b1.getLsbD i <;> cases b2.getLsbD i <;>
  cases c1.getLsbD i <;> cases c2.getLsbD i <;> rfl

theorem F2Circuit.eval_isLinear : ∀ (c : F2Circuit wIn wOut), IsF2Linear1 c.eval
  | .id => {
      map_zero := rfl
      map_xor := fun _ _ => rfl
    }
  | .zero => {
      map_zero := rfl
      map_xor := fun _ _ => by simp [F2Circuit.eval]
    }
  | .xor c1 c2 =>
    let h1 := c1.eval_isLinear
    let h2 := c2.eval_isLinear
    { map_zero := by simp [F2Circuit.eval, h1.map_zero, h2.map_zero]
      map_xor := fun a b => by
        simp only [F2Circuit.eval, h1.map_xor, h2.map_xor]
        exact bitvec_xor_four_rearrange _ _ _ _ }
  | .andConst c m =>
    let h := c.eval_isLinear
    { map_zero := by simp [F2Circuit.eval, h.map_zero]
      map_xor := fun a b => by
        simp only [F2Circuit.eval, h.map_xor, bitvec_and_xor_distrib_right] }
  | .shlConst c k =>
    let h := c.eval_isLinear
    { map_zero := by simp [F2Circuit.eval, h.map_zero]
      map_xor := fun a b => by
        simp only [F2Circuit.eval, h.map_xor, bitvec_shl_xor_distrib] }
  | .lshrConst c k =>
    let h := c.eval_isLinear
    { map_zero := by simp [F2Circuit.eval, h.map_zero]
      map_xor := fun a b => by
        simp only [F2Circuit.eval, h.map_xor, bitvec_lshr_xor_distrib] }
  | .extract lo len c =>
    let h := c.eval_isLinear
    { map_zero := by simp [F2Circuit.eval, h.map_zero]
      map_xor := fun a b => by
        simp only [F2Circuit.eval, h.map_xor, bitvec_extract_xor_distrib] }
  | .concat cHi cLo =>
    let hHi := cHi.eval_isLinear
    let hLo := cLo.eval_isLinear
    { map_zero := by
        simp only [F2Circuit.eval, hHi.map_zero, hLo.map_zero]
        apply BitVec.eq_of_getLsbD_eq
        intro i _
        rw [BitVec.append_eq, BitVec.getLsbD_append]
        split <;> simp
      map_xor := fun a b => by
        simp only [F2Circuit.eval, hHi.map_xor, hLo.map_xor, bitvec_append_xor_distrib] }
  | .comp c2 c1 =>
    let h1 := c1.eval_isLinear
    let h2 := c2.eval_isLinear
    { map_zero := by simp [F2Circuit.eval, h1.map_zero, h2.map_zero]
      map_xor := fun a b => by simp [F2Circuit.eval, h1.map_xor, h2.map_xor] }

theorem checkF2CircuitEq_sound {wIn wOut : Nat} (c1 c2 : F2Circuit wIn wOut)
    (hcert : checkF2Linear1 c1.eval c2.eval = true) :
    ∀ x : BitVec wIn, c1.eval x = c2.eval x :=
  checkF2Linear1_sound c1.eval_isLinear c2.eval_isLinear hcert

-- ============================================================================
-- Carryless Multiply (`pclmulqdq`) Schoolbook & Karatsuba + Bilinearity Proofs!
-- ============================================================================

def clmulAux {wOut : Nat} (x : BitVec wOut) {wY : Nat} (y : BitVec wY) : Nat → BitVec wOut
  | 0 => 0#wOut
  | Nat.succ i =>
    let prev := clmulAux x y i
    match y.getLsbD i with
    | false => prev
    | true  => prev ^^^ (x <<< i)

/-- Arbitrary-width carryless polynomial multiplication (`pclmulqdq` at `w = 64`, `wOut = 128`). -/
def clmul (w wOut : Nat) (x y : BitVec w) : BitVec wOut :=
  clmulAux (x.zeroExtend wOut) y w

theorem bitvec_zeroExtend_zero {w wOut : Nat} : (0#w).zeroExtend wOut = 0#wOut := by
  simp

theorem bitvec_zeroExtend_xor {w wOut : Nat} (a b : BitVec w) :
    (a ^^^ b).zeroExtend wOut = a.zeroExtend wOut ^^^ b.zeroExtend wOut := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.zeroExtend, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor]
  cases decide (i < wOut) <;> rfl

theorem clmulAux_zero_left {wOut wY : Nat} (y : BitVec wY) :
    ∀ n : Nat, clmulAux (0#wOut) y n = 0#wOut
  | 0 => rfl
  | Nat.succ i => by
    unfold clmulAux
    rw [clmulAux_zero_left y i]
    cases y.getLsbD i <;> simp

theorem clmulAux_xor_left {wOut wY : Nat} (x1 x2 : BitVec wOut) (y : BitVec wY) :
    ∀ n : Nat, clmulAux (x1 ^^^ x2) y n = clmulAux x1 y n ^^^ clmulAux x2 y n
  | 0 => by simp [clmulAux]
  | Nat.succ i => by
    unfold clmulAux
    rw [clmulAux_xor_left x1 x2 y i]
    cases y.getLsbD i with
    | false => rfl
    | true =>
      dsimp only
      rw [bitvec_shl_xor_distrib]
      exact bitvec_xor_four_rearrange _ _ _ _

theorem clmulAux_zero_right {wOut wY : Nat} (x : BitVec wOut) :
    ∀ n : Nat, clmulAux x (0#wY) n = 0#wOut
  | 0 => rfl
  | Nat.succ i => by
    unfold clmulAux
    simp [clmulAux_zero_right x i]

theorem clmulAux_xor_right {wOut wY : Nat} (x : BitVec wOut) (y1 y2 : BitVec wY) :
    ∀ n : Nat, clmulAux x (y1 ^^^ y2) n = clmulAux x y1 n ^^^ clmulAux x y2 n
  | 0 => by simp [clmulAux]
  | Nat.succ i => by
    unfold clmulAux
    rw [clmulAux_xor_right x y1 y2 i, BitVec.getLsbD_xor]
    cases y1.getLsbD i <;> cases y2.getLsbD i
    · rfl
    · change clmulAux x y1 i ^^^ clmulAux x y2 i ^^^ x <<< i =
             clmulAux x y1 i ^^^ (clmulAux x y2 i ^^^ x <<< i)
      exact BitVec.xor_assoc _ _ _
    · change clmulAux x y1 i ^^^ clmulAux x y2 i ^^^ x <<< i =
             (clmulAux x y1 i ^^^ x <<< i) ^^^ clmulAux x y2 i
      apply BitVec.eq_of_getLsbD_eq
      intro k _
      simp only [BitVec.getLsbD_xor]
      cases (clmulAux x y1 i).getLsbD k <;> cases (clmulAux x y2 i).getLsbD k <;> cases (x <<< i).getLsbD k <;> rfl
    · change clmulAux x y1 i ^^^ clmulAux x y2 i =
             (clmulAux x y1 i ^^^ x <<< i) ^^^ (clmulAux x y2 i ^^^ x <<< i)
      apply BitVec.eq_of_getLsbD_eq
      intro k _
      simp only [BitVec.getLsbD_xor]
      cases (clmulAux x y1 i).getLsbD k <;> cases (clmulAux x y2 i).getLsbD k <;> cases (x <<< i).getLsbD k <;> rfl

theorem clmul_isBilinear (w wOut : Nat) : IsF2Bilinear (clmul w wOut) where
  zero_left := fun y => by
    unfold clmul
    rw [bitvec_zeroExtend_zero]
    exact clmulAux_zero_left y w
  xor_left := fun a1 a2 y => by
    unfold clmul
    rw [bitvec_zeroExtend_xor]
    exact clmulAux_xor_left _ _ y w
  zero_right := fun x => by
    unfold clmul
    exact clmulAux_zero_right _ w
  xor_right := fun x b1 b2 => by
    unfold clmul
    exact clmulAux_xor_right _ b1 b2 w

/-- Karatsuba 64x64 -> 128-bit carryless multiplication using three 32x32 -> 64-bit `clmul` calls! -/
def clmulKaratsuba64 (x y : BitVec 64) : BitVec 128 :=
  let xLo : BitVec 32 := BitVec.extractLsb' 0 32 x
  let xHi : BitVec 32 := BitVec.extractLsb' 32 32 x
  let yLo : BitVec 32 := BitVec.extractLsb' 0 32 y
  let yHi : BitVec 32 := BitVec.extractLsb' 32 32 y
  let z0 : BitVec 128 := (clmul 32 64 xLo yLo).zeroExtend 128
  let z2 : BitVec 128 := ((clmul 32 64 xHi yHi).zeroExtend 128) <<< 64
  let zMid : BitVec 128 := (clmul 32 64 (xLo ^^^ xHi) (yLo ^^^ yHi)).zeroExtend 128
  let z1 : BitVec 128 := (zMid ^^^ z0 ^^^ (clmul 32 64 xHi yHi).zeroExtend 128) <<< 32
  z0 ^^^ z1 ^^^ z2

private theorem karatsuba_xor_rearrange {w : Nat}
    (z0a z0b zHa zHb zMa zMb : BitVec w) :
    (z0a ^^^ z0b) ^^^
    (((zMa ^^^ zMb) ^^^ (z0a ^^^ z0b) ^^^ (zHa ^^^ zHb)) <<< 32) ^^^
    ((zHa ^^^ zHb) <<< 64) =
    (z0a ^^^ ((zMa ^^^ z0a ^^^ zHa) <<< 32) ^^^ (zHa <<< 64)) ^^^
    (z0b ^^^ ((zMb ^^^ z0b ^^^ zHb) <<< 32) ^^^ (zHb <<< 64)) := by
  rw [bitvec_xor_six_rearrange zMa zMb z0a z0b zHa zHb,
      bitvec_shl_xor_distrib _ _ 32, bitvec_shl_xor_distrib _ _ 64]
  exact bitvec_xor_six_rearrange _ _ _ _ _ _

theorem clmulKaratsuba64_isBilinear : IsF2Bilinear clmulKaratsuba64 where
  zero_left := fun y => by
    unfold clmulKaratsuba64
    have hb := clmul_isBilinear 32 64
    simp [hb.zero_left]
  xor_left := fun a1 a2 y => by
    unfold clmulKaratsuba64
    dsimp only
    have hb := clmul_isBilinear 32 64
    rw [bitvec_extract_xor_distrib 0 32 a1 a2, bitvec_extract_xor_distrib 32 32 a1 a2]
    rw [bitvec_xor_four_rearrange (BitVec.extractLsb' 0 32 a1) (BitVec.extractLsb' 0 32 a2)
          (BitVec.extractLsb' 32 32 a1) (BitVec.extractLsb' 32 32 a2)]
    have h0 := hb.xor_left (BitVec.extractLsb' 0 32 a1) (BitVec.extractLsb' 0 32 a2)
                 (BitVec.extractLsb' 0 32 y)
    have h2 := hb.xor_left (BitVec.extractLsb' 32 32 a1) (BitVec.extractLsb' 32 32 a2)
                 (BitVec.extractLsb' 32 32 y)
    have hM := hb.xor_left (BitVec.extractLsb' 0 32 a1 ^^^ BitVec.extractLsb' 32 32 a1)
                 (BitVec.extractLsb' 0 32 a2 ^^^ BitVec.extractLsb' 32 32 a2)
                 (BitVec.extractLsb' 0 32 y ^^^ BitVec.extractLsb' 32 32 y)
    rw [h0, h2, hM, bitvec_zeroExtend_xor, bitvec_zeroExtend_xor, bitvec_zeroExtend_xor]
    exact karatsuba_xor_rearrange _ _ _ _ _ _
  zero_right := fun x => by
    unfold clmulKaratsuba64
    have hb := clmul_isBilinear 32 64
    simp [hb.zero_right]
  xor_right := fun x b1 b2 => by
    unfold clmulKaratsuba64
    dsimp only
    have hb := clmul_isBilinear 32 64
    rw [bitvec_extract_xor_distrib 0 32 b1 b2, bitvec_extract_xor_distrib 32 32 b1 b2]
    rw [bitvec_xor_four_rearrange (BitVec.extractLsb' 0 32 b1) (BitVec.extractLsb' 0 32 b2)
          (BitVec.extractLsb' 32 32 b1) (BitVec.extractLsb' 32 32 b2)]
    have h0 := hb.xor_right (BitVec.extractLsb' 0 32 x)
                 (BitVec.extractLsb' 0 32 b1) (BitVec.extractLsb' 0 32 b2)
    have h2 := hb.xor_right (BitVec.extractLsb' 32 32 x)
                 (BitVec.extractLsb' 32 32 b1) (BitVec.extractLsb' 32 32 b2)
    have hM := hb.xor_right (BitVec.extractLsb' 0 32 x ^^^ BitVec.extractLsb' 32 32 x)
                 (BitVec.extractLsb' 0 32 b1 ^^^ BitVec.extractLsb' 32 32 b1)
                 (BitVec.extractLsb' 0 32 b2 ^^^ BitVec.extractLsb' 32 32 b2)
    rw [h0, h2, hM, bitvec_zeroExtend_xor, bitvec_zeroExtend_xor, bitvec_zeroExtend_xor]
    exact karatsuba_xor_rearrange _ _ _ _ _ _

/-- Full 64x64 -> 128-bit `pclmulqdq` Karatsuba vs Schoolbook equivalence! -/
theorem pclmulqdq64_karatsuba_eq_schoolbook :
    ∀ (x y : BitVec 64), clmulKaratsuba64 x y = clmul 64 128 x y :=
  checkF2Bilinear_sound clmulKaratsuba64_isBilinear (clmul_isBilinear 64 128) (by decide +kernel)

/-- Full 64x64 -> 128-bit `pclmulqdq` commutativity! -/
theorem pclmulqdq64_comm :
    ∀ (x y : BitVec 64), clmul 64 128 x y = clmul 64 128 y x :=
  checkF2Bilinear_sound
    (clmul_isBilinear 64 128)
    { zero_left  := fun y => (clmul_isBilinear 64 128).zero_right y
      xor_left   := fun a1 a2 y => (clmul_isBilinear 64 128).xor_right y a1 a2
      zero_right := fun x => (clmul_isBilinear 64 128).zero_left x
      xor_right  := fun x b1 b2 => (clmul_isBilinear 64 128).xor_left b1 b2 x }
    (by decide +kernel)

-- ============================================================================
-- SIMD 128-bit `vpshufb` Byte Permutes & Split-Nibble GF(2^8) Multiply!
-- ============================================================================

/-- Extract byte `i` (`0 ≤ i < 16`) from a 128-bit XMM register. -/
def getByte128 (v : BitVec 128) (i : Nat) : BitVec 8 :=
  BitVec.extractLsb' (8 * i) 8 v

/-- Pack 16 bytes (`f 0` at LSB .. `f 15` at MSB) into a 128-bit XMM register via shifts and XOR. -/
def packBytes128Aux (f : Nat → BitVec 8) : Nat → BitVec 128
  | 0 => 0#128
  | Nat.succ k =>
    packBytes128Aux f k ^^^ (((f k).zeroExtend 128) <<< (8 * k))

def packBytes128 (f : Nat → BitVec 8) : BitVec 128 :=
  packBytes128Aux f 16

/-- x86 SSSE3 `VPSHUFB xmm_src, xmm_ctrl`:
    For each lane `i ∈ [0, 16)`, if bit 7 of `ctrl` byte `i` is 1 then `0x00`,
    else byte `(ctrl_byte_i & 0x0f)` of `src`. -/
def vpshufb128 (src ctrl : BitVec 128) : BitVec 128 :=
  packBytes128 fun i =>
    let cb := getByte128 ctrl i
    match cb.getLsbD 7 with
    | true  => 0#8
    | false => getByte128 src ((cb &&& 0x0f#8).toNat)

theorem getByte128_zero (i : Nat) : getByte128 (0#128) i = 0#8 := by
  simp [getByte128]

theorem getByte128_xor (a b : BitVec 128) (i : Nat) :
    getByte128 (a ^^^ b) i = getByte128 a i ^^^ getByte128 b i :=
  bitvec_extract_xor_distrib (8 * i) 8 a b

theorem packBytes128Aux_zero (f : Nat → BitVec 8) (hf : ∀ i, f i = 0#8) :
    ∀ n : Nat, packBytes128Aux f n = 0#128
  | 0 => rfl
  | Nat.succ k => by
    unfold packBytes128Aux
    rw [packBytes128Aux_zero f hf k, hf k]
    simp

theorem packBytes128Aux_xor (f g : Nat → BitVec 8) :
    ∀ n : Nat, packBytes128Aux (fun i => f i ^^^ g i) n =
      packBytes128Aux f n ^^^ packBytes128Aux g n
  | 0 => by simp [packBytes128Aux]
  | Nat.succ k => by
    unfold packBytes128Aux
    rw [packBytes128Aux_xor f g k, bitvec_zeroExtend_xor, bitvec_shl_xor_distrib]
    exact bitvec_xor_four_rearrange _ _ _ _

/-- `src ↦ vpshufb128 src ctrl` (dynamic source, constant control mask) is unconditionally F_2-linear! -/
theorem vpshufb128_constCtrl_isLinear (ctrl : BitVec 128) :
    IsF2Linear1 (fun src => vpshufb128 src ctrl) where
  map_zero := by
    unfold vpshufb128 packBytes128
    apply packBytes128Aux_zero
    intro i
    dsimp only
    cases (getByte128 ctrl i).getLsbD 7 <;> simp [getByte128_zero]
  map_xor := fun a b => by
    unfold vpshufb128 packBytes128
    rw [← packBytes128Aux_xor]
    congr 1
    funext i
    dsimp only
    cases (getByte128 ctrl i).getLsbD 7 with
    | true  => simp
    | false => exact getByte128_xor a b _

/-- Checks whether a 16-byte `vpshufb` LUT (`lut : BitVec 128`) is F_2-linear over 4-bit indices `0..15`. -/
def checkLut16Row (lut : BitVec 128) (a : Nat) : Nat → Bool
  | 0 => true
  | Nat.succ b =>
    checkLut16Row lut a b &&
    (getByte128 lut (Nat.xor a b) == (getByte128 lut a ^^^ getByte128 lut b))

def checkLut16LinearAux (lut : BitVec 128) : Nat → Bool
  | 0 => true
  | Nat.succ a => checkLut16LinearAux lut a && checkLut16Row lut a 16

def checkLut16Linear (lut : BitVec 128) : Bool :=
  (getByte128 lut 0 == 0#8) && checkLut16LinearAux lut 16

theorem checkLut16Row_sound {lut : BitVec 128} {a : Nat} :
    ∀ {n b : Nat}, b < n → checkLut16Row lut a n = true →
      getByte128 lut (Nat.xor a b) = getByte128 lut a ^^^ getByte128 lut b
  | 0, _, hb, _ => nomatch hb
  | Nat.succ k, b, hb, hchk => by
    unfold checkLut16Row at hchk
    cases hp : checkLut16Row lut a k with
    | false => rw [hp] at hchk; contradiction
    | true =>
      rw [hp, Bool.true_and] at hchk
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hb) with
      | inl hlt => exact checkLut16Row_sound hlt hp
      | inr heq =>
        subst heq
        exact eq_of_beq hchk

theorem checkLut16LinearAux_sound {lut : BitVec 128} :
    ∀ {m a b : Nat}, a < m → b < 16 → checkLut16LinearAux lut m = true →
      getByte128 lut (Nat.xor a b) = getByte128 lut a ^^^ getByte128 lut b
  | 0, _, _, ha, _, _ => nomatch ha
  | Nat.succ k, a, b, ha, hb, hchk => by
    unfold checkLut16LinearAux at hchk
    cases hp : checkLut16LinearAux lut k with
    | false => rw [hp] at hchk; contradiction
    | true =>
      rw [hp, Bool.true_and] at hchk
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ha) with
      | inl hlt => exact checkLut16LinearAux_sound hlt hb hp
      | inr heq =>
        subst heq
        exact checkLut16Row_sound hb hchk

theorem nibble_mask_lt_16 (x : BitVec 8) : (x &&& 0x0f#8).toNat < 16 := by
  have heq : (x &&& 0x0f#8) = (BitVec.extractLsb' 0 4 x).zeroExtend 8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.zero_add]
    rw [Bool.and_comm]
    congr 1
    revert i; decide
  rw [heq]
  unfold BitVec.zeroExtend
  rw [BitVec.toNat_setWidth]
  have hlt : (BitVec.extractLsb' 0 4 x).toNat < 16 := (BitVec.extractLsb' 0 4 x).isLt
  omega

theorem nibble_mask_msb_false (x : BitVec 8) : (x &&& 0x0f#8).getLsbD 7 = false := by
  simp

/-- Vectorized split-nibble GF(2^8) multiplication across 16 bytes using two `vpshufb128` calls! -/
def gf256SimdVpshufb128 (lutLo lutHi : BitVec 128) (v : BitVec 128) : BitVec 128 :=
  let mask0f : BitVec 128 := 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128
  let lo := v &&& mask0f
  let hi := (v >>> 4) &&& mask0f
  vpshufb128 lutLo lo ^^^ vpshufb128 lutHi hi

theorem getByte128_mask0f (v : BitVec 128) (i : Nat) (hi : i < 16) :
    getByte128 (v &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i = (getByte128 v i) &&& 0x0f#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [getByte128, BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and, BitVec.getLsbD_and]
  congr 1
  -- Check that bit `8*i + k` of `0x0f0f...0f#128` equals `(0x0f#8).getLsbD k` for `i < 16, k < 8`:
  revert i k
  decide

theorem getByte128_shr4_mask0f (v : BitVec 128) (i : Nat) (hi : i < 16) :
    getByte128 ((v >>> 4) &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i = ((getByte128 v i) >>> 4) &&& 0x0f#8 := by
  rw [getByte128_mask0f (v >>> 4) i hi]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [getByte128, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    hk, decide_true, Bool.true_and]
  -- When `k ≥ 4`, `(0x0f#8).getLsbD k = false`, making both sides `false`!
  -- When `k < 4`, `8*i + (4 + k) < 128` and `4 + k < 8`!
  cases h4 : decide (k < 4) with
  | false =>
    have h0f : (0x0f#8).getLsbD k = false := by
      revert k; decide
    rw [h0f, Bool.and_false, Bool.and_false]
  | true =>
    rw [decide_eq_true_eq] at h4
    have h128 : 4 + (8 * i + k) < 128 := by omega
    have h8 : 4 + k < 8 := by omega
    have hadd : 4 + (8 * i + k) = 8 * i + (4 + k) := by omega
    simp [h8, hadd]

theorem packBytes128Aux_congr {f g : Nat → BitVec 8} :
    ∀ {n : Nat}, (∀ i < n, f i = g i) → packBytes128Aux f n = packBytes128Aux g n
  | 0, _ => rfl
  | Nat.succ k, hfg => by
    unfold packBytes128Aux
    rw [packBytes128Aux_congr (fun i hi => hfg i (Nat.lt_succ_of_lt hi)), hfg k (Nat.lt_succ_self k)]

/-- Whenever `checkLut16Linear lutLo && checkLut16Linear lutHi = true`, the 16-lane `vpshufb`
    split-nibble lookup `gf256SimdVpshufb128 lutLo lutHi` is guaranteed `IsF2Linear1`! -/
theorem gf256SimdVpshufb128_isLinear {lutLo lutHi : BitVec 128}
    (hLo : checkLut16Linear lutLo = true) (hHi : checkLut16Linear lutHi = true) :
    IsF2Linear1 (gf256SimdVpshufb128 lutLo lutHi) := by
  unfold checkLut16Linear at hLo hHi
  cases hLo0 : (getByte128 lutLo 0 == 0#8) with
  | false => rw [hLo0] at hLo; contradiction
  | true =>
    rw [hLo0, Bool.true_and] at hLo
    cases hHi0 : (getByte128 lutHi 0 == 0#8) with
    | false => rw [hHi0] at hHi; contradiction
    | true =>
      rw [hHi0, Bool.true_and] at hHi
      have zLo := eq_of_beq hLo0
      have zHi := eq_of_beq hHi0
      refine { map_zero := ?_, map_xor := ?_ }
      · unfold gf256SimdVpshufb128 vpshufb128 packBytes128
        dsimp only
        have pLo : packBytes128Aux (fun i =>
            let cb := getByte128 (0#128 &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i
            match cb.getLsbD 7 with | true => 0#8 | false => getByte128 lutLo (cb &&& 0x0f#8).toNat) 16 = 0#128 := by
          apply packBytes128Aux_zero
          intro i
          dsimp only
          have hcb : getByte128 (0#128 &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i = 0#8 := by
            simp [getByte128]
          rw [hcb]
          exact zLo
        have pHi : packBytes128Aux (fun i =>
            let cb := getByte128 ((0#128 >>> 4) &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i
            match cb.getLsbD 7 with | true => 0#8 | false => getByte128 lutHi (cb &&& 0x0f#8).toNat) 16 = 0#128 := by
          apply packBytes128Aux_zero
          intro i
          dsimp only
          have hcb : getByte128 ((0#128 >>> 4) &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i = 0#8 := by
            simp [getByte128]
          rw [hcb]
          exact zHi
        rw [pLo, pHi]
        rfl
      · intro a b
        unfold gf256SimdVpshufb128 vpshufb128 packBytes128
        dsimp only
        have hPartLo : packBytes128Aux (fun i =>
            let cb := getByte128 ((a ^^^ b) &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i
            match cb.getLsbD 7 with | true => 0#8 | false => getByte128 lutLo (cb &&& 0x0f#8).toNat) 16 =
          packBytes128Aux (fun i =>
            let cb := getByte128 (a &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i
            match cb.getLsbD 7 with | true => 0#8 | false => getByte128 lutLo (cb &&& 0x0f#8).toNat) 16 ^^^
          packBytes128Aux (fun i =>
            let cb := getByte128 (b &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i
            match cb.getLsbD 7 with | true => 0#8 | false => getByte128 lutLo (cb &&& 0x0f#8).toNat) 16 := by
          rw [← packBytes128Aux_xor]
          apply packBytes128Aux_congr
          intro i hi
          dsimp only
          rw [getByte128_mask0f (a ^^^ b) i hi, getByte128_mask0f a i hi, getByte128_mask0f b i hi]
          rw [nibble_mask_msb_false, nibble_mask_msb_false, nibble_mask_msb_false]
          dsimp only
          rw [getByte128_xor a b i, bitvec_and_xor_distrib_right]
          have h1 : ((getByte128 a i &&& 0x0f#8) &&& 0x0f#8) = (getByte128 a i &&& 0x0f#8) := by simp [BitVec.and_assoc]
          have h2 : ((getByte128 b i &&& 0x0f#8) &&& 0x0f#8) = (getByte128 b i &&& 0x0f#8) := by simp [BitVec.and_assoc]
          have h3 : (((getByte128 a i &&& 0x0f#8) ^^^ (getByte128 b i &&& 0x0f#8)) &&& 0x0f#8) =
                    ((getByte128 a i &&& 0x0f#8) ^^^ (getByte128 b i &&& 0x0f#8)) := by
            rw [bitvec_and_xor_distrib_right, h1, h2]
          rw [h1, h2, h3, BitVec.toNat_xor]
          exact checkLut16LinearAux_sound (nibble_mask_lt_16 _) (nibble_mask_lt_16 _) hLo
        have hPartHi : packBytes128Aux (fun i =>
            let cb := getByte128 (((a ^^^ b) >>> 4) &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i
            match cb.getLsbD 7 with | true => 0#8 | false => getByte128 lutHi (cb &&& 0x0f#8).toNat) 16 =
          packBytes128Aux (fun i =>
            let cb := getByte128 ((a >>> 4) &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i
            match cb.getLsbD 7 with | true => 0#8 | false => getByte128 lutHi (cb &&& 0x0f#8).toNat) 16 ^^^
          packBytes128Aux (fun i =>
            let cb := getByte128 ((b >>> 4) &&& 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f#128) i
            match cb.getLsbD 7 with | true => 0#8 | false => getByte128 lutHi (cb &&& 0x0f#8).toNat) 16 := by
          rw [← packBytes128Aux_xor]
          apply packBytes128Aux_congr
          intro i hi
          dsimp only
          rw [getByte128_shr4_mask0f (a ^^^ b) i hi, getByte128_shr4_mask0f a i hi, getByte128_shr4_mask0f b i hi]
          rw [nibble_mask_msb_false, nibble_mask_msb_false, nibble_mask_msb_false]
          dsimp only
          rw [getByte128_xor a b i, bitvec_lshr_xor_distrib, bitvec_and_xor_distrib_right]
          have h1 : (((getByte128 a i >>> 4) &&& 0x0f#8) &&& 0x0f#8) = ((getByte128 a i >>> 4) &&& 0x0f#8) := by simp [BitVec.and_assoc]
          have h2 : (((getByte128 b i >>> 4) &&& 0x0f#8) &&& 0x0f#8) = ((getByte128 b i >>> 4) &&& 0x0f#8) := by simp [BitVec.and_assoc]
          have h3 : ((((getByte128 a i >>> 4) &&& 0x0f#8) ^^^ ((getByte128 b i >>> 4) &&& 0x0f#8)) &&& 0x0f#8) =
                    (((getByte128 a i >>> 4) &&& 0x0f#8) ^^^ ((getByte128 b i >>> 4) &&& 0x0f#8)) := by
            rw [bitvec_and_xor_distrib_right, h1, h2]
          rw [h1, h2, h3, BitVec.toNat_xor]
          exact checkLut16LinearAux_sound (nibble_mask_lt_16 _) (nibble_mask_lt_16 _) hHi
        rw [hPartLo, hPartHi]
        exact bitvec_xor_four_rearrange _ _ _ _

/-- Reference bit-level GF(2^8) multiplication modulo `x^8 + x^4 + x^3 + x + 1` (`0x1b`, AES/GHASH byte field). -/
def gf256Xtime (a : BitVec 8) : BitVec 8 :=
  match a.getLsbD 7 with
  | false => a <<< 1
  | true  => (a <<< 1) ^^^ 0x1b#8

def gf256MulConstByteAux (c a : BitVec 8) : Nat → BitVec 8
  | 0 => 0#8
  | Nat.succ k =>
    -- Horner step from MSB `k`: `xtime(prev) ^^^ (if c[k] then a else 0)`
    let prev := gf256MulConstByteAux c a k
    let shifted := gf256Xtime prev
    match c.getLsbD (7 - k) with
    | false => shifted
    | true  => shifted ^^^ a

def gf256MulConstByte (c a : BitVec 8) : BitVec 8 :=
  gf256MulConstByteAux c a 8

def gf256MulConstSimd128 (c : BitVec 8) (v : BitVec 128) : BitVec 128 :=
  packBytes128 fun i => gf256MulConstByte c (getByte128 v i)

theorem gf256Xtime_zero : gf256Xtime 0#8 = 0#8 := rfl

theorem gf256Xtime_xor (a b : BitVec 8) :
    gf256Xtime (a ^^^ b) = gf256Xtime a ^^^ gf256Xtime b := by
  unfold gf256Xtime
  rw [BitVec.getLsbD_xor, bitvec_shl_xor_distrib]
  cases a.getLsbD 7 <;> cases b.getLsbD 7
  · change (a <<< 1) ^^^ (b <<< 1) = (a <<< 1) ^^^ (b <<< 1)
    rfl
  · change ((a <<< 1) ^^^ (b <<< 1)) ^^^ 0x1b#8 = (a <<< 1) ^^^ ((b <<< 1) ^^^ 0x1b#8)
    exact BitVec.xor_assoc _ _ _
  · change ((a <<< 1) ^^^ (b <<< 1)) ^^^ 0x1b#8 = ((a <<< 1) ^^^ 0x1b#8) ^^^ (b <<< 1)
    apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_xor]
    cases (a <<< 1).getLsbD i <;> cases (b <<< 1).getLsbD i <;> cases (0x1b#8).getLsbD i <;> rfl
  · change (a <<< 1) ^^^ (b <<< 1) = ((a <<< 1) ^^^ 0x1b#8) ^^^ ((b <<< 1) ^^^ 0x1b#8)
    apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_xor]
    cases (a <<< 1).getLsbD i <;> cases (b <<< 1).getLsbD i <;> cases (0x1b#8).getLsbD i <;> rfl

theorem gf256MulConstByteAux_zero (c : BitVec 8) :
    ∀ n : Nat, gf256MulConstByteAux c 0#8 n = 0#8
  | 0 => rfl
  | Nat.succ k => by
    unfold gf256MulConstByteAux
    dsimp only
    rw [gf256MulConstByteAux_zero c k, gf256Xtime_zero]
    cases c.getLsbD (7 - k) <;> rfl

theorem gf256MulConstByteAux_xor (c a b : BitVec 8) :
    ∀ n : Nat, gf256MulConstByteAux c (a ^^^ b) n =
      gf256MulConstByteAux c a n ^^^ gf256MulConstByteAux c b n
  | 0 => by simp [gf256MulConstByteAux]
  | Nat.succ k => by
    unfold gf256MulConstByteAux
    dsimp only
    rw [gf256MulConstByteAux_xor c a b k, gf256Xtime_xor]
    cases c.getLsbD (7 - k) with
    | false => rfl
    | true => exact bitvec_xor_four_rearrange _ _ _ _

theorem gf256MulConstSimd128_isLinear (c : BitVec 8) :
    IsF2Linear1 (gf256MulConstSimd128 c) where
  map_zero := by
    unfold gf256MulConstSimd128 packBytes128
    apply packBytes128Aux_zero
    intro i
    rw [getByte128_zero]
    exact gf256MulConstByteAux_zero c 8
  map_xor := fun a b => by
    unfold gf256MulConstSimd128 packBytes128
    rw [← packBytes128Aux_xor]
    congr 1
    funext i
    rw [getByte128_xor]
    exact gf256MulConstByteAux_xor c _ _ 8

/-- Precompute the two 16-byte `vpshufb` tables (`lutLo`, `lutHi`) for any GF(2^8) constant `c`. -/
def mkGf256LutLo (c : BitVec 8) : BitVec 128 :=
  packBytes128 fun nib => gf256MulConstByte c (BitVec.ofNat 8 nib)

def mkGf256LutHi (c : BitVec 8) : BitVec 128 :=
  packBytes128 fun nib => gf256MulConstByte c (BitVec.ofNat 8 (nib * 16))

/-- End-to-end 128-bit SIMD theorem: for AES MixColumns / Reed-Solomon constant `0x0e` (or `0x9d`),
    16-lane `vpshufb` split-nibble GF(2^8) multiplication equals 16-lane polynomial GF(2^8)
    multiplication across ALL `2^128` XMM register inputs! -/
theorem vpshufb128_gf256_mul_0x9d_eq :
    ∀ v : BitVec 128,
      gf256SimdVpshufb128 (mkGf256LutLo 0x9d#8) (mkGf256LutHi 0x9d#8) v =
      gf256MulConstSimd128 0x9d#8 v :=
  checkF2Linear1_sound
    (gf256SimdVpshufb128_isLinear (by decide +kernel) (by decide +kernel))
    (gf256MulConstSimd128_isLinear 0x9d#8)
    (by decide +kernel)

/-- Constant-polynomial `pclmulqdq` CRC-64-ECMA folding (`0x42f0e1eba9ea3693`):
    Unary `IsF2Linear1` requires only 64 unit-basis evaluations in GMP (`< 0.1s` kernel replay)! -/
theorem crc64_ecma_pclmulqdq_karatsuba_eq_schoolbook :
    ∀ x : BitVec 64,
      clmulKaratsuba64 x 0x42f0e1eba9ea3693#64 = clmul 64 128 x 0x42f0e1eba9ea3693#64 :=
  checkF2Linear1_sound
    ⟨clmulKaratsuba64_isBilinear.zero_left _, fun a1 a2 => clmulKaratsuba64_isBilinear.xor_left a1 a2 _⟩
    ⟨(clmul_isBilinear 64 128).zero_left _, fun a1 a2 => (clmul_isBilinear 64 128).xor_left a1 a2 _⟩
    (by decide +kernel)

end F2SimdCert
