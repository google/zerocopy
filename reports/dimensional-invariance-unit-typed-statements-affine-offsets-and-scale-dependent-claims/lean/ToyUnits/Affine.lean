import ToyUnits.Instances

/-!
# Affine (offset) units: dimension checking over-claims; a point/vector discipline restores invariance

One point dimension (temperature), modelled as an ordered one-dimensional affine space over the
scalars (an interval scale). Readings have one of three sorts:
* `pt`  — a temperature reading (a point); a scale change `g = (a, b)` maps it to `a * v + b`;
* `vec` — a temperature difference (a vector); `g` maps it to `a * v`;
* `num` — a dimensionless number; unchanged.

Plain dimension checking (`ADimChecked`) gives `pt` and `vec` the same exponent `1` and so
accepts `t₁ + t₂ ≤ t₃`. The point/vector discipline (`HasSort`, `PointVectorTyped`) allows
point − point (a vector), point ± vector and vector + point (a point), vector-space operations
(scalar multiplication on either side, division by a number), ratios of vectors, binary affine
combinations of points with constant weights satisfying a side condition `W` (the standard one is
`WeightsSumOne`), and comparisons within one sort.
-/

namespace Toy.Units

/-- Sorts of the affine toy. -/
inductive ASort where
  | pt
  | vec
  | num

variable {K : Type} [ScalarOps K]

/-- How a temperature scale change `g = (a, b)` acts on a reading of sort `σ`. -/
def ASort.act (g : K × K) : ASort → K → K
  | .pt, v => g.1 * v + g.2
  | .vec, v => g.1 * v
  | .num, v => v

/-- The exponent of the temperature dimension that plain dimension checking assigns to a sort. -/
def ASort.exp : ASort → Int
  | .pt => 1
  | .vec => 1
  | .num => 0

/-- Expressions of the affine toy; `comb w₁ e₁ w₂ e₂` is the weighted sum `w₁ * e₁ + w₂ * e₂`. -/
inductive AExpr (K : Type) where
  | var (x : Nat)
  | lit (c : K) (σ : ASort)
  | add (e₁ e₂ : AExpr K)
  | sub (e₁ e₂ : AExpr K)
  | mul (e₁ e₂ : AExpr K)
  | div (e₁ e₂ : AExpr K)
  | comb (w₁ : K) (e₁ : AExpr K) (w₂ : K) (e₂ : AExpr K)

/-- Formulas of the affine toy; quantifiers carry the sort of the bound variable. -/
inductive AFormula (K : Type) where
  | le (e₁ e₂ : AExpr K)
  | eq (e₁ e₂ : AExpr K)
  | and (φ ψ : AFormula K)
  | or (φ ψ : AFormula K)
  | not (φ : AFormula K)
  | all (x : Nat) (σ : ASort) (φ : AFormula K)
  | ex (x : Nat) (σ : ASort) (φ : AFormula K)

/-- Raw reading in temperature scale `u` (relative to the reference scale): a literal `lit c σ`
denotes `c` in the reference scale and reads as `σ.act u c`. -/
def AExpr.evalIn (u : K × K) (ρ : Env K) : AExpr K → K
  | .var x => ρ x
  | .lit c σ => σ.act u c
  | .add e₁ e₂ => e₁.evalIn u ρ + e₂.evalIn u ρ
  | .sub e₁ e₂ => e₁.evalIn u ρ + -(e₂.evalIn u ρ)
  | .mul e₁ e₂ => e₁.evalIn u ρ * e₂.evalIn u ρ
  | .div e₁ e₂ => e₁.evalIn u ρ * (e₂.evalIn u ρ)⁻¹
  | .comb w₁ e₁ w₂ e₂ => w₁ * e₁.evalIn u ρ + w₂ * e₂.evalIn u ρ

/-- Raw reading of an affine-toy formula; quantifiers range over all of `K`. -/
def AFormula.holdsIn (u : K × K) : Env K → AFormula K → Prop
  | ρ, .le e₁ e₂ => e₁.evalIn u ρ ≤ e₂.evalIn u ρ
  | ρ, .eq e₁ e₂ => e₁.evalIn u ρ = e₂.evalIn u ρ
  | ρ, .and φ ψ => AFormula.holdsIn u ρ φ ∧ AFormula.holdsIn u ρ ψ
  | ρ, .or φ ψ => AFormula.holdsIn u ρ φ ∨ AFormula.holdsIn u ρ ψ
  | ρ, .not φ => ¬ AFormula.holdsIn u ρ φ
  | ρ, .all x _ φ => ∀ v : K, AFormula.holdsIn u (upd ρ x v) φ
  | ρ, .ex x _ φ => ∃ v : K, AFormula.holdsIn u (upd ρ x v) φ

/-- The scale change `g` applied to readings whose sorts are given by `S`. -/
def actA (S : Nat → ASort) (g : K × K) (ρ : Env K) : Env K := fun x => (S x).act g (ρ x)

/-- `φ` keeps its truth value under every scale change `g = (a, b)` with `a > 0`, from every scale
`u` (including scales with `u.1 ≤ 0`) to `(a * u.1, a * u.2 + b)`, with readings transformed by
`actA S g`. -/
def AffineInvariant (S : Nat → ASort) (φ : AFormula K) : Prop :=
  ∀ g : K × K, 0 < g.1 → ∀ (u : K × K) (ρ : Env K),
    AFormula.holdsIn (g.1 * u.1, g.1 * u.2 + g.2) (actA S g ρ) φ ↔ AFormula.holdsIn u ρ φ

/-- `φ` keeps its truth value under every scale change `g = (a, b)` with `a > 0` between scales
with positive factor: from a scale `u` with `u.1 > 0` to `(a * u.1, a * u.2 + b)` when
`a * u.1 > 0`. Scales with `u.1 ≤ 0` are not considered. -/
def PosAffineInvariant (S : Nat → ASort) (φ : AFormula K) : Prop :=
  ∀ (g u : K × K) (ρ : Env K), 0 < g.1 → 0 < u.1 → 0 < g.1 * u.1 →
    (AFormula.holdsIn (g.1 * u.1, g.1 * u.2 + g.2) (actA S g ρ) φ ↔ AFormula.holdsIn u ρ φ)

/-- Invariance over all scales implies invariance over scales with positive factor. -/
theorem posAffineInvariant_of_affineInvariant {S : Nat → ASort} {φ : AFormula K}
    (h : AffineInvariant S φ) : PosAffineInvariant S φ :=
  fun g u ρ hg _ _ => h g hg u ρ

/-- Plain dimension checking (temperature exponent only; points and differences both have
exponent `1`). -/
inductive ADimChecked (S : Nat → ASort) : AExpr K → Int → Prop
  | var (x : Nat) : ADimChecked S (.var x) (S x).exp
  | lit (c : K) (σ : ASort) : ADimChecked S (.lit c σ) σ.exp
  | add {e₁ e₂ : AExpr K} {k : Int} :
      ADimChecked S e₁ k → ADimChecked S e₂ k → ADimChecked S (.add e₁ e₂) k
  | sub {e₁ e₂ : AExpr K} {k : Int} :
      ADimChecked S e₁ k → ADimChecked S e₂ k → ADimChecked S (.sub e₁ e₂) k
  | mul {e₁ e₂ : AExpr K} {k₁ k₂ : Int} :
      ADimChecked S e₁ k₁ → ADimChecked S e₂ k₂ → ADimChecked S (.mul e₁ e₂) (k₁ + k₂)
  | div {e₁ e₂ : AExpr K} {k₁ k₂ : Int} :
      ADimChecked S e₁ k₁ → ADimChecked S e₂ k₂ → ADimChecked S (.div e₁ e₂) (k₁ - k₂)
  | comb {e₁ e₂ : AExpr K} {k : Int} (w₁ w₂ : K) :
      ADimChecked S e₁ k → ADimChecked S e₂ k → ADimChecked S (.comb w₁ e₁ w₂ e₂) k

/-- Plain dimension checking for affine-toy formulas. -/
inductive ADimCheckedF : (Nat → ASort) → AFormula K → Prop
  | le {S : Nat → ASort} {e₁ e₂ : AExpr K} {k : Int} :
      ADimChecked S e₁ k → ADimChecked S e₂ k → ADimCheckedF S (.le e₁ e₂)
  | eq {S : Nat → ASort} {e₁ e₂ : AExpr K} {k : Int} :
      ADimChecked S e₁ k → ADimChecked S e₂ k → ADimCheckedF S (.eq e₁ e₂)
  | and {S : Nat → ASort} {φ ψ : AFormula K} :
      ADimCheckedF S φ → ADimCheckedF S ψ → ADimCheckedF S (.and φ ψ)
  | or {S : Nat → ASort} {φ ψ : AFormula K} :
      ADimCheckedF S φ → ADimCheckedF S ψ → ADimCheckedF S (.or φ ψ)
  | not {S : Nat → ASort} {φ : AFormula K} : ADimCheckedF S φ → ADimCheckedF S (.not φ)
  | all {S : Nat → ASort} {x : Nat} {σ : ASort} {φ : AFormula K} :
      ADimCheckedF (upd S x σ) φ → ADimCheckedF S (.all x σ φ)
  | ex {S : Nat → ASort} {x : Nat} {σ : ASort} {φ : AFormula K} :
      ADimCheckedF (upd S x σ) φ → ADimCheckedF S (.ex x σ φ)

/-- The point/vector (torsor) discipline, with side condition `W` on the weights of an affine
combination of two points. -/
inductive HasSort (W : K → K → Prop) (S : Nat → ASort) : AExpr K → ASort → Prop
  | var (x : Nat) : HasSort W S (.var x) (S x)
  | lit (c : K) (σ : ASort) : HasSort W S (.lit c σ) σ
  | ptSubPt {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .pt → HasSort W S e₂ .pt → HasSort W S (.sub e₁ e₂) .vec
  | ptAddVec {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .pt → HasSort W S e₂ .vec → HasSort W S (.add e₁ e₂) .pt
  | vecAddPt {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .vec → HasSort W S e₂ .pt → HasSort W S (.add e₁ e₂) .pt
  | ptSubVec {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .pt → HasSort W S e₂ .vec → HasSort W S (.sub e₁ e₂) .pt
  | vecAdd {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .vec → HasSort W S e₂ .vec → HasSort W S (.add e₁ e₂) .vec
  | vecSub {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .vec → HasSort W S e₂ .vec → HasSort W S (.sub e₁ e₂) .vec
  | numMulVec {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .num → HasSort W S e₂ .vec → HasSort W S (.mul e₁ e₂) .vec
  | vecMulNum {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .vec → HasSort W S e₂ .num → HasSort W S (.mul e₁ e₂) .vec
  | vecDivNum {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .vec → HasSort W S e₂ .num → HasSort W S (.div e₁ e₂) .vec
  | vecDivVec {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .vec → HasSort W S e₂ .vec → HasSort W S (.div e₁ e₂) .num
  | numAdd {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .num → HasSort W S e₂ .num → HasSort W S (.add e₁ e₂) .num
  | numSub {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .num → HasSort W S e₂ .num → HasSort W S (.sub e₁ e₂) .num
  | numMul {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .num → HasSort W S e₂ .num → HasSort W S (.mul e₁ e₂) .num
  | numDiv {e₁ e₂ : AExpr K} :
      HasSort W S e₁ .num → HasSort W S e₂ .num → HasSort W S (.div e₁ e₂) .num
  | combPt {e₁ e₂ : AExpr K} (w₁ w₂ : K) :
      W w₁ w₂ → HasSort W S e₁ .pt → HasSort W S e₂ .pt → HasSort W S (.comb w₁ e₁ w₂ e₂) .pt

/-- The point/vector discipline for formulas: atoms compare two expressions of one sort. -/
inductive PointVectorTyped (W : K → K → Prop) : (Nat → ASort) → AFormula K → Prop
  | le {S : Nat → ASort} {e₁ e₂ : AExpr K} {σ : ASort} :
      HasSort W S e₁ σ → HasSort W S e₂ σ → PointVectorTyped W S (.le e₁ e₂)
  | eq {S : Nat → ASort} {e₁ e₂ : AExpr K} {σ : ASort} :
      HasSort W S e₁ σ → HasSort W S e₂ σ → PointVectorTyped W S (.eq e₁ e₂)
  | and {S : Nat → ASort} {φ ψ : AFormula K} :
      PointVectorTyped W S φ → PointVectorTyped W S ψ → PointVectorTyped W S (.and φ ψ)
  | or {S : Nat → ASort} {φ ψ : AFormula K} :
      PointVectorTyped W S φ → PointVectorTyped W S ψ → PointVectorTyped W S (.or φ ψ)
  | not {S : Nat → ASort} {φ : AFormula K} : PointVectorTyped W S φ → PointVectorTyped W S (.not φ)
  | all {S : Nat → ASort} {x : Nat} {σ : ASort} {φ : AFormula K} :
      PointVectorTyped W (upd S x σ) φ → PointVectorTyped W S (.all x σ φ)
  | ex {S : Nat → ASort} {x : Nat} {σ : ASort} {φ : AFormula K} :
      PointVectorTyped W (upd S x σ) φ → PointVectorTyped W S (.ex x σ φ)

/-- The standard weight condition for an affine combination: the weights sum to `1`. -/
def WeightsSumOne (w₁ w₂ : K) : Prop := w₁ + w₂ = 1

section Lemmas
variable (h : CommRingLaws K)
include h

theorem neg_add_distrib' (p q : K) : -(p + q) = -p + -q := by
  symm; apply neg_eq_of_add_eq_zero' h
  haveI : Std.Associative (α := K) (· + ·) := ⟨h.add_assoc⟩
  haveI : Std.Commutative (α := K) (· + ·) := ⟨h.add_comm⟩
  calc p + q + (-p + -q) = (p + -p) + (q + -q) := by ac_rfl
    _ = 0 := by rw [h.add_neg, h.add_neg, h.add_zero]

theorem act_comp (σ : ASort) (g u : K × K) (c : K) :
    σ.act (g.1 * u.1, g.1 * u.2 + g.2) c = σ.act g (σ.act u c) := by
  cases σ with
  | pt => simp only [ASort.act]; rw [h.distrib, h.mul_assoc, h.add_assoc]
  | vec => simp only [ASort.act]; rw [h.mul_assoc]
  | num => rfl

theorem pt_sub_pt (a b X Y : K) : (a * X + b) + -(a * Y + b) = a * (X + -Y) := by
  haveI : Std.Associative (α := K) (· + ·) := ⟨h.add_assoc⟩
  haveI : Std.Commutative (α := K) (· + ·) := ⟨h.add_comm⟩
  rw [neg_add_distrib' h, h.distrib, mul_neg' h]
  calc a * X + b + (-(a * Y) + -b) = (a * X + -(a * Y)) + (b + -b) := by ac_rfl
    _ = a * X + -(a * Y) := by rw [h.add_neg, h.add_zero]

theorem pt_add_vec (a b X Y : K) : (a * X + b) + a * Y = a * (X + Y) + b := by
  haveI : Std.Associative (α := K) (· + ·) := ⟨h.add_assoc⟩
  haveI : Std.Commutative (α := K) (· + ·) := ⟨h.add_comm⟩
  rw [h.distrib]; ac_rfl

theorem vec_add_pt (a b X Y : K) : a * X + (a * Y + b) = a * (X + Y) + b := by
  haveI : Std.Associative (α := K) (· + ·) := ⟨h.add_assoc⟩
  haveI : Std.Commutative (α := K) (· + ·) := ⟨h.add_comm⟩
  rw [h.distrib]; ac_rfl

theorem pt_sub_vec (a b X Y : K) : (a * X + b) + -(a * Y) = a * (X + -Y) + b := by
  haveI : Std.Associative (α := K) (· + ·) := ⟨h.add_assoc⟩
  haveI : Std.Commutative (α := K) (· + ·) := ⟨h.add_comm⟩
  rw [h.distrib, mul_neg' h]; ac_rfl

theorem comb_pt (a b X Y w₁ w₂ : K) (hw : w₁ + w₂ = 1) :
    w₁ * (a * X + b) + w₂ * (a * Y + b) = a * (w₁ * X + w₂ * Y) + b := by
  haveI : Std.Associative (α := K) (· + ·) := ⟨h.add_assoc⟩
  haveI : Std.Commutative (α := K) (· + ·) := ⟨h.add_comm⟩
  rw [h.distrib, h.distrib, h.distrib, mul_left_comm' h w₁ a, mul_left_comm' h w₂ a]
  calc a * (w₁ * X) + w₁ * b + (a * (w₂ * Y) + w₂ * b)
      = a * (w₁ * X) + a * (w₂ * Y) + (w₁ * b + w₂ * b) := by ac_rfl
    _ = a * (w₁ * X) + a * (w₂ * Y) + b := by rw [← add_mul' h, hw, one_mul' h]

omit h in
theorem upd_actA (S : Nat → ASort) (g : K × K) (ρ : Env K) (x : Nat) (σ : ASort) (v : K) :
    upd (actA S g ρ) x (σ.act g v) = actA (upd S x σ) g (upd ρ x v) := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [upd, actA]
  · simp [upd, actA, hy]

end Lemmas

/-- **Covariance.** Under the field laws and `0⁻¹ = 0`, for every scale change `g` with
`g.1 ≠ 0`, an expression of sort `σ` (weights summing to one) read after the change equals
`σ.act g` applied to its reading before the change. -/
theorem AExpr.evalIn_act (h : FieldLaws K) (hz : InvZeroLaw K) {S : Nat → ASort}
    {e : AExpr K} {σ : ASort} (he : HasSort WeightsSumOne S e σ) {g : K × K} (hg : g.1 ≠ 0)
    (u : K × K) (ρ : Env K) :
    AExpr.evalIn (g.1 * u.1, g.1 * u.2 + g.2) (actA S g ρ) e = σ.act g (AExpr.evalIn u ρ e) := by
  have hR := h.toCommRingLaws
  induction he with
  | var x => rfl
  | lit c σ => exact act_comp hR σ g u c
  | ptSubPt _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂, pt_sub_pt hR]
  | ptAddVec _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂, pt_add_vec hR]
  | vecAddPt _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂, vec_add_pt hR]
  | ptSubVec _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂, pt_sub_vec hR]
  | vecAdd _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂, h.distrib]
  | vecSub _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂, h.distrib, mul_neg' hR]
  | numMulVec _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂, mul_left_comm' hR]
  | vecMulNum _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂, h.mul_assoc]
  | vecDivNum _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂, h.mul_assoc]
  | vecDivVec _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *
    rw [ih₁, ih₂, mul_inv' h hz, mul_mul_mul_comm' hR, h.mul_inv _ hg, one_mul' hR]
  | numAdd _ _ ih₁ ih₂ => simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂]
  | numSub _ _ ih₁ ih₂ => simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂]
  | numMul _ _ ih₁ ih₂ => simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂]
  | numDiv _ _ ih₁ ih₂ => simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂]
  | combPt w₁ w₂ hw _ _ ih₁ ih₂ =>
    simp only [AExpr.evalIn, ASort.act] at *; rw [ih₁, ih₂, comb_pt hR _ _ _ _ _ _ hw]

section OrderLemmas
variable (h : OrderedFieldLaws K)
include h

theorem add_le_add_iff_right' (a b c : K) : a + c ≤ b + c ↔ a ≤ b := by
  constructor
  · intro hle
    have := h.add_le_mono _ _ (-c) hle
    rwa [h.add_assoc, h.add_assoc, h.add_neg, h.add_zero, h.add_zero] at this
  · exact h.add_le_mono a b c

theorem act_le_iff (σ : ASort) {g : K × K} (hg : 0 < g.1) (a b : K) :
    σ.act g a ≤ σ.act g b ↔ a ≤ b := by
  cases σ with
  | pt => simp only [ASort.act]; rw [add_le_add_iff_right' h]; exact mul_le_mul_left_iff' h hg
  | vec => simp only [ASort.act]; exact mul_le_mul_left_iff' h hg
  | num => exact Iff.rfl

end OrderLemmas

theorem act_inj (h : FieldLaws K) (σ : ASort) {g : K × K} (hg : g.1 ≠ 0) (a b : K) :
    σ.act g a = σ.act g b ↔ a = b := by
  constructor
  · intro e
    cases σ with
    | pt =>
      simp only [ASort.act] at e
      exact mul_left_cancel₀' h hg (add_right_cancel' h.toCommRingLaws e)
    | vec => exact mul_left_cancel₀' h hg e
    | num => exact e
  · intro e; rw [e]

theorem act_surj (h : FieldLaws K) (σ : ASort) {g : K × K} (hg : g.1 ≠ 0) (v : K) :
    ∃ w, σ.act g w = v := by
  have hR := h.toCommRingLaws
  cases σ with
  | pt =>
    refine ⟨g.1⁻¹ * (v + -g.2), ?_⟩
    simp only [ASort.act]
    rw [← h.mul_assoc, h.mul_inv _ hg, one_mul' hR, h.add_assoc, neg_add_cancel' hR, h.add_zero]
  | vec =>
    refine ⟨g.1⁻¹ * v, ?_⟩
    simp only [ASort.act]; rw [← h.mul_assoc, h.mul_inv _ hg, one_mul' hR]
  | num => exact ⟨v, rfl⟩

/-- **The point/vector discipline restores invariance.** Under the ordered-field laws and
`0⁻¹ = 0`, every formula typed by the point/vector discipline with weights summing to one is
invariant under every scale change `x ↦ a * x + b` with `a > 0`, from every scale `u`. -/
theorem affineInvariant_of_pointVectorTyped (h : OrderedFieldLaws K) (hz : InvZeroLaw K)
    {S : Nat → ASort} {φ : AFormula K} (hφ : PointVectorTyped WeightsSumOne S φ) :
    AffineInvariant S φ := by
  intro g hg
  have hg0 : g.1 ≠ 0 := (ne_of_lt' h hg).symm
  induction hφ with
  | le h₁ h₂ =>
    intro u ρ; simp only [AFormula.holdsIn]
    rw [AExpr.evalIn_act h.toFieldLaws hz h₁ hg0, AExpr.evalIn_act h.toFieldLaws hz h₂ hg0]
    exact act_le_iff h _ hg _ _
  | eq h₁ h₂ =>
    intro u ρ; simp only [AFormula.holdsIn]
    rw [AExpr.evalIn_act h.toFieldLaws hz h₁ hg0, AExpr.evalIn_act h.toFieldLaws hz h₂ hg0]
    exact act_inj h.toFieldLaws _ hg0 _ _
  | and _ _ ih₁ ih₂ => intro u ρ; simp only [AFormula.holdsIn]; rw [ih₁, ih₂]
  | or _ _ ih₁ ih₂ => intro u ρ; simp only [AFormula.holdsIn]; rw [ih₁, ih₂]
  | not _ ih => intro u ρ; simp only [AFormula.holdsIn]; rw [ih]
  | @all S x σ φ _ ih =>
    intro u ρ; simp only [AFormula.holdsIn]
    constructor
    · intro H v
      have := H (σ.act g v)
      rwa [upd_actA, ih] at this
    · intro H v
      obtain ⟨w, rfl⟩ := act_surj h.toFieldLaws σ hg0 v
      rw [upd_actA, ih]; exact H w
  | @ex S x σ φ _ ih =>
    intro u ρ; simp only [AFormula.holdsIn]
    constructor
    · rintro ⟨v, hv⟩
      obtain ⟨w, rfl⟩ := act_surj h.toFieldLaws σ hg0 v
      rw [upd_actA, ih] at hv; exact ⟨w, hv⟩
    · rintro ⟨v, hv⟩
      exact ⟨σ.act g v, by rwa [upd_actA, ih]⟩

end Toy.Units
