import ToyUnits.Counterexamples

/-!
# A free theorem for one-variable expressions of dimension `L`

Setting: one base dimension, a length variable `x` (`Γ x = L`), and an expression `e` that
mentions no variable other than `x`, has only dimensionless literals, and has dimension `L`
(`OneVarLength`). Then `e` reads as `c * v` at `x = v`, with the exposed constant
`c = e` read at `x = 1`.

* `oneVarLength_poly_eval_eq_mul`: for every `v`, polynomial fragment, commutative-ring laws only;
  `Γ x = L` is not assumed (it follows, `ctx_eq_L_of_poly`).
* `oneVarLength_eval_eq_mul`: for every `v`, full rational fragment, field laws and `0⁻¹ = 0`.
* `definableOnPos_iff`: the functions computed on positive readings, in every unit system and for
  all readings of other variables, by a well-typed expression of dimension `L` in a length
  variable are the maps `v ↦ c * v`; hence `v ↦ v + 1` and `v ↦ max v 1` are not definable.
-/

namespace Toy.Units

variable {m : Nat} {K : Type} [ScalarOps K]

/-- Every variable occurrence in `e` is `x`. -/
def Expr.onlyVar (x : Nat) : Expr m K → Prop
  | .var y => y = x
  | .lit _ _ => True
  | .add a b => a.onlyVar x ∧ b.onlyVar x
  | .sub a b => a.onlyVar x ∧ b.onlyVar x
  | .mul a b => a.onlyVar x ∧ b.onlyVar x
  | .div a b => a.onlyVar x ∧ b.onlyVar x
  | .zpow a _ => a.onlyVar x

/-- Every literal in `e` is dimensionless. -/
def Expr.dimlessLits : Expr m K → Prop
  | .var _ => True
  | .lit _ d => d = Dim.one
  | .add a b => a.dimlessLits ∧ b.dimlessLits
  | .sub a b => a.dimlessLits ∧ b.dimlessLits
  | .mul a b => a.dimlessLits ∧ b.dimlessLits
  | .div a b => a.dimlessLits ∧ b.dimlessLits
  | .zpow a _ => a.dimlessLits

/-- `e` uses no division and no negative power. -/
def Expr.isPolynomial : Expr m K → Prop
  | .var _ => True
  | .lit _ _ => True
  | .add a b => a.isPolynomial ∧ b.isPolynomial
  | .sub a b => a.isPolynomial ∧ b.isPolynomial
  | .mul a b => a.isPolynomial ∧ b.isPolynomial
  | .div _ _ => False
  | .zpow a k => 0 ≤ k ∧ a.isPolynomial

/-- `e` is a one-variable expression of dimension `L` in the length variable `x`, with
dimensionless literals. -/
structure OneVarLength (Γ : Ctx 1) (x : Nat) (e : Expr 1 K) : Prop where
  ctx_x : Γ x = L
  typed : HasDim Γ e L
  only_x : e.onlyVar x
  dimless : e.dimlessLits

theorem scaleOf_dimOne (h : CommRingLaws K) (s : Fin m → K) : scaleOf s Dim.one = 1 := by
  unfold scaleOf Dim.one; exact finProd_one h m

/-- The reading of `e` depends only on the reading of `x` when `e` mentions only `x` and has
dimensionless literals; in particular it does not depend on the unit system. -/
theorem evalIn_congr_of_onlyVar_dimless (h : CommRingLaws K) {x : Nat} {e : Expr m K}
    (hx : e.onlyVar x) (hd : e.dimlessLits) (s s' : Fin m → K) {ρ ρ' : Env K}
    (hρ : ρ x = ρ' x) : e.evalIn s ρ = e.evalIn s' ρ' := by
  induction e with
  | var y => simp only [Expr.onlyVar] at hx; subst hx; exact hρ
  | lit c d =>
    simp only [Expr.dimlessLits] at hd; subst hd
    simp only [Expr.evalIn]; rw [scaleOf_dimOne h, scaleOf_dimOne h]
  | add a b iha ihb => simp only [Expr.evalIn]; rw [iha hx.1 hd.1, ihb hx.2 hd.2]
  | sub a b iha ihb => simp only [Expr.evalIn]; rw [iha hx.1 hd.1, ihb hx.2 hd.2]
  | mul a b iha ihb => simp only [Expr.evalIn]; rw [iha hx.1 hd.1, ihb hx.2 hd.2]
  | div a b iha ihb => simp only [Expr.evalIn]; rw [iha hx.1 hd.1, ihb hx.2 hd.2]
  | zpow a k iha => simp only [Expr.evalIn]; rw [iha hx hd]

theorem upd_self {α : Type} (f : Nat → α) (x : Nat) (v : α) : upd f x v x = v := by
  simp [upd]

/-- Homogeneity step: under the field laws and `0⁻¹ = 0`, at every nonzero reading `x = v` a
one-variable expression of dimension `L` with dimensionless literals reads as its reading at
`x = 1` times `v` (rescale by the unit change `t = v`). -/
theorem oneVarLength_eval_eq_mul_of_ne_zero (h : FieldLaws K) (hz : InvZeroLaw K)
    {Γ : Ctx 1} {x : Nat} {e : Expr 1 K} (he : OneVarLength Γ x e)
    (s : Fin 1 → K) (ρ : Env K) (v : K) (hv : v ≠ 0) :
    e.evalIn s (upd ρ x v) = e.evalIn s (upd ρ x 1) * v := by
  have hR := h.toCommRingLaws
  have ht : ∀ i : Fin 1, (fun _ => v) i ≠ 0 := fun _ => hv
  have hom := evalIn_act_eq_scaleOf_mul h hz he.typed ht s (upd ρ x 1)
  rw [scaleOf_L hR] at hom
  have hc : e.evalIn (fun i => (fun _ => v) i * s i) (actEnv Γ (fun _ => v) (upd ρ x 1)) =
      e.evalIn s (upd ρ x v) := by
    apply evalIn_congr_of_onlyVar_dimless hR he.only_x he.dimless
    simp only [actEnv, upd_self, he.ctx_x, scaleOf_L hR]; exact h.mul_one v
  rw [← hc, hom, h.mul_comm]

omit [ScalarOps K] in
/-- Dimension count for the polynomial fragment: a polynomial expression that mentions only `x`
and has dimensionless literals has dimension exponent `n * Γ x 0` for some natural number `n`. -/
theorem poly_dim_eq_nat_mul_ctx {Γ : Ctx 1} {x : Nat} {e : Expr 1 K} {d : Dim 1}
    (he : HasDim Γ e d) (hx : e.onlyVar x) (hd : e.dimlessLits) (hp : e.isPolynomial) :
    ∃ n : Nat, d 0 = (n : Int) * Γ x 0 := by
  induction he with
  | var y =>
    simp only [Expr.onlyVar] at hx; subst hx
    exact ⟨1, by omega⟩
  | lit c d' =>
    simp only [Expr.dimlessLits] at hd; subst hd
    exact ⟨0, by simp [Dim.one]⟩
  | add _ _ ih₁ _ => exact ih₁ hx.1 hd.1 hp.1
  | sub _ _ ih₁ _ => exact ih₁ hx.1 hd.1 hp.1
  | mul _ _ ih₁ ih₂ =>
    obtain ⟨n₁, h₁⟩ := ih₁ hx.1 hd.1 hp.1
    obtain ⟨n₂, h₂⟩ := ih₂ hx.2 hd.2 hp.2
    refine ⟨n₁ + n₂, ?_⟩
    simp only [Dim.mul, h₁, h₂]
    rw [Int.natCast_add, Int.add_mul]
  | div _ _ _ _ => exact hp.elim
  | zpow k _ ih =>
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp.1
    obtain ⟨n₀, h₀⟩ := ih hx hd hp.2
    refine ⟨n * n₀, ?_⟩
    simp only [Dim.pow, h₀]
    rw [Int.natCast_mul, Int.mul_assoc]

omit [ScalarOps K] in
/-- In the polynomial fragment `x` must be a length: a polynomial expression of dimension `L` that
mentions only `x` and has dimensionless literals forces `Γ x = L` (no scalar law is used). -/
theorem ctx_eq_L_of_poly {Γ : Ctx 1} {x : Nat} {e : Expr 1 K}
    (htyped : HasDim Γ e L) (hx : e.onlyVar x) (hd : e.dimlessLits) (hp : e.isPolynomial) :
    Γ x = L := by
  obtain ⟨n, hn⟩ := poly_dim_eq_nat_mul_ctx htyped hx hd hp
  have h1 : (1 : Int) = (n : Int) * Γ x 0 := hn
  have hΓ0 : Γ x 0 = 1 := by
    cases n with
    | zero => simp at h1
    | succ k =>
      cases k with
      | zero => omega
      | succ k' =>
        have h1' : (1 : Int) = ((k' + 2 : Nat) : Int) * Γ x 0 := h1
        have hk : (2 : Int) ≤ ((k' + 2 : Nat) : Int) := by omega
        by_cases ha : Γ x 0 ≤ 0
        · have : ((k' + 2 : Nat) : Int) * Γ x 0 ≤ 0 :=
            Int.mul_nonpos_of_nonneg_of_nonpos (by omega) ha
          omega
        · have ha1 : (1 : Int) ≤ Γ x 0 := by omega
          have : (2 : Int) ≤ ((k' + 2 : Nat) : Int) * Γ x 0 := by
            have := Int.mul_le_mul_of_nonneg_right hk (by omega : (0 : Int) ≤ Γ x 0)
            omega
          omega
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  exact hΓ0

/-- Auxiliary induction for the polynomial fragment. -/
theorem oneVarLength_poly_aux (h : CommRingLaws K) {Γ : Ctx 1} {x : Nat} (hΓ : Γ x = L)
    {e : Expr 1 K} {d : Dim 1} (he : HasDim Γ e d) :
    e.onlyVar x → e.dimlessLits → e.isPolynomial →
      ∃ k : Nat, (∀ i, d i = (k : Int)) ∧ ∀ (s : Fin 1 → K) (ρ : Env K) (v : K),
        e.evalIn s (upd ρ x v) = e.evalIn s (upd ρ x 1) * npow v k := by
  induction he with
  | var y =>
    intro hx _ _
    simp only [Expr.onlyVar] at hx; subst hx
    refine ⟨1, fun i => by rw [hΓ]; rfl, fun s ρ v => ?_⟩
    simp only [Expr.evalIn, upd_self]; rw [npow_one h, one_mul' h]
  | lit c d =>
    intro _ hd _
    simp only [Expr.dimlessLits] at hd; subst hd
    exact ⟨0, fun i => rfl, fun s ρ v => by simp only [Expr.evalIn, npow]; rw [h.mul_one]⟩
  | add _ _ ih₁ ih₂ =>
    intro hx hd hp
    obtain ⟨k₁, hk₁, e₁⟩ := ih₁ hx.1 hd.1 hp.1
    obtain ⟨k₂, hk₂, e₂⟩ := ih₂ hx.2 hd.2 hp.2
    have : k₂ = k₁ := by have := (hk₁ 0).symm.trans (hk₂ 0); omega
    subst this
    refine ⟨k₂, hk₁, fun s ρ v => ?_⟩
    simp only [Expr.evalIn]; rw [e₁, e₂, add_mul' h]
  | sub _ _ ih₁ ih₂ =>
    intro hx hd hp
    obtain ⟨k₁, hk₁, e₁⟩ := ih₁ hx.1 hd.1 hp.1
    obtain ⟨k₂, hk₂, e₂⟩ := ih₂ hx.2 hd.2 hp.2
    have : k₂ = k₁ := by have := (hk₁ 0).symm.trans (hk₂ 0); omega
    subst this
    refine ⟨k₂, hk₁, fun s ρ v => ?_⟩
    simp only [Expr.evalIn]; rw [e₁, e₂, add_mul' h, neg_mul' h]
  | mul _ _ ih₁ ih₂ =>
    intro hx hd hp
    obtain ⟨k₁, hk₁, e₁⟩ := ih₁ hx.1 hd.1 hp.1
    obtain ⟨k₂, hk₂, e₂⟩ := ih₂ hx.2 hd.2 hp.2
    refine ⟨k₁ + k₂, fun i => ?_, fun s ρ v => ?_⟩
    · simp only [Dim.mul]; rw [hk₁, hk₂]; omega
    · simp only [Expr.evalIn]; rw [e₁, e₂, npow_add h, mul_mul_mul_comm' h]
  | div _ _ _ _ => intro _ _ hp; exact hp.elim
  | zpow k _ ih =>
    intro hx hd hp
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp.1
    obtain ⟨k₀, hk₀, e₀⟩ := ih hx hd hp.2
    refine ⟨k₀ * n, fun i => ?_, fun s ρ v => ?_⟩
    · simp only [Dim.pow]; rw [hk₀]; simp [Int.mul_comm]
    · show npow _ n = npow _ n * _
      rw [e₀, npow_mul_base h, npow_npow h]

/-- **Free theorem, polynomial fragment.** Under the commutative-ring laws alone, a polynomial
expression of dimension `L` that mentions only the variable `x` and has dimensionless literals
reads, at every `x = v`, as its reading at `x = 1` times `v`. -/
theorem oneVarLength_poly_eval_eq_mul (h : CommRingLaws K) {Γ : Ctx 1} {x : Nat}
    {e : Expr 1 K} (htyped : HasDim Γ e L) (hx : e.onlyVar x) (hd : e.dimlessLits)
    (hp : e.isPolynomial) (s : Fin 1 → K) (ρ : Env K) (v : K) :
    e.evalIn s (upd ρ x v) = e.evalIn s (upd ρ x 1) * v := by
  obtain ⟨k, hk, hev⟩ :=
    oneVarLength_poly_aux h (ctx_eq_L_of_poly htyped hx hd hp) htyped hx hd hp
  have : k = 1 := by have := hk 0; simp only [L] at this; omega
  subst this
  rw [hev, npow_one h]

/-- Auxiliary induction for the rational fragment at nonzero readings. -/
theorem oneVarLength_aux (h : FieldLaws K) (hz : InvZeroLaw K) {Γ : Ctx 1} {x : Nat}
    (hΓ : Γ x = L) {e : Expr 1 K} {d : Dim 1} (he : HasDim Γ e d) :
    e.onlyVar x → e.dimlessLits →
      ∃ k : Int, (∀ i, d i = k) ∧ ∀ (s : Fin 1 → K) (ρ : Env K) (v : K), v ≠ 0 →
        e.evalIn s (upd ρ x v) = e.evalIn s (upd ρ x 1) * zpow v k := by
  have hR := h.toCommRingLaws
  induction he with
  | var y =>
    intro hx _
    simp only [Expr.onlyVar] at hx; subst hx
    refine ⟨1, fun i => by rw [hΓ]; rfl, fun s ρ v _ => ?_⟩
    simp only [Expr.evalIn, upd_self]; rw [zpow_one h, one_mul' hR]
  | lit c d =>
    intro _ hd
    simp only [Expr.dimlessLits] at hd; subst hd
    exact ⟨0, fun i => rfl, fun s ρ v _ => by
      simp only [Expr.evalIn]; rw [zpow_zero, h.mul_one]⟩
  | add _ _ ih₁ ih₂ =>
    intro hx hd
    obtain ⟨k₁, hk₁, e₁⟩ := ih₁ hx.1 hd.1
    obtain ⟨k₂, hk₂, e₂⟩ := ih₂ hx.2 hd.2
    have : k₂ = k₁ := (hk₂ 0).symm.trans (hk₁ 0)
    subst this
    refine ⟨k₂, hk₁, fun s ρ v hv => ?_⟩
    simp only [Expr.evalIn]; rw [e₁ s ρ v hv, e₂ s ρ v hv, add_mul' hR]
  | sub _ _ ih₁ ih₂ =>
    intro hx hd
    obtain ⟨k₁, hk₁, e₁⟩ := ih₁ hx.1 hd.1
    obtain ⟨k₂, hk₂, e₂⟩ := ih₂ hx.2 hd.2
    have : k₂ = k₁ := (hk₂ 0).symm.trans (hk₁ 0)
    subst this
    refine ⟨k₂, hk₁, fun s ρ v hv => ?_⟩
    simp only [Expr.evalIn]; rw [e₁ s ρ v hv, e₂ s ρ v hv, add_mul' hR, neg_mul' hR]
  | mul _ _ ih₁ ih₂ =>
    intro hx hd
    obtain ⟨k₁, hk₁, e₁⟩ := ih₁ hx.1 hd.1
    obtain ⟨k₂, hk₂, e₂⟩ := ih₂ hx.2 hd.2
    refine ⟨k₁ + k₂, fun i => ?_, fun s ρ v hv => ?_⟩
    · simp only [Dim.mul]; rw [hk₁, hk₂]
    · simp only [Expr.evalIn]
      rw [e₁ s ρ v hv, e₂ s ρ v hv, zpow_add h hv, mul_mul_mul_comm' hR]
  | div _ _ ih₁ ih₂ =>
    intro hx hd
    obtain ⟨k₁, hk₁, e₁⟩ := ih₁ hx.1 hd.1
    obtain ⟨k₂, hk₂, e₂⟩ := ih₂ hx.2 hd.2
    refine ⟨k₁ - k₂, fun i => ?_, fun s ρ v hv => ?_⟩
    · simp only [Dim.div]; rw [hk₁, hk₂]
    · simp only [Expr.evalIn]
      rw [e₁ s ρ v hv, e₂ s ρ v hv, mul_inv' h hz, Int.sub_eq_add_neg, zpow_add h hv,
        zpow_neg h hv, mul_mul_mul_comm' hR]
  | zpow k _ ih =>
    intro hx hd
    obtain ⟨k₀, hk₀, e₀⟩ := ih hx hd
    refine ⟨k * k₀, fun i => ?_, fun s ρ v hv => ?_⟩
    · simp only [Dim.pow]; rw [hk₀]
    · simp only [Expr.evalIn]
      rw [e₀ s ρ v hv, zpow_mul_base h hz, zpow_zpow h hv]

theorem one_add_one_ne_zero' (h : OrderedFieldLaws K) : (1 : K) + 1 ≠ 0 := by
  intro e
  have h1 := h.add_le_mono 0 1 1 (zero_le_one' h)
  rw [zero_add' h.toCommRingLaws, e] at h1
  exact h.zero_ne_one (h.le_antisymm _ _ (zero_le_one' h) h1)

/-- At the reading `x = 0`, under the commutative-ring laws and `0⁻¹ = 0` (no order law, no
inverse law), an expression that mentions only `x`, has dimensionless literals and has a nonzero
dimension exponent reads `0`. -/
theorem evalIn_zero_of_dim_ne_zero (h : CommRingLaws K) (hz : InvZeroLaw K)
    {Γ : Ctx 1} {x : Nat} {e : Expr 1 K} {d : Dim 1}
    (he : HasDim Γ e d) (hx : e.onlyVar x) (hd : e.dimlessLits) (hdim : d 0 ≠ 0)
    (s : Fin 1 → K) (ρ : Env K) :
    e.evalIn s (upd ρ x 0) = 0 := by
  induction he with
  | var y =>
    simp only [Expr.onlyVar] at hx; subst hx
    simp only [Expr.evalIn, upd_self]
  | lit c d' =>
    simp only [Expr.dimlessLits] at hd; subst hd
    exact (hdim rfl).elim
  | add _ _ ih₁ ih₂ =>
    simp only [Expr.evalIn]
    rw [ih₁ hx.1 hd.1 hdim, ih₂ hx.2 hd.2 hdim, h.add_zero]
  | sub _ _ ih₁ ih₂ =>
    simp only [Expr.evalIn]
    rw [ih₁ hx.1 hd.1 hdim, ih₂ hx.2 hd.2 hdim, neg_zero' h, h.add_zero]
  | @mul e₁ e₂ d₁ d₂ _ _ ih₁ ih₂ =>
    simp only [Expr.evalIn]
    by_cases h1 : d₁ 0 ≠ 0
    · rw [ih₁ hx.1 hd.1 h1, zero_mul' h]
    · have h2 : d₂ 0 ≠ 0 := by simp only [Dim.mul] at hdim; omega
      rw [ih₂ hx.2 hd.2 h2, mul_zero' h]
  | @div e₁ e₂ d₁ d₂ _ _ ih₁ ih₂ =>
    simp only [Expr.evalIn]
    by_cases h1 : d₁ 0 ≠ 0
    · rw [ih₁ hx.1 hd.1 h1, zero_mul' h]
    · have h2 : d₂ 0 ≠ 0 := by simp only [Dim.div] at hdim; omega
      rw [ih₂ hx.2 hd.2 h2, hz, mul_zero' h]
  | @zpow e₀ d₀ k _ ih =>
    simp only [Expr.evalIn]
    have h0 : d₀ 0 ≠ 0 := by
      intro hc; apply hdim; simp only [Dim.pow, hc, Int.mul_zero]
    have hk : k ≠ 0 := by
      intro hc; apply hdim; simp only [Dim.pow, hc, Int.zero_mul]
    rw [ih hx hd h0]
    cases k with
    | ofNat n =>
      cases n with
      | zero => exact (hk rfl).elim
      | succ n => exact npow_zero_base_succ h n
    | negSucc n =>
      simp only [zpow]
      rw [npow_zero_base_succ h n, hz]

/-- **Free theorem, rational fragment, every reading.** Under the field laws and `0⁻¹ = 0` (no
order law), a one-variable expression of dimension `L` with dimensionless literals reads, at every
`x = v` (zero and, in an ordered field, negative readings included), as its reading at `x = 1`
times `v`. -/
theorem oneVarLength_eval_eq_mul (h : FieldLaws K) (hz : InvZeroLaw K)
    {Γ : Ctx 1} {x : Nat} {e : Expr 1 K} (he : OneVarLength Γ x e)
    (s : Fin 1 → K) (ρ : Env K) (v : K) :
    e.evalIn s (upd ρ x v) = e.evalIn s (upd ρ x 1) * v := by
  have hR := h.toCommRingLaws
  by_cases hv : v = 0
  · subst hv
    rw [mul_zero' hR]
    exact evalIn_zero_of_dim_ne_zero hR hz he.typed he.only_x he.dimless
      (by decide : L 0 ≠ 0) s ρ
  · exact oneVarLength_eval_eq_mul_of_ne_zero h hz he s ρ v hv

/-! ## Definability on positive readings -/

/-- `f` is computed, at every positive reading `x = v` of a length variable `x`, in every unit
system and for all readings of the other variables, by some expression of dimension `L`. -/
def DefinableOnPos (f : K → K) : Prop :=
  ∃ (Γ : Ctx 1) (x : Nat) (e : Expr 1 K), Γ x = L ∧ HasDim Γ e L ∧
    ∀ (s : Fin 1 → K) (ρ : Env K) (v : K), 0 < v → e.evalIn s (upd ρ x v) = f v

/-- `lit c 1 * x`: the witness for linear maps. -/
def linearWitness (c : K) : Expr 1 K := .mul (.lit c Dim.one) (.var 0)

theorem dim_one_mul_L : Dim.mul Dim.one L = L := by
  funext i; simp [Dim.mul, Dim.one, L]

omit [ScalarOps K] in
theorem linearWitness_oneVarLength (c : K) : OneVarLength ctxL 0 (linearWitness c) where
  ctx_x := rfl
  typed := dim_one_mul_L ▸ HasDim.mul (HasDim.lit c Dim.one) (HasDim.var 0)
  only_x := ⟨trivial, rfl⟩
  dimless := ⟨rfl, trivial⟩

theorem upd_eq_self_of_apply {α : Type} (ρ : Nat → α) (x : Nat) (v : α) (h : ρ x = v) :
    upd ρ x v = ρ := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [upd, h]
  · simp [upd, hy]

/-- **Definability on positive readings (exact).** Under the ordered-field laws and `0⁻¹ = 0`,
a function `f` is computed on positive readings of a length variable, in every unit system and for
all readings of the other variables, by an expression of dimension `L` if and only if
`f v = c * v` for some constant `c` and every `v > 0`. -/
theorem definableOnPos_iff (h : OrderedFieldLaws K) (hz : InvZeroLaw K) (f : K → K) :
    DefinableOnPos f ↔ ∃ c : K, ∀ v : K, 0 < v → f v = c * v := by
  have hR := h.toCommRingLaws
  constructor
  · rintro ⟨Γ, x, e, hΓ, he, hf⟩
    refine ⟨e.evalIn (fun _ => 1) (upd (fun _ => 0) x 1), fun v hv => ?_⟩
    have hv0 : v ≠ 0 := (ne_of_lt' h hv).symm
    let ρ₀ : Env K := upd (fun _ => 0) x 1
    let ρ' : Env K := actEnv Γ (fun _ => v) ρ₀
    have hρ'x : ρ' x = v := by
      simp only [ρ', ρ₀, actEnv, upd_self, hΓ, scaleOf_L hR]
      exact h.mul_one v
    have hom := evalIn_act_eq_scaleOf_mul h.toFieldLaws hz he (fun _ => hv0) (fun _ => 1) ρ₀
    rw [scaleOf_L hR] at hom
    have h2 : e.evalIn (fun i => (fun _ => v) i * (fun _ => (1 : K)) i) ρ' = f v := by
      have := hf (fun i => (fun _ => v) i * (fun _ => (1 : K)) i) ρ' v hv
      rwa [upd_eq_self_of_apply ρ' x v hρ'x] at this
    rw [h2] at hom
    rw [hom, h.mul_comm]
  · rintro ⟨c, hc⟩
    refine ⟨ctxL, 0, linearWitness c, rfl, (linearWitness_oneVarLength c).typed,
      fun s ρ v hv => ?_⟩
    simp only [linearWitness, Expr.evalIn, upd_self]
    rw [scaleOf_dimOne hR, one_mul' hR, hc v hv]

/-- **Not definable: `v ↦ v + 1`.** Under the ordered-field laws and `0⁻¹ = 0`, no expression of
dimension `L` computes `v + 1` at every positive reading `v` of a length variable, in every unit
system and for all readings of the other variables. -/
theorem not_definableOnPos_add_one (h : OrderedFieldLaws K) (hz : InvZeroLaw K) :
    ¬ DefinableOnPos (fun v : K => v + 1) := by
  have hR := h.toCommRingLaws
  rw [definableOnPos_iff h hz]
  rintro ⟨c, hc⟩
  have h1 := hc 1 (zero_lt_one' h)
  rw [h.mul_one] at h1
  have h2pos : (0 : K) < 1 + 1 := by
    apply lt_of_le_of_ne' h
    · have := h.add_le_mono 0 1 1 (zero_le_one' h)
      rw [zero_add' hR] at this
      exact h.le_trans _ _ _ (zero_le_one' h) this
    · exact (one_add_one_ne_zero' h).symm
  have h2 := hc (1 + 1) h2pos
  rw [← h1, h.distrib, h.mul_one] at h2
  have h3 := add_left_cancel' hR h2
  have h4 : (1 : K) + 1 = 1 + 0 := by rw [h.add_zero]; exact h3.symm
  exact h.zero_ne_one (add_left_cancel' hR h4).symm

/-- **Not definable: `v ↦ max v 1`** (over `Rat`). No expression of dimension `L` computes
`max v 1` at every positive reading `v` of a length variable, in every unit system and for all
readings of the other variables. -/
theorem not_definableOnPos_max_one : ¬ DefinableOnPos (fun v : Rat => max v 1) := by
  rw [definableOnPos_iff ratLaws ratInvZero]
  rintro ⟨c, hc⟩
  have h1 := hc 1 (by decide)
  have h2 := hc (1 / 2) (by grind)
  have e1 : max (1 : Rat) 1 = 1 := by grind
  have e2 : max (1 / 2 : Rat) 1 = 1 := by grind
  rw [e1] at h1; rw [e2] at h2
  grind

/-- **Positive control (scale-invariant threshold).** `v ↦ max v 0` is definable on positive
readings (it equals `v ↦ 1 * v` there). -/
theorem definableOnPos_max_zero : DefinableOnPos (fun v : Rat => max v 0) :=
  (definableOnPos_iff ratLaws ratInvZero _).2 ⟨1, fun v hv => by grind⟩

/-! ## Controls and tightness -/

/-- `x + lit 1 L`: `x` plus one reference length. -/
def addOneLength : Expr 1 Rat := .add (.var 0) (.lit 1 L)

/-- **Control (dimensioned literal).** `x + lit 1 L` has dimension `L` and mentions only `x`, its
literal is not dimensionless, and in the unit system `s` it reads `v + s 0` at `x = v`: it
computes `v + 1` in the reference system `s = 1` and not across unit systems. -/
theorem addOneLength_control :
    HasDim ctxL addOneLength L ∧ addOneLength.onlyVar 0 ∧ ¬ addOneLength.dimlessLits ∧
      ∀ (s : Fin 1 → Rat) (ρ : Env Rat) (v : Rat), addOneLength.evalIn s (upd ρ 0 v) = v + s 0 := by
  refine ⟨.add (.var 0) (.lit 1 L), ⟨rfl, trivial⟩, fun hd => ?_, fun s ρ v => ?_⟩
  · have := congrFun hd.2 0; simp [L, Dim.one] at this
  · simp only [addOneLength, Expr.evalIn, upd_self, scaleOf_L ratLaws.toCommRingLaws]; grind

/-- `x + lit 1 1`: `x` plus a dimensionless one. -/
def addOneDimless : Expr 1 Rat := .add (.var 0) (.lit 1 Dim.one)

/-- **Positive control (ill typed).** `x + lit 1 1` mentions only `x` and has dimensionless
literals, computes `v + 1` in every unit system, and has no dimension. -/
theorem addOneDimless_control :
    (∀ d, ¬ HasDim ctxL addOneDimless d) ∧ addOneDimless.onlyVar 0 ∧ addOneDimless.dimlessLits ∧
      ∀ (s : Fin 1 → Rat) (ρ : Env Rat) (v : Rat), addOneDimless.evalIn s (upd ρ 0 v) = v + 1 := by
  refine ⟨fun d hd => ?_, ⟨rfl, trivial⟩, ⟨trivial, rfl⟩, fun s ρ v => ?_⟩
  · obtain ⟨h₁, h₂⟩ := hasDim_add_inv hd
    have := congrFun ((hasDim_var_inv h₁).symm.trans (hasDim_lit_inv h₂)) 0
    simp [ctxL, L, Dim.one] at this
  · simp only [addOneDimless, Expr.evalIn, upd_self, scaleOf_dimOne ratLaws.toCommRingLaws]; grind

/-- `x * x / (x - x)` over `RatJ`. -/
def sqOverZero : Expr 1 RatJ := .div (.mul (.var 0) (.var 0)) (.sub (.var 0) (.var 0))

theorem dim_mul_L_L_div_L : Dim.div (Dim.mul L L) L = L := by
  funext i; simp [Dim.div, Dim.mul, L]

theorem sqOverZero_oneVarLength : OneVarLength ctxL 0 sqOverZero where
  ctx_x := rfl
  typed := dim_mul_L_L_div_L ▸
    HasDim.div (HasDim.mul (HasDim.var 0) (HasDim.var 0)) (HasDim.sub (HasDim.var 0) (HasDim.var 0))
  only_x := ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  dimless := ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- **Counterexample (`0⁻¹ = 0`, and polynomiality without it).** Over `RatJ` (every
ordered-field law, `0⁻¹ = 1`) the non-polynomial expression `x * x / (x - x)` of dimension `L`, in
the length variable `x` with dimensionless literals, reads `v * v` at `x = v`; at `v = 2` this is
`4`, not `1 * 2`. It satisfies every hypothesis of `oneVarLength_poly_eval_eq_mul` except
polynomiality, and every hypothesis of `oneVarLength_eval_eq_mul` except `0⁻¹ = 0`. -/
theorem sqOverZero_not_linear_ratJ :
    CommRingLaws RatJ ∧ FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ ctxL 0 = L ∧
      HasDim ctxL sqOverZero L ∧ sqOverZero.onlyVar 0 ∧ sqOverZero.dimlessLits ∧
      ¬ sqOverZero.isPolynomial ∧
      sqOverZero.evalIn (fun _ => 1) (upd (fun _ => RatJ.ofRat 0) 0 (RatJ.ofRat 2)) ≠
        sqOverZero.evalIn (fun _ => 1) (upd (fun _ => RatJ.ofRat 0) 0 1) * RatJ.ofRat 2 := by
  refine ⟨ratJLaws.toCommRingLaws, ratJLaws.toFieldLaws, ratJ_not_invZero, rfl,
    sqOverZero_oneVarLength.typed, sqOverZero_oneVarLength.only_x,
    sqOverZero_oneVarLength.dimless, fun hp => hp.elim, ?_⟩
  simp only [sqOverZero, Expr.evalIn, upd_self]
  simp only [RatJ.one_def, RatJ.mul_def, RatJ.add_def, RatJ.neg_def, RatJ.inv_def,
    ne_eq, RatJ.ofRat_inj]
  simp (config := { decide := true })
  grind

end Toy.Units
