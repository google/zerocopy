import ToyUnits.Algebra

/-!
# Dimensions, typed syntax, readings and unit changes

* A dimension over `m` base dimensions is an exponent vector `Fin m → Int`.
* Expressions: variables, literals annotated with a dimension, `+`, `-`, `*`, `/`, integer powers.
* Formulas: `≤` and `=` atoms, `∧`, `∨`, `¬`, `∀`/`∃` over a variable of a given dimension.
* `HasDim` and `WellTypedAt` are dimension checking; the raw reading `Expr.evalIn` /
  `Formula.holdsIn` ignores dimensions and evaluates the syntax over plain scalars.
* A unit system `s : Fin m → K` gives, per base dimension, the factor by which readings
  in `s` exceed readings in the reference units; a literal `lit c d` denotes `c` reference
  units of dimension `d` and reads as `scaleOf s d * c` in `s`.
-/

namespace Toy.Units

/-- A dimension: one integer exponent per base dimension. -/
abbrev Dim (m : Nat) := Fin m → Int

/-- The dimensionless dimension (all exponents `0`). -/
def Dim.one {m : Nat} : Dim m := fun _ => 0
/-- Product of dimensions: exponents add. -/
def Dim.mul {m : Nat} (d e : Dim m) : Dim m := fun i => d i + e i
/-- Quotient of dimensions: exponents subtract. -/
def Dim.div {m : Nat} (d e : Dim m) : Dim m := fun i => d i - e i
/-- Integer power of a dimension: exponents are multiplied by `k`. -/
def Dim.pow {m : Nat} (d : Dim m) (k : Int) : Dim m := fun i => k * d i

/-- Expressions over scalars `K` with `m` base dimensions. -/
inductive Expr (m : Nat) (K : Type) where
  | var (x : Nat)
  | lit (c : K) (d : Dim m)
  | add (e₁ e₂ : Expr m K)
  | sub (e₁ e₂ : Expr m K)
  | mul (e₁ e₂ : Expr m K)
  | div (e₁ e₂ : Expr m K)
  | zpow (e : Expr m K) (k : Int)

/-- Formulas; quantifiers carry the dimension of the bound variable. -/
inductive Formula (m : Nat) (K : Type) where
  | le (e₁ e₂ : Expr m K)
  | eq (e₁ e₂ : Expr m K)
  | and (φ ψ : Formula m K)
  | or (φ ψ : Formula m K)
  | not (φ : Formula m K)
  | all (x : Nat) (d : Dim m) (φ : Formula m K)
  | ex (x : Nat) (d : Dim m) (φ : Formula m K)

/-- A typing context: the declared dimension of every variable. -/
abbrev Ctx (m : Nat) := Nat → Dim m

/-- An environment: the numeric reading of every variable. -/
abbrev Env (K : Type) := Nat → K

/-- Point update of a function on variables. -/
def upd {α : Type} (f : Nat → α) (x : Nat) (v : α) : Nat → α :=
  fun y => if y = x then v else f y

variable {m : Nat} {K : Type} [ScalarOps K]

/-- Dimension checking for expressions: `+` and `-` need equal dimensions, `*` and `/` add and
subtract exponent vectors, `zpow e k` multiplies them by `k`. -/
inductive HasDim (Γ : Ctx m) : Expr m K → Dim m → Prop
  | var (x : Nat) : HasDim Γ (.var x) (Γ x)
  | lit (c : K) (d : Dim m) : HasDim Γ (.lit c d) d
  | add {e₁ e₂ : Expr m K} {d : Dim m} :
      HasDim Γ e₁ d → HasDim Γ e₂ d → HasDim Γ (.add e₁ e₂) d
  | sub {e₁ e₂ : Expr m K} {d : Dim m} :
      HasDim Γ e₁ d → HasDim Γ e₂ d → HasDim Γ (.sub e₁ e₂) d
  | mul {e₁ e₂ : Expr m K} {d₁ d₂ : Dim m} :
      HasDim Γ e₁ d₁ → HasDim Γ e₂ d₂ → HasDim Γ (.mul e₁ e₂) (Dim.mul d₁ d₂)
  | div {e₁ e₂ : Expr m K} {d₁ d₂ : Dim m} :
      HasDim Γ e₁ d₁ → HasDim Γ e₂ d₂ → HasDim Γ (.div e₁ e₂) (Dim.div d₁ d₂)
  | zpow {e : Expr m K} {d : Dim m} (k : Int) :
      HasDim Γ e d → HasDim Γ (.zpow e k) (Dim.pow d k)

/-- Dimension checking for formulas, with `≤` atoms allowed only at dimensions satisfying `O`.
Atoms compare two expressions of one dimension; quantifiers extend the context. -/
inductive WellTypedAt (O : Dim m → Prop) : Ctx m → Formula m K → Prop
  | le {Γ : Ctx m} {e₁ e₂ : Expr m K} {d : Dim m} :
      O d → HasDim Γ e₁ d → HasDim Γ e₂ d → WellTypedAt O Γ (.le e₁ e₂)
  | eq {Γ : Ctx m} {e₁ e₂ : Expr m K} {d : Dim m} :
      HasDim Γ e₁ d → HasDim Γ e₂ d → WellTypedAt O Γ (.eq e₁ e₂)
  | and {Γ : Ctx m} {φ ψ : Formula m K} :
      WellTypedAt O Γ φ → WellTypedAt O Γ ψ → WellTypedAt O Γ (.and φ ψ)
  | or {Γ : Ctx m} {φ ψ : Formula m K} :
      WellTypedAt O Γ φ → WellTypedAt O Γ ψ → WellTypedAt O Γ (.or φ ψ)
  | not {Γ : Ctx m} {φ : Formula m K} : WellTypedAt O Γ φ → WellTypedAt O Γ (.not φ)
  | all {Γ : Ctx m} {x : Nat} {d : Dim m} {φ : Formula m K} :
      WellTypedAt O (upd Γ x d) φ → WellTypedAt O Γ (.all x d φ)
  | ex {Γ : Ctx m} {x : Nat} {d : Dim m} {φ : Formula m K} :
      WellTypedAt O (upd Γ x d) φ → WellTypedAt O Γ (.ex x d φ)

/-- Dimension checking for formulas (order atoms at every dimension). -/
def WellTyped (Γ : Ctx m) (φ : Formula m K) : Prop := WellTypedAt (fun _ => True) Γ φ

/-- The factor `∏ i, s i ^ d i` by which unit system `s` multiplies readings of dimension `d`. -/
def scaleOf (s : Fin m → K) (d : Dim m) : K := finProd m (fun i => zpow (s i) (d i))

/-- The raw reading of an expression in unit system `s` with variable readings `ρ`:
dimensions are ignored except that `lit c d` reads as `scaleOf s d * c`. -/
def Expr.evalIn (s : Fin m → K) (ρ : Env K) : Expr m K → K
  | .var x => ρ x
  | .lit c d => scaleOf s d * c
  | .add e₁ e₂ => e₁.evalIn s ρ + e₂.evalIn s ρ
  | .sub e₁ e₂ => e₁.evalIn s ρ + -(e₂.evalIn s ρ)
  | .mul e₁ e₂ => e₁.evalIn s ρ * e₂.evalIn s ρ
  | .div e₁ e₂ => e₁.evalIn s ρ * (e₂.evalIn s ρ)⁻¹
  | .zpow e k => Toy.Units.zpow (e.evalIn s ρ) k

/-- The raw reading of a formula; quantifiers range over all of `K`. -/
def Formula.holdsIn (s : Fin m → K) : Env K → Formula m K → Prop
  | ρ, .le e₁ e₂ => e₁.evalIn s ρ ≤ e₂.evalIn s ρ
  | ρ, .eq e₁ e₂ => e₁.evalIn s ρ = e₂.evalIn s ρ
  | ρ, .and φ ψ => Formula.holdsIn s ρ φ ∧ Formula.holdsIn s ρ ψ
  | ρ, .or φ ψ => Formula.holdsIn s ρ φ ∨ Formula.holdsIn s ρ ψ
  | ρ, .not φ => ¬ Formula.holdsIn s ρ φ
  | ρ, .all x _ φ => ∀ v : K, Formula.holdsIn s (upd ρ x v) φ
  | ρ, .ex x _ φ => ∃ v : K, Formula.holdsIn s (upd ρ x v) φ

/-- The unit change `t` applied to readings: a variable of dimension `Γ x` is multiplied by
`scaleOf t (Γ x)`. -/
def actEnv (Γ : Ctx m) (t : Fin m → K) (ρ : Env K) : Env K := fun x => scaleOf t (Γ x) * ρ x

/-- Every scale factor is positive. -/
def Positive (t : Fin m → K) : Prop := ∀ i, 0 < t i

/-- Applying the unit change `t` (from any unit system `s` to `fun i => t i * s i`, with readings
transformed by `actEnv Γ t`) leaves the truth value of `φ` unchanged. -/
def InvariantAt (Γ : Ctx m) (t : Fin m → K) (φ : Formula m K) : Prop :=
  ∀ (s : Fin m → K) (ρ : Env K),
    Formula.holdsIn (fun i => t i * s i) (actEnv Γ t ρ) φ ↔ Formula.holdsIn s ρ φ

/-- `φ` is invariant under every positive unit change, applied to every base unit system `s`
(including base systems with zero or negative factors). -/
def UnitInvariant (Γ : Ctx m) (φ : Formula m K) : Prop :=
  ∀ t : Fin m → K, Positive t → InvariantAt Γ t φ

/-- `φ` is invariant under every positive unit change between positive unit systems: from a
system `s` with positive factors to `fun i => t i * s i`, where `t` and the new system have
positive factors. Base systems with a zero or negative factor are not considered. -/
def PosUnitInvariant (Γ : Ctx m) (φ : Formula m K) : Prop :=
  ∀ (t s : Fin m → K) (ρ : Env K), Positive t → Positive s → Positive (fun i => t i * s i) →
    (Formula.holdsIn (fun i => t i * s i) (actEnv Γ t ρ) φ ↔ Formula.holdsIn s ρ φ)

/-- Invariance over all base unit systems implies invariance over positive ones (no law needed). -/
theorem posUnitInvariant_of_unitInvariant {Γ : Ctx m} {φ : Formula m K}
    (h : UnitInvariant Γ φ) : PosUnitInvariant Γ φ :=
  fun t s ρ ht _ _ => h t ht s ρ

end Toy.Units
