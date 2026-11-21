# Unit-typed statements and invariance under changes of units: ratio scales, sign flips, affine offsets and total division in a Lean 4 toy model

## Summary

This package formalizes, in Lean 4 (`leanprover/lean4:v4.34.1`, core Lean, no Mathlib), a small first-order language of arithmetic statements about physical quantities whose variables and literals carry dimensions. It asks when such a statement holds or fails independently of the choice of units, and which conventions that independence silently depends on. The sixteen results fall into four groups: invariance of dimension-typed formulas under multiplicative unit changes, including changes with zero or negative factors (Results 1–8); offset scales such as degrees Celsius (Results 9–10); what an expression of dimension `L` can compute from a single length (Results 11–15); and the total-division convention `0⁻¹ = 0` (Result 16, which characterizes it; nine other results have a tightness witness showing that they fail without it).

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers. Comparisons with the documented behaviour of real libraries appear in Findings, "Modeling bridge to real systems", labelled `derived (modeling bridge)`, and are kept separate from the kernel-checked theorems.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

The plain-language claims, as recorded in `results.json` (a worked numerical instance attached to Results 5 and 9 is given with those results under Findings):

1. **`plain_reading_iff_pos_unit_invariant`** (`hasPlainReading_iff_posUnitInvariant`). For every scalar type `K` with the operations `ScalarOps K` and no law assumed, every context `Γ` and every formula `φ`: `φ` has a plain reading (`HasPlainReading Γ φ`: some predicate `R` on the quotient, by positive unit-change steps `unitChangeStep Γ`, of the situations `PosSituation m K` — pairs of a unit system `s : Fin m → K` with positive factors and readings `ρ` — satisfies `Formula.holdsIn s ρ φ ↔ R (Quot.mk _ p)` for every situation `p = ⟨(s, ρ), _⟩`) if and only if `φ` keeps its truth value under every positive unit change between unit systems with positive factors (`PosUnitInvariant Γ φ`).
2. **`typed_expression_homogeneous_nonzero_scaling`** (`evalIn_act_eq_scaleOf_mul`). Assume the field laws (`FieldLaws K`) and the convention `0⁻¹ = 0` (`InvZeroLaw K`). For every context `Γ`, every expression `e` of dimension `d` (`HasDim Γ e d`), every unit change `t` whose factors are all nonzero, every unit system `s : Fin m → K` (including systems with zero or negative factors) and all readings `ρ`: the reading of `e` in the system `fun i => t i * s i` with the transformed readings `actEnv Γ t ρ` equals `scaleOf t d` times the reading of `e` in `s` with `ρ`.
3. **`well_typed_formula_unit_invariant`** (`unitInvariant_of_wellTyped`). Assume the ordered-field laws (`OrderedFieldLaws K`) and `0⁻¹ = 0` (`InvZeroLaw K`). Every formula that is well typed in context `Γ` (`WellTyped Γ φ`: atoms `≤` and `=` between expressions of one dimension, `∧`, `∨`, `¬`, and `∀`/`∃` over a variable of a declared dimension ranging over all of `K`) keeps its truth value under every positive multiplicative (ratio-scale) unit change `t`, applied to every base unit system `s : Fin m → K` (including systems with zero or negative factors) and all readings (`UnitInvariant Γ φ`).
4. **`order_preserving_unit_change_preserves_typed_formulas`** (`invariantAt_of_wellTypedAt`). Assume the field laws (`FieldLaws K`; no order law) and `0⁻¹ = 0`. Let `t` be a unit change whose factors are all nonzero, and `O` a set of dimensions such that for every `d` with `O d`, multiplication by `scaleOf t d` preserves and reflects `≤` (`∀ a b, scaleOf t d * a ≤ scaleOf t d * b ↔ a ≤ b`). Then every formula that is well typed with order atoms at dimensions in `O` (`WellTypedAt O Γ φ`) keeps its truth value under `t`, applied to every base unit system (including systems with zero or negative factors) and all readings (`InvariantAt Γ t φ`).
5. **`untyped_reading_unit_dependent`** (`sumMixed_not_wellTyped_not_posUnitInvariant`). The formula `sumMixed`, `x + x * x ≤ 2` with `x` a length and the literal `2` dimensionless (a length added to an area, compared with a number), is not well typed (`¬ WellTyped ctxL sumMixed`), and it is not invariant under positive unit changes between positive unit systems (`¬ PosUnitInvariant ctxL sumMixed`).
6. **`typing_sufficient_not_necessary`** (`cubeSum_not_wellTyped_unitInvariant`). The formula `cubeSum`, `x + x * x * x ≤ 0` with `x` a length (a length added to a cubed length), is not well typed, yet it keeps its truth value under every positive unit change from every base unit system (`UnitInvariant ctxL cubeSum`).
7. **`equality_only_formulas_tolerate_nonzero_scaling`** (`invariantAt_of_wellTypedAt_noOrder_of_ne_zero`). Assume the field laws (`FieldLaws K`; no order law) and `0⁻¹ = 0`. For every unit change `t` whose factors are all nonzero (in an ordered field such factors may be negative), every formula that is well typed with no order atom (`WellTypedAt (fun _ => False) Γ φ`: dimension-typed `=` atoms, connectives and quantifiers) keeps its truth value under `t`, applied to every base unit system (including systems with zero or negative factors) and all readings (`InvariantAt Γ t φ`).
8. **`order_atoms_preserved_iff_scale_factor_positive`** (`invariantAt_all_wellTypedAt_iff`). Assume the ordered-field laws and `0⁻¹ = 0`, and let `t` be a unit change whose factors are all nonzero. For every set `O` of dimensions: `t` preserves the truth value of every formula that is well typed with order atoms at dimensions in `O` (`∀ Γ φ, WellTypedAt O Γ φ → InvariantAt Γ t φ`) if and only if the scale factor of every such dimension is positive (`∀ d, O d → 0 < scaleOf t d`). The condition is on `scaleOf t d = ∏ i, t i ^ d i` for `d ∈ O`, not on the base factors `t i`.
9. **`offset_units_dimension_check_overclaims`** (`sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant`). In the affine toy with all variables temperature readings (points, `sortsPt`), the formula `sumTemps` (`t₁ + t₂ ≤ t₃`) passes plain dimension checking (`ADimCheckedF sortsPt sumTemps`), is rejected by the point/vector discipline (`¬ PointVectorTyped WeightsSumOne sortsPt sumTemps`), and is not invariant under positive affine scale changes between scales with positive factor (`¬ PosAffineInvariant sortsPt sumTemps`).
10. **`point_vector_typed_formulas_affine_invariant`** (`affineInvariant_of_pointVectorTyped`). Assume the ordered-field laws and `0⁻¹ = 0`. Every formula typed by the point/vector discipline with weights summing to one (`PointVectorTyped WeightsSumOne S φ`: point − point, point ± vector and vector + point, vector-space operations, ratios of vectors, number arithmetic, binary affine combinations `w₁ * p + w₂ * q` of points with constant weights `w₁ + w₂ = 1`, comparisons within one sort, connectives, and quantifiers over a sort) keeps its truth value under every scale change `x ↦ a * x + b` with `a > 0`, applied to every scale `u` (including scales with `u.1 ≤ 0`) and all readings (`AffineInvariant S φ`).
11. **`one_var_length_polynomial_linear_everywhere`** (`oneVarLength_poly_eval_eq_mul`). Assume the commutative-ring laws (`CommRingLaws K`; no inverse law, no order law, no `0⁻¹` convention). For every context `Γ`, variable `x` and expression `e` such that `e` has dimension `L` (`HasDim Γ e L`), mentions no variable other than `x` (`e.onlyVar x`), has dimensionless literals (`e.dimlessLits`) and is polynomial (`e.isPolynomial`: no division, no negative power), for every unit system `s`, all readings `ρ` and every reading `v` of `x`: the reading of `e` at `x = v` equals its reading at `x = 1` times `v`.
12. **`one_var_length_rational_linear_everywhere`** (`oneVarLength_eval_eq_mul`). Assume the field laws (`FieldLaws K`; no order law) and `0⁻¹ = 0` (`InvZeroLaw K`). For every one-variable expression of dimension `L` in a length variable `x` with dimensionless literals (`OneVarLength Γ x e`: `Γ x = L`, `HasDim Γ e L`, `e.onlyVar x`, `e.dimlessLits`), every unit system `s`, all readings `ρ` and every reading `v` of `x` (zero included; in an ordered field, negative readings included): the reading of `e` at `x = v` equals its reading at `x = 1` times `v`.
13. **`definable_on_positive_iff_linear`** (`definableOnPos_iff`). Assume the ordered-field laws and `0⁻¹ = 0`. A function `f : K → K` is definable on positive readings (`DefinableOnPos f`: for some context `Γ`, variable `x` with `Γ x = L` and expression `e` of dimension `L`, the reading of `e` at `x = v` equals `f v` for every `v > 0`, every unit system `s` and all readings `ρ` of the other variables) if and only if there is a constant `c` with `f v = c * v` for every `v > 0`.
14. **`succ_not_definable_on_positive`** (`not_definableOnPos_add_one`). Assume the ordered-field laws and `0⁻¹ = 0`. The function `v ↦ v + 1` is not definable on positive readings (`¬ DefinableOnPos (fun v => v + 1)`): no expression of dimension `L` in a length variable computes `v + 1` at every positive reading `v`, in every unit system and for all readings of the other variables.
15. **`max_one_not_definable_on_positive`** (`not_definableOnPos_max_one`). Over `Rat` (which satisfies the ordered-field laws and `0⁻¹ = 0`), the function `v ↦ max v 1` is not definable on positive readings (`¬ DefinableOnPos (fun v : Rat => max v 1)`): no expression of dimension `L` in a length variable computes `max v 1` at every positive reading `v`, in every unit system and for all readings of the other variables.
16. **`inv_zero_convention_iff_typed_homogeneity`** (`allHomogeneous_iff_invZero`). Assume the field laws (`FieldLaws K`) and that `K` has an element `a` with `a ≠ 0` and `a ≠ 1`. With at least one base dimension (`m + 1` base dimensions), every well-typed expression is homogeneous under every unit change with nonzero factors (`AllHomogeneous (m + 1) K`: for every `Γ`, `e`, `d` with `HasDim Γ e d`, every `t` with nonzero factors, every unit system `s` and all readings `ρ`, the reading in `fun i => t i * s i` with `actEnv Γ t ρ` equals `scaleOf t d` times the reading in `s` with `ρ`) if and only if the total division returns `0` at a zero denominator (`InvZeroLaw K`).

Each result's hypothesis ledger (with a Lean counterexample for every hypothesis marked `tight`), non-vacuity witness and prior art are under Findings. Its non-claims are under Boundaries, "Non-claims of Result N"; they record what the result does not show, including stronger readings that are refuted or left open.

## Applicability

### What the model is

The definitions form a toy model in the Lean namespace `Toy.Units`, built as the Lake library `ToyUnits` (modules `Scalar`, `Algebra`, `Syntax`, `Inversion`, `PlainReading`, `Homogeneity`, `Instances`, `Counterexamples`, `Affine`, `AffineExamples`, `FreeTheorem`, `Examples`, `Tightness`, `ZeroInverse`) in the package directory `lean/`. They are meant to capture three things that unit checkers and measurement theory reason about informally:

- **Dimension checking under changes of units.** Arithmetic statements (`Expr`, `Formula`) over quantities read in one coherent unit system `s : Fin m → K`, with `m` base dimensions. A change of units `t` multiplies the reading of every quantity of dimension `d` by `scaleOf t d` (a ratio-scale change when the factors are positive). Dimension checking is `HasDim` for expressions and `WellTypedAt` / `WellTyped` for formulas.
- **Offset scales.** A separate affine toy (`AExpr`, `AFormula`) has one point dimension, such as temperature in °C or °F, whose admissible changes are `x ↦ a * x + b` with `a > 0` (an interval-scale change). Plain dimension checking (`ADimChecked`, `ADimCheckedF`) is compared with a point/vector discipline (`HasSort`, `PointVectorTyped`).
- **Total division.** Division is a total operation whose value at a zero denominator is the scalar domain's `0⁻¹`; the convention `0⁻¹ = 0` (`InvZeroLaw`) is kept out of every law bundle, so each theorem shows whether it needs it.

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers. No embedding, abstraction or simulation between the toy and any real system is proved, so no theorem transfers to a real system by itself.

### Known gaps between the model and real systems

- **One coherent unit system.** Every quantity of dimension `d` is read in the same unit and rescales by the same factor. There are no per-variable unit tags and no conversions between two units of one dimension (metres and feet, newton-seconds and pound-force seconds); a statement that mixes two units of one dimension cannot be expressed, so the model's dimension checking says nothing about it.
- **Syntax.** The language is first order: `+`, `-`, `*`, total `/`, integer powers, literals annotated with a dimension, atoms `≤` and `=`, connectives, and quantifiers over a variable of a declared dimension. Absolute value, roots, transcendental functions, conditionals, `max` and higher-order functions are absent.
- **Exact scalars.** Readings are elements of an abstract scalar type `K` with the operations `ScalarOps K`; every algebraic or order law used is an explicit hypothesis. Rounding, floating point and measurement error are outside the model.
- **Quantifier domains.** Quantifiers range over all of `K`. Bounded or discrete quantity domains (integers, intervals) and physical bounds such as absolute zero are not modeled.
- **Literal annotations are trusted.** A literal written without its unit is modeled as a literal of dimension `Dim.one`; a mis-annotated literal gives a different formula, which may be well typed and invariant while meaning something else.
- **Affine toy.** One point dimension, binary affine combinations of points with constant weights, and no products of temperature differences with other dimensions (such as `J / K`).
- **One-variable results.** Results 11–15 concern one base dimension (`Fin 1`) and expressions in a single length variable; Results 13–15 constrain positive readings `v > 0`.

### Scalar domains used as witnesses

Theorems are generic in the scalar type `K`. Concrete witnesses use Lean core `Rat` (which satisfies the ordered-field laws and `0⁻¹ = 0`: `ratLaws`, `ratInvZero`); `RatJ`, which is `Rat` with the single change `0⁻¹ := 1` (`ratJLaws`, `ratJ_not_invZero`); the two-element field `GF2` (field laws and `0⁻¹ = 0`, no ordered-field laws: `gf2_fieldLaws`, `gf2_invZero`, `gf2_not_orderedFieldLaws`); `GF2J`, which is `GF2` with `0⁻¹ := 1` (`gf2J_fieldLaws`, `gf2J_not_invZero`); and integer operations with `inv _ := 0` (`intOps`, `intOps_not_mulInv`). They test whether a result needs `InvZeroLaw`, an order, or the inverse law.

### Statement conventions

A unit system `s : Fin m → K` gives, per base dimension, the factor by which readings in `s` exceed readings in the reference units. Two invariance notions are used and kept apart by name: `UnitInvariant` and `InvariantAt` quantify over every base unit system `s : Fin m → K`, including systems with zero or negative factors (the stronger notion, used in the positive results); `PosUnitInvariant` quantifies over unit systems with positive factors and leaves out base systems with a zero or negative factor (the physically meaningful notion, used in the plain-reading result and in the counterexamples). `UnitInvariant` implies `PosUnitInvariant` (`posUnitInvariant_of_unitInvariant`) and not conversely (`posConstFormula_posUnitInvariant_not_unitInvariant`). The affine toy has the same split (`AffineInvariant` versus `PosAffineInvariant`). Division is total; its value at a zero denominator is the domain's `0⁻¹`. No truncating operation occurs in any definition: scalar division is the domain's total division, the `Rat` arithmetic of the witnesses is exact, and dimensions are integer exponent vectors, so `Dim.div` uses integer subtraction.

### Toolchain

Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean only: no Std import, no Mathlib, and no `[[require]]` in `lean/lakefile.toml`. Citations of the form `-- ToyUnits/File.lean:A-B` in this report are relative to `lean/`.

### Subjects and how they relate

`REPORT.json` lists three kinds of subject, which play different roles:

- **The Lean 4 toolchain** checks every theorem; it is the source of all `execution (Lean kernel check)` evidence.
- **Prior work** that results of this package restate or relate to: Atkey–Johann–Kennedy 2013 (paper source read at a pinned commit of the authors' repository), Kennedy 1997 (bibliographic record only; its content is taken from the description in Atkey–Johann–Kennedy 2013), Stevens 1946 and Luce 1959 (bibliographic records and content summaries verified through a search index; full texts not retrieved), and Allen 2026 (arXiv abstract read). None of their formal systems is compared with the toy by a proved relation.
- **Real unit libraries**, Pint 0.26.2 and mp-units v2.5.0, enter the report through their documentation at pinned commits, which the modeling-bridge remarks compare with the toy. No library code was run or compiled, and no statement is made about library behaviour beyond what the cited documentation says.

Further sources cited for context are listed under Evidence, "Primary sources", each with the level at which it was verified.

## Findings

Basis: execution (Lean kernel check) for every theorem quoted in this section. Every Lean block is one of two kinds. Most are verbatim quotations of the package source, opened by a comment giving the file and line range, with proofs elided as `…`. The others are introduced as unfolded renderings of one side of a quoted theorem: each is a Lean term that elaborates in that theorem's context and is definitionally equal to the side it renders. The remarks under "Modeling bridge to real systems" are `derived (modeling bridge)` and are not kernel-checked.

How to read a result. Tiers: `T0` is a known result restated in this vocabulary; `T1` is folklore made precise (known informally or in another formalism; no novelty is claimed). Depth: `definitional` (the proof unfolds definitions), `shallow` (a short argument from the definitions), `substantive` (none here). In a hypothesis ledger, `tight: counterexample X (…)` means that the Lean theorem `X`, quoted with the result, exhibits an instance of the stated kind in which every other hypothesis holds and the conclusion fails; `harmless` means that every structure of the intended kind satisfies the hypothesis. A non-vacuity witness is a Lean theorem stating that all hypotheses hold together in a concrete instance; a positive control (for impossibility results) is a nearby setting where the conclusion fails.

### Definitions (verbatim) with examples

Each core definition is quoted verbatim, followed by a sentence on what it is meant to capture and by proved examples, positive and negative, that test it.

#### Scalars: operations as data, laws as named propositions (`Scalar.lean`, `Instances.lean`)

```lean
-- ToyUnits/Scalar.lean:14
class ScalarOps (K : Type) extends Zero K, One K, Add K, Mul K, Neg K, Inv K, LE K, LT K
```

```lean
-- ToyUnits/Scalar.lean:16
instance instScalarOpsRat : ScalarOps Rat where
```

```lean
-- ToyUnits/Scalar.lean:42
def InvZeroLaw : Prop := (0 : K)⁻¹ = 0
```

```lean
-- ToyUnits/Scalar.lean:38
def MulInvLaw : Prop := ∀ a : K, a ≠ 0 → a * a⁻¹ = 1
```

```lean
-- ToyUnits/Scalar.lean:59-67
structure CommRingLaws : Prop where
  add_assoc : AddAssocLaw K
  add_comm : AddCommLaw K
  add_zero : AddZeroLaw K
  add_neg : AddNegLaw K
  mul_assoc : MulAssocLaw K
  mul_comm : MulCommLaw K
  mul_one : MulOneLaw K
  distrib : DistribLaw K
```

```lean
-- ToyUnits/Scalar.lean:70-72
structure FieldLaws : Prop extends CommRingLaws K where
  mul_inv : MulInvLaw K
  zero_ne_one : ZeroNeOneLaw K
```

```lean
-- ToyUnits/Scalar.lean:75-82
structure OrderedFieldLaws : Prop extends FieldLaws K where
  le_refl : LeReflLaw K
  le_trans : LeTransLaw K
  le_antisymm : LeAntisymmLaw K
  le_total : LeTotalLaw K
  lt_iff : LtIffLaw K
  add_le_mono : AddLeMonoLaw K
  mul_nonneg : MulNonnegLaw K
```

Captures: an ordered field whose every law is an explicit hypothesis. The convention `0⁻¹ = 0` (`InvZeroLaw`) is kept outside every bundle, so each theorem shows whether it needs it. The remaining law propositions (`AddAssocLaw`, `AddCommLaw`, `AddZeroLaw`, `AddNegLaw`, `MulAssocLaw`, `MulCommLaw`, `MulOneLaw`, `DistribLaw`, `ZeroNeOneLaw`, `LeReflLaw`, `LeTransLaw`, `LeAntisymmLaw`, `LeTotalLaw`, `LtIffLaw`, `AddLeMonoLaw`, `MulNonnegLaw`) are one-line statements of the usual axioms; they are quoted under "Auxiliary declarations cited by name (verbatim)" at the end of Findings. `RatJ` is `Rat` with the single change `0⁻¹ := 1`; `GF2` is the two-element field (with `0⁻¹ = 0`), and `GF2J` is `GF2` with `0⁻¹ := 1`. They test whether a result needs `InvZeroLaw` or an order.

Examples (all fully proved):

```lean
-- ToyUnits/Instances.lean:18
theorem ratLaws : OrderedFieldLaws Rat where
```

```lean
-- ToyUnits/Instances.lean:41
theorem ratInvZero : InvZeroLaw Rat := …
```

```lean
-- ToyUnits/Instances.lean:44
def RatJ : Type := Rat
```

```lean
-- ToyUnits/Instances.lean:47
def RatJ.ofRat (q : Rat) : RatJ := q
```

```lean
-- ToyUnits/Instances.lean:50
def RatJ.toRat (a : RatJ) : Rat := a
```

```lean
-- ToyUnits/Instances.lean:52-60
instance instScalarOpsRatJ : ScalarOps RatJ where
  zero := RatJ.ofRat 0
  one := RatJ.ofRat 1
  add a b := RatJ.ofRat (RatJ.toRat a + RatJ.toRat b)
  mul a b := RatJ.ofRat (RatJ.toRat a * RatJ.toRat b)
  neg a := RatJ.ofRat (-(RatJ.toRat a))
  inv a := RatJ.ofRat (if RatJ.toRat a = 0 then 1 else (RatJ.toRat a)⁻¹)
  le a b := RatJ.toRat a ≤ RatJ.toRat b
  lt a b := RatJ.toRat a < RatJ.toRat b
```

```lean
-- ToyUnits/Instances.lean:75
theorem ratJLaws : OrderedFieldLaws RatJ where
```

```lean
-- ToyUnits/Instances.lean:98
theorem ratJ_not_invZero : ¬ InvZeroLaw RatJ := …
```

```lean
-- ToyUnits/Instances.lean:106
def GF2 : Type := Bool
```

```lean
-- ToyUnits/Instances.lean:108-116
instance instScalarOpsGF2 : ScalarOps GF2 where
  zero := false
  one := true
  add a b := xor a b
  mul a b := a && b
  neg a := a
  inv a := a
  le _ _ := True
  lt _ _ := False
```

```lean
-- ToyUnits/Instances.lean:119
theorem gf2_fieldLaws : FieldLaws GF2 where
```

```lean
-- ToyUnits/Instances.lean:136
theorem gf2_invZero : InvZeroLaw GF2 := …
```

```lean
-- ToyUnits/Instances.lean:139
theorem gf2_one_add_one_eq_zero : (1 : GF2) + 1 = 0 := …
```

```lean
-- ToyUnits/Examples.lean:188
theorem gf2_not_orderedFieldLaws : ¬ OrderedFieldLaws GF2 := …
```

```lean
-- ToyUnits/Instances.lean:142
def GF2J : Type := Bool
```

```lean
-- ToyUnits/Instances.lean:144-152
instance instScalarOpsGF2J : ScalarOps GF2J where
  zero := false
  one := true
  add a b := xor a b
  mul a b := a && b
  neg a := a
  inv _ := true
  le _ _ := True
  lt _ _ := False
```

```lean
-- ToyUnits/Instances.lean:155
theorem gf2J_fieldLaws : FieldLaws GF2J where
```

```lean
-- ToyUnits/Instances.lean:172
theorem gf2J_not_invZero : ¬ InvZeroLaw GF2J := …
```

```lean
-- ToyUnits/Instances.lean:176
theorem gf2J_eq_zero_or_one (a : GF2J) : a = 0 ∨ a = 1 := …
```

```lean
-- ToyUnits/Examples.lean:39-40
@[instance_reducible] def intOps : ScalarOps Int where
  inv _ := 0
```

```lean
-- ToyUnits/Examples.lean:42
theorem intOps_not_mulInv : ¬ @MulInvLaw Int intOps := …
```

#### Powers and finite products (`Algebra.lean`)

```lean
-- ToyUnits/Algebra.lean:15-17
def npow (a : K) : Nat → K
  | 0 => 1
  | n + 1 => npow a n * a
```

```lean
-- ToyUnits/Algebra.lean:21-23
def zpow (a : K) : Int → K
  | .ofNat n => npow a n
  | .negSucc n => (npow a (n + 1))⁻¹
```

```lean
-- ToyUnits/Algebra.lean:26-28
def finProd : (n : Nat) → (Fin n → K) → K
  | 0, _ => 1
  | n + 1, f => f 0 * finProd n (fun i => f i.succ)
```

Captures: natural and integer powers and the product over `Fin n`. At base `0` and a negative exponent, `zpow` returns `0⁻¹`, i.e. whatever the domain's inverse returns at `0`.

#### Dimensions (`Syntax.lean`, `Instances.lean`)

```lean
-- ToyUnits/Syntax.lean:19
abbrev Dim (m : Nat) := Fin m → Int
```

```lean
-- ToyUnits/Syntax.lean:22
def Dim.one {m : Nat} : Dim m := fun _ => 0
```

```lean
-- ToyUnits/Syntax.lean:24
def Dim.mul {m : Nat} (d e : Dim m) : Dim m := fun i => d i + e i
```

```lean
-- ToyUnits/Syntax.lean:26
def Dim.div {m : Nat} (d e : Dim m) : Dim m := fun i => d i - e i
```

```lean
-- ToyUnits/Syntax.lean:28
def Dim.pow {m : Nat} (d : Dim m) (k : Int) : Dim m := fun i => k * d i
```

```lean
-- ToyUnits/Instances.lean:182
def L : Dim 1 := fun _ => 1
```

```lean
-- ToyUnits/Instances.lean:185
def ctxL : Ctx 1 := fun _ => L
```

Captures: a dimension as an integer exponent vector over `m` base dimensions; `L` is the length dimension when `m = 1`, and `ctxL` declares every variable a length.

Examples (all fully proved):

```lean
-- ToyUnits/Examples.lean:13
theorem dim_examples : Dim.mul L L 0 = 2 ∧ Dim.div L L = Dim.one := …
```

```lean
-- ToyUnits/Examples.lean:17
theorem dim_area_ne_length : Dim.mul L L ≠ L := …
```

#### Syntax, contexts, environments (`Syntax.lean`)

```lean
-- ToyUnits/Syntax.lean:31-38
inductive Expr (m : Nat) (K : Type) where
  | var (x : Nat)
  | lit (c : K) (d : Dim m)
  | add (e₁ e₂ : Expr m K)
  | sub (e₁ e₂ : Expr m K)
  | mul (e₁ e₂ : Expr m K)
  | div (e₁ e₂ : Expr m K)
  | zpow (e : Expr m K) (k : Int)
```

```lean
-- ToyUnits/Syntax.lean:41-48
inductive Formula (m : Nat) (K : Type) where
  | le (e₁ e₂ : Expr m K)
  | eq (e₁ e₂ : Expr m K)
  | and (φ ψ : Formula m K)
  | or (φ ψ : Formula m K)
  | not (φ : Formula m K)
  | all (x : Nat) (d : Dim m) (φ : Formula m K)
  | ex (x : Nat) (d : Dim m) (φ : Formula m K)
```

```lean
-- ToyUnits/Syntax.lean:51
abbrev Ctx (m : Nat) := Nat → Dim m
```

```lean
-- ToyUnits/Syntax.lean:54
abbrev Env (K : Type) := Nat → K
```

```lean
-- ToyUnits/Syntax.lean:57-58
def upd {α : Type} (f : Nat → α) (x : Nat) (v : α) : Nat → α :=
  fun y => if y = x then v else f y
```

Captures: arithmetic statements about quantities, with literals annotated by a dimension. A literal annotated `Dim.one` is a bare number, the representation of a literal written without its unit.

#### Dimension checking (`Syntax.lean`)

```lean
-- ToyUnits/Syntax.lean:64-76
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
```

```lean
-- ToyUnits/Syntax.lean:80-93
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
```

```lean
-- ToyUnits/Syntax.lean:96
def WellTyped (Γ : Ctx m) (φ : Formula m K) : Prop := WellTypedAt (fun _ => True) Γ φ
```

Captures: dimension checking for a first-order language in the style of Kennedy's dimension types. `WellTypedAt O` restricts order atoms to dimensions in `O`; `WellTyped` allows them everywhere. Dimension checking is relative to one coherent unit system; it does not track units of the same dimension separately.

Examples (all fully proved):

```lean
-- ToyUnits/Examples.lean:87
theorem hasDim_area_example : HasDim ctxL (Expr.mul (K := Rat) (.var 0) (.var 0)) (Dim.mul L L) := …
```

```lean
-- ToyUnits/Examples.lean:91-92
theorem hasDim_sumMixed_none (d : Dim 1) :
    ¬ HasDim ctxL (Expr.add (K := Rat) (.var 0) (.mul (.var 0) (.var 0))) d := …
```

```lean
-- ToyUnits/Examples.lean:81
theorem nonnegL_not_wellTypedAt_noOrder : ¬ WellTypedAt (fun _ => False) ctxL nonnegL := …
```

#### Raw readings (`Syntax.lean`)

```lean
-- ToyUnits/Syntax.lean:99
def scaleOf (s : Fin m → K) (d : Dim m) : K := finProd m (fun i => zpow (s i) (d i))
```

```lean
-- ToyUnits/Syntax.lean:103-110
def Expr.evalIn (s : Fin m → K) (ρ : Env K) : Expr m K → K
  | .var x => ρ x
  | .lit c d => scaleOf s d * c
  | .add e₁ e₂ => e₁.evalIn s ρ + e₂.evalIn s ρ
  | .sub e₁ e₂ => e₁.evalIn s ρ + -(e₂.evalIn s ρ)
  | .mul e₁ e₂ => e₁.evalIn s ρ * e₂.evalIn s ρ
  | .div e₁ e₂ => e₁.evalIn s ρ * (e₂.evalIn s ρ)⁻¹
  | .zpow e k => Toy.Units.zpow (e.evalIn s ρ) k
```

```lean
-- ToyUnits/Syntax.lean:113-120
def Formula.holdsIn (s : Fin m → K) : Env K → Formula m K → Prop
  | ρ, .le e₁ e₂ => e₁.evalIn s ρ ≤ e₂.evalIn s ρ
  | ρ, .eq e₁ e₂ => e₁.evalIn s ρ = e₂.evalIn s ρ
  | ρ, .and φ ψ => Formula.holdsIn s ρ φ ∧ Formula.holdsIn s ρ ψ
  | ρ, .or φ ψ => Formula.holdsIn s ρ φ ∨ Formula.holdsIn s ρ ψ
  | ρ, .not φ => ¬ Formula.holdsIn s ρ φ
  | ρ, .all x _ φ => ∀ v : K, Formula.holdsIn s (upd ρ x v) φ
  | ρ, .ex x _ φ => ∃ v : K, Formula.holdsIn s (upd ρ x v) φ
```

Captures: the raw reading evaluates the syntax over plain scalars, ignoring dimensions except that a literal `lit c d` (meaning `c` reference units of dimension `d`) reads as `scaleOf s d * c` in unit system `s`. Quantifiers range over all of `K`. Subtraction reads as `a + -b`, division as `a * b⁻¹` (total; its value at `0` is the domain's `0⁻¹`).

Examples (all fully proved):

```lean
-- ToyUnits/Examples.lean:22-24
theorem scaleOf_mm_examples :
    scaleOf (fun _ => (1000 : Rat)) L = 1000 ∧
      scaleOf (fun _ => (1000 : Rat)) (Dim.mul L L) = 1000000 := …
```

```lean
-- ToyUnits/Examples.lean:29
theorem scaleOf_area_ne_length : scaleOf (fun _ => (1000 : Rat)) (Dim.mul L L) ≠ 1000 := …
```

```lean
-- ToyUnits/Examples.lean:51-53
theorem evalIn_lit_examples (ρ : Env Rat) :
    (Expr.lit (3 : Rat) L).evalIn (fun _ => 1000) ρ = 3000 ∧
      (Expr.lit (3 : Rat) (Dim.one (m := 1))).evalIn (fun _ => 1000) ρ = 3 := …
```

#### Unit changes and invariance (`Syntax.lean`)

```lean
-- ToyUnits/Syntax.lean:124
def actEnv (Γ : Ctx m) (t : Fin m → K) (ρ : Env K) : Env K := fun x => scaleOf t (Γ x) * ρ x
```

```lean
-- ToyUnits/Syntax.lean:127
def Positive (t : Fin m → K) : Prop := ∀ i, 0 < t i
```

```lean
-- ToyUnits/Syntax.lean:131-133
def InvariantAt (Γ : Ctx m) (t : Fin m → K) (φ : Formula m K) : Prop :=
  ∀ (s : Fin m → K) (ρ : Env K),
    Formula.holdsIn (fun i => t i * s i) (actEnv Γ t ρ) φ ↔ Formula.holdsIn s ρ φ
```

```lean
-- ToyUnits/Syntax.lean:137-138
def UnitInvariant (Γ : Ctx m) (φ : Formula m K) : Prop :=
  ∀ t : Fin m → K, Positive t → InvariantAt Γ t φ
```

```lean
-- ToyUnits/Syntax.lean:143-145
def PosUnitInvariant (Γ : Ctx m) (φ : Formula m K) : Prop :=
  ∀ (t s : Fin m → K) (ρ : Env K), Positive t → Positive s → Positive (fun i => t i * s i) →
    (Formula.holdsIn (fun i => t i * s i) (actEnv Γ t ρ) φ ↔ Formula.holdsIn s ρ φ)
```

```lean
-- ToyUnits/Syntax.lean:148-149
theorem posUnitInvariant_of_unitInvariant {Γ : Ctx m} {φ : Formula m K}
    (h : UnitInvariant Γ φ) : PosUnitInvariant Γ φ := …
```

```lean
-- ToyUnits/Homogeneity.lean:64-68
theorem posUnitInvariant_iff_of_orderedField (h : OrderedFieldLaws K) (Γ : Ctx m)
    (φ : Formula m K) :
    PosUnitInvariant Γ φ ↔ ∀ t : Fin m → K, Positive t → ∀ s : Fin m → K, Positive s →
      ∀ ρ : Env K, (Formula.holdsIn (fun i => t i * s i) (actEnv Γ t ρ) φ ↔
        Formula.holdsIn s ρ φ) := …
```

Captures: a unit change `t` takes unit system `s` to `fun i => t i * s i` and multiplies the reading of a variable of dimension `d` by `scaleOf t d`. `InvariantAt Γ t φ` says `t` does not change the truth of `φ`, from every base unit system `s` (including systems with zero or negative factors); `UnitInvariant` asks this for every positive `t`. `PosUnitInvariant` asks it between unit systems with positive factors, leaving out base systems with a zero or negative factor. `UnitInvariant` is strictly stronger than `PosUnitInvariant` (`posConstFormula_posUnitInvariant_not_unitInvariant`).

Examples (all fully proved):

```lean
-- ToyUnits/Examples.lean:33-34
theorem positive_examples :
    Positive (m := 1) (fun _ => (1000 : Rat)) ∧ ¬ Positive (m := 1) (fun _ => (-1 : Rat)) := …
```

```lean
-- ToyUnits/Examples.lean:59
theorem actEnv_example : actEnv ctxL (fun _ => (1000 : Rat)) (fun _ => 3) 0 = 3000 := …
```

```lean
-- ToyUnits/Counterexamples.lean:285
def posConstFormula : Formula 1 Rat := .le (.add (.lit 1 L) (.lit 1 (Dim.mul L L))) (.lit 0 L)
```

```lean
-- ToyUnits/Counterexamples.lean:291-292
theorem posConstFormula_posUnitInvariant_not_unitInvariant :
    PosUnitInvariant ctxL posConstFormula ∧ ¬ UnitInvariant ctxL posConstFormula := …
```

#### Plain readings (`PlainReading.lean`)

```lean
-- ToyUnits/PlainReading.lean:18-19
abbrev PosSituation (m : Nat) (K : Type) [ScalarOps K] : Type :=
  {p : (Fin m → K) × Env K // Positive p.1}
```

```lean
-- ToyUnits/PlainReading.lean:22-23
def unitChangeStep (Γ : Ctx m) (p q : PosSituation m K) : Prop :=
  ∃ t : Fin m → K, Positive t ∧ q.1 = ((fun i => t i * p.1.1 i), actEnv Γ t p.1.2)
```

```lean
-- ToyUnits/PlainReading.lean:27-29
def HasPlainReading (Γ : Ctx m) (φ : Formula m K) : Prop :=
  ∃ R : Quot (unitChangeStep (K := K) Γ) → Prop,
    ∀ p : PosSituation m K, Formula.holdsIn p.1.1 p.1.2 φ ↔ R (Quot.mk _ p)
```

Captures: a statement 'about the quantities' is a predicate on physical situations, i.e. on the quotient of (positive unit system, readings) pairs by positive unit changes.

Examples (all fully proved):

```lean
-- ToyUnits/Examples.lean:63-66
theorem unitChangeStep_example (ρ : Env Rat) :
    unitChangeStep ctxL ⟨((fun _ => 1), ρ), fun _ => (by decide : (0 : Rat) < 1)⟩
      ⟨((fun i => (fun _ => (1000 : Rat)) i * (fun _ => (1 : Rat)) i),
        actEnv ctxL (fun _ => 1000) ρ), fun _ => (by grind : (0 : Rat) < 1000 * 1)⟩ := …
```

```lean
-- ToyUnits/Examples.lean:71-73
theorem unitChangeStep_readings_unchanged_not :
    ¬ unitChangeStep ctxL ⟨((fun _ => (1 : Rat)), fun _ => 1), fun _ => (by decide : (0 : Rat) < 1)⟩
      ⟨((fun _ => (2 : Rat)), fun _ => 1), fun _ => (by decide : (0 : Rat) < 2)⟩ := …
```

```lean
-- ToyUnits/Counterexamples.lean:274
theorem nonnegL_hasPlainReading : HasPlainReading ctxL nonnegL := …
```

```lean
-- ToyUnits/Counterexamples.lean:278
theorem sumMixed_no_plainReading : ¬ HasPlainReading ctxL sumMixed := …
```

#### Named formulas and expressions of the length instance (`Counterexamples.lean`, `Examples.lean`, `Tightness.lean`, `FreeTheorem.lean`)

```lean
-- ToyUnits/Counterexamples.lean:39
def sumMixed : Formula 1 Rat := .le (.add (.var 0) (.mul (.var 0) (.var 0))) (.lit 2 Dim.one)
```

```lean
-- ToyUnits/Counterexamples.lean:83
def dropUnitLe : Formula 1 Rat := .le (.var 0) (.lit 2 Dim.one)
```

```lean
-- ToyUnits/Counterexamples.lean:86
def unitLe : Formula 1 Rat := .le (.var 0) (.lit 2 L)
```

```lean
-- ToyUnits/Counterexamples.lean:110-111
def cubeSum : Formula 1 Rat :=
  .le (.add (.var 0) (.mul (.mul (.var 0) (.var 0)) (.var 0))) (.lit 0 L)
```

```lean
-- ToyUnits/Counterexamples.lean:171
def nonnegL : Formula 1 Rat := .le (.lit 0 L) (.var 0)
```

```lean
-- ToyUnits/Counterexamples.lean:187
def nonnegL2 : Formula 1 Rat := .le (.lit 0 (Dim.mul L L)) (.mul (.var 0) (.var 0))
```

```lean
-- ToyUnits/Counterexamples.lean:201
def eqXY : Formula 1 Rat := .eq (.var 0) (.var 1)
```

```lean
-- ToyUnits/Counterexamples.lean:216
def xTimesInvX : Expr 1 Rat := .mul (.var 0) (.div (.lit 1 Dim.one) (.var 0))
```

```lean
-- ToyUnits/Counterexamples.lean:242
def ctxDiv : Ctx 1 := fun x => if x = 2 then Dim.div L L else L
```

```lean
-- ToyUnits/Counterexamples.lean:245
def divLe : Formula 1 RatJ := .le (.div (.var 0) (.var 1)) (.var 2)
```

```lean
-- ToyUnits/Examples.lean:116
def quantL : Formula 1 Rat := .all 1 L (.or (.le (.var 0) (.var 1)) (.le (.var 1) (.var 0)))
```

```lean
-- ToyUnits/Tightness.lean:10
def xVar : Expr 1 Rat := .var 0
```

```lean
-- ToyUnits/Tightness.lean:29
def divXY : Expr 1 RatJ := .div (.var 0) (.var 1)
```

```lean
-- ToyUnits/Tightness.lean:50
def divEq : Formula 1 RatJ := .eq (.div (.var 0) (.var 1)) (.var 2)
```

```lean
-- ToyUnits/Tightness.lean:99
def twoVarSum : Expr 1 Rat := .add (.var 0) (.var 1)
```

```lean
-- ToyUnits/Tightness.lean:119
def ctxInvL : Ctx 1 := fun _ => Dim.div Dim.one L
```

```lean
-- ToyUnits/Tightness.lean:122
def invVar : Expr 1 Rat := .div (.lit 1 Dim.one) (.var 0)
```

```lean
-- ToyUnits/Tightness.lean:143
def invLLit : Expr 1 RatJ := .lit (RatJ.ofRat 1) (Dim.div Dim.one L)
```

```lean
-- ToyUnits/FreeTheorem.lean:452
def addOneLength : Expr 1 Rat := .add (.var 0) (.lit 1 L)
```

```lean
-- ToyUnits/FreeTheorem.lean:465
def addOneDimless : Expr 1 Rat := .add (.var 0) (.lit 1 Dim.one)
```

```lean
-- ToyUnits/FreeTheorem.lean:479
def sqOverZero : Expr 1 RatJ := .div (.mul (.var 0) (.var 0)) (.sub (.var 0) (.var 0))
```

Toy formulas used as witnesses. `ctxDiv` makes `z` (variable `2`) of dimension `L / L` so that `x / y ≤ z` is well typed. The expressions used as controls and counterexamples for the one-variable results (Results 11, 12 and 14) are `twoVarSum`, `x + y`; `invVar`, `1 / x` with a dimensionless literal, read in the context `ctxInvL`, which gives every variable dimension `1 / L`; `addOneLength`, `x` plus a literal `1` of dimension `L`; `addOneDimless`, `x` plus a dimensionless literal `1`; and `sqOverZero`, `x * x / (x - x)` over `RatJ`.

#### Affine (offset) toy (`Affine.lean`, `AffineExamples.lean`)

```lean
-- ToyUnits/Affine.lean:23-26
inductive ASort where
  | pt
  | vec
  | num
```

```lean
-- ToyUnits/Affine.lean:31-34
def ASort.act (g : K × K) : ASort → K → K
  | .pt, v => g.1 * v + g.2
  | .vec, v => g.1 * v
  | .num, v => v
```

```lean
-- ToyUnits/Affine.lean:37-40
def ASort.exp : ASort → Int
  | .pt => 1
  | .vec => 1
  | .num => 0
```

```lean
-- ToyUnits/Affine.lean:43-50
inductive AExpr (K : Type) where
  | var (x : Nat)
  | lit (c : K) (σ : ASort)
  | add (e₁ e₂ : AExpr K)
  | sub (e₁ e₂ : AExpr K)
  | mul (e₁ e₂ : AExpr K)
  | div (e₁ e₂ : AExpr K)
  | comb (w₁ : K) (e₁ : AExpr K) (w₂ : K) (e₂ : AExpr K)
```

```lean
-- ToyUnits/Affine.lean:53-60
inductive AFormula (K : Type) where
  | le (e₁ e₂ : AExpr K)
  | eq (e₁ e₂ : AExpr K)
  | and (φ ψ : AFormula K)
  | or (φ ψ : AFormula K)
  | not (φ : AFormula K)
  | all (x : Nat) (σ : ASort) (φ : AFormula K)
  | ex (x : Nat) (σ : ASort) (φ : AFormula K)
```

```lean
-- ToyUnits/Affine.lean:64-71
def AExpr.evalIn (u : K × K) (ρ : Env K) : AExpr K → K
  | .var x => ρ x
  | .lit c σ => σ.act u c
  | .add e₁ e₂ => e₁.evalIn u ρ + e₂.evalIn u ρ
  | .sub e₁ e₂ => e₁.evalIn u ρ + -(e₂.evalIn u ρ)
  | .mul e₁ e₂ => e₁.evalIn u ρ * e₂.evalIn u ρ
  | .div e₁ e₂ => e₁.evalIn u ρ * (e₂.evalIn u ρ)⁻¹
  | .comb w₁ e₁ w₂ e₂ => w₁ * e₁.evalIn u ρ + w₂ * e₂.evalIn u ρ
```

```lean
-- ToyUnits/Affine.lean:74-81
def AFormula.holdsIn (u : K × K) : Env K → AFormula K → Prop
  | ρ, .le e₁ e₂ => e₁.evalIn u ρ ≤ e₂.evalIn u ρ
  | ρ, .eq e₁ e₂ => e₁.evalIn u ρ = e₂.evalIn u ρ
  | ρ, .and φ ψ => AFormula.holdsIn u ρ φ ∧ AFormula.holdsIn u ρ ψ
  | ρ, .or φ ψ => AFormula.holdsIn u ρ φ ∨ AFormula.holdsIn u ρ ψ
  | ρ, .not φ => ¬ AFormula.holdsIn u ρ φ
  | ρ, .all x _ φ => ∀ v : K, AFormula.holdsIn u (upd ρ x v) φ
  | ρ, .ex x _ φ => ∃ v : K, AFormula.holdsIn u (upd ρ x v) φ
```

```lean
-- ToyUnits/Affine.lean:84
def actA (S : Nat → ASort) (g : K × K) (ρ : Env K) : Env K := fun x => (S x).act g (ρ x)
```

```lean
-- ToyUnits/Affine.lean:89-91
def AffineInvariant (S : Nat → ASort) (φ : AFormula K) : Prop :=
  ∀ g : K × K, 0 < g.1 → ∀ (u : K × K) (ρ : Env K),
    AFormula.holdsIn (g.1 * u.1, g.1 * u.2 + g.2) (actA S g ρ) φ ↔ AFormula.holdsIn u ρ φ
```

```lean
-- ToyUnits/Affine.lean:96-98
def PosAffineInvariant (S : Nat → ASort) (φ : AFormula K) : Prop :=
  ∀ (g u : K × K) (ρ : Env K), 0 < g.1 → 0 < u.1 → 0 < g.1 * u.1 →
    (AFormula.holdsIn (g.1 * u.1, g.1 * u.2 + g.2) (actA S g ρ) φ ↔ AFormula.holdsIn u ρ φ)
```

```lean
-- ToyUnits/Affine.lean:101-102
theorem posAffineInvariant_of_affineInvariant {S : Nat → ASort} {φ : AFormula K}
    (h : AffineInvariant S φ) : PosAffineInvariant S φ := …
```

```lean
-- ToyUnits/Affine.lean:107-119
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
```

```lean
-- ToyUnits/Affine.lean:122-135
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
```

```lean
-- ToyUnits/Affine.lean:139-171
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
```

```lean
-- ToyUnits/Affine.lean:174-187
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
```

```lean
-- ToyUnits/Affine.lean:190
def WeightsSumOne (w₁ w₂ : K) : Prop := w₁ + w₂ = 1
```

Captures: one point dimension (temperature), modelled as an ordered one-dimensional affine space over the scalars (an interval scale): the admissible changes are `x ↦ a * x + b` with `a > 0` (positive scaling and translation). A scale `u = (a, b)` reads a reference point reading `c` as `a * c + b`, a difference as `a * c`, a number as `c`. A point literal `lit c .pt` denotes a fixed reference point (for example `0 °C` reads `273.15` in kelvin and `32` in °F), not the numeral `c` in every scale. `ADimChecked` is plain dimension checking (points and differences both have exponent `1`); `HasSort`/`PointVectorTyped` is the point/vector discipline, with binary affine combinations `comb w₁ e₁ w₂ e₂` of points whose constant weights satisfy the side condition `W`.

Examples (all fully proved):

```lean
-- ToyUnits/AffineExamples.lean:14
def celsius : Rat × Rat := (1, 0)
```

```lean
-- ToyUnits/AffineExamples.lean:16
def celsiusToKelvin : Rat × Rat := (1, 5463 / 20)
```

```lean
-- ToyUnits/AffineExamples.lean:18
def celsiusToFahrenheit : Rat × Rat := (9 / 5, 32)
```

```lean
-- ToyUnits/AffineExamples.lean:21
def sortsPt : Nat → ASort := fun _ => .pt
```

```lean
-- ToyUnits/AffineExamples.lean:30-32
theorem act_examples :
    ASort.pt.act celsiusToKelvin 20 = 5863 / 20 ∧ ASort.vec.act celsiusToKelvin 5 = 5 ∧
      ASort.pt.act celsiusToFahrenheit 100 = 212 := …
```

```lean
-- ToyUnits/AffineExamples.lean:37
theorem act_vec_no_offset : ASort.vec.act celsiusToKelvin 5 ≠ 5 + 5463 / 20 := …
```

```lean
-- ToyUnits/AffineExamples.lean:41-42
theorem weightsSumOne_examples :
    WeightsSumOne (1 / 2 : Rat) (1 / 2) ∧ ¬ WeightsSumOne (1 : Rat) 1 := …
```

```lean
-- ToyUnits/AffineExamples.lean:46-47
theorem hasSort_ptSubPt_example :
    HasSort (WeightsSumOne (K := Rat)) sortsPt (.sub (.var 0) (.var 1)) .vec := …
```

```lean
-- ToyUnits/AffineExamples.lean:51-52
theorem hasSort_sum_none (σ : ASort) :
    ¬ HasSort (WeightsSumOne (K := Rat)) sortsPt (.add (.var 0) (.var 1)) σ := …
```

```lean
-- ToyUnits/AffineExamples.lean:61-62
theorem aDimChecked_sum_example :
    ADimChecked (K := Rat) sortsPt (.add (.var 0) (.var 1)) 1 := …
```

```lean
-- ToyUnits/AffineExamples.lean:65-66
theorem aDimChecked_mixed_none (k : Int) :
    ¬ ADimChecked (K := Rat) sortsPt (.add (.var 0) (.lit 1 .num)) k := …
```

#### Named formulas of the affine toy

```lean
-- ToyUnits/AffineExamples.lean:74
def sumTemps : AFormula Rat := .le (.add (.var 0) (.var 1)) (.var 2)
```

```lean
-- ToyUnits/AffineExamples.lean:85
def sumTempsEnv : Env Rat := fun x => if x = 2 then 0 else -10
```

```lean
-- ToyUnits/AffineExamples.lean:130
def meanLe : AFormula Rat := .le (.comb (1 / 2) (.var 0) (1 / 2) (.var 1)) (.var 2)
```

```lean
-- ToyUnits/AffineExamples.lean:138
def ptLe : AFormula Rat := .le (.var 0) (.var 1)
```

```lean
-- ToyUnits/AffineExamples.lean:156
def combSumLe : AFormula Rat := .le (.comb 1 (.var 0) 1 (.var 1)) (.var 2)
```

```lean
-- ToyUnits/AffineExamples.lean:175-176
def ratioLe : AFormula RatJ :=
  .le (.div (.sub (.var 0) (.var 1)) (.sub (.var 2) (.var 2))) (.lit 1 .num)
```

```lean
-- ToyUnits/Examples.lean:155
def quantPt : AFormula Rat := .all 1 .pt (.or (.le (.var 0) (.var 1)) (.le (.var 1) (.var 0)))
```

```lean
-- ToyUnits/AffineExamples.lean:201-202
def affPosConst : AFormula Rat :=
  .le (.add (.lit 1 .vec) (.mul (.lit 1 .vec) (.lit 1 .vec))) (.lit 0 .vec)
```

Toy formulas used as witnesses.

#### One-variable expressions and definability (`FreeTheorem.lean`)

```lean
-- ToyUnits/FreeTheorem.lean:24-31
def Expr.onlyVar (x : Nat) : Expr m K → Prop
  | .var y => y = x
  | .lit _ _ => True
  | .add a b => a.onlyVar x ∧ b.onlyVar x
  | .sub a b => a.onlyVar x ∧ b.onlyVar x
  | .mul a b => a.onlyVar x ∧ b.onlyVar x
  | .div a b => a.onlyVar x ∧ b.onlyVar x
  | .zpow a _ => a.onlyVar x
```

```lean
-- ToyUnits/FreeTheorem.lean:34-41
def Expr.dimlessLits : Expr m K → Prop
  | .var _ => True
  | .lit _ d => d = Dim.one
  | .add a b => a.dimlessLits ∧ b.dimlessLits
  | .sub a b => a.dimlessLits ∧ b.dimlessLits
  | .mul a b => a.dimlessLits ∧ b.dimlessLits
  | .div a b => a.dimlessLits ∧ b.dimlessLits
  | .zpow a _ => a.dimlessLits
```

```lean
-- ToyUnits/FreeTheorem.lean:44-51
def Expr.isPolynomial : Expr m K → Prop
  | .var _ => True
  | .lit _ _ => True
  | .add a b => a.isPolynomial ∧ b.isPolynomial
  | .sub a b => a.isPolynomial ∧ b.isPolynomial
  | .mul a b => a.isPolynomial ∧ b.isPolynomial
  | .div _ _ => False
  | .zpow a k => 0 ≤ k ∧ a.isPolynomial
```

```lean
-- ToyUnits/FreeTheorem.lean:55-59
structure OneVarLength (Γ : Ctx 1) (x : Nat) (e : Expr 1 K) : Prop where
  ctx_x : Γ x = L
  typed : HasDim Γ e L
  only_x : e.onlyVar x
  dimless : e.dimlessLits
```

```lean
-- ToyUnits/FreeTheorem.lean:356-358
def DefinableOnPos (f : K → K) : Prop :=
  ∃ (Γ : Ctx 1) (x : Nat) (e : Expr 1 K), Γ x = L ∧ HasDim Γ e L ∧
    ∀ (s : Fin 1 → K) (ρ : Env K) (v : K), 0 < v → e.evalIn s (upd ρ x v) = f v
```

```lean
-- ToyUnits/FreeTheorem.lean:361
def linearWitness (c : K) : Expr 1 K := .mul (.lit c Dim.one) (.var 0)
```

Captures: the fragment of Kennedy's free theorem for a single length variable: expressions mentioning only `x`, with dimensionless literals, of dimension `L`. `DefinableOnPos f` asks for an expression of dimension `L` in a length variable `x` that computes `f` at every positive reading of `x`, in every unit system and for all readings of the other variables; it does not restrict the expression's other variables or literals, because the quantification over `s` and `ρ` already removes their influence.

Examples (all fully proved):

```lean
-- ToyUnits/Examples.lean:103
theorem addOneLength_not_oneVarLength : ¬ OneVarLength ctxL 0 addOneLength := …
```

```lean
-- ToyUnits/Examples.lean:107
theorem xTimesInvX_not_polynomial : ¬ xTimesInvX.isPolynomial := …
```

```lean
-- ToyUnits/Examples.lean:110
theorem definableOnPos_two_mul : DefinableOnPos (fun v : Rat => 2 * v) := …
```

```lean
-- ToyUnits/FreeTheorem.lean:446
theorem definableOnPos_max_zero : DefinableOnPos (fun v : Rat => max v 0) := …
```

#### Homogeneity of every typed expression (`ZeroInverse.lean`)

```lean
-- ToyUnits/ZeroInverse.lean:18-21
def AllHomogeneous (m : Nat) (K : Type) [ScalarOps K] : Prop :=
  ∀ (Γ : Ctx m) (e : Expr m K) (d : Dim m), HasDim Γ e d → ∀ t : Fin m → K, (∀ i, t i ≠ 0) →
    ∀ (s : Fin m → K) (ρ : Env K),
      Expr.evalIn (fun i => t i * s i) (actEnv Γ t ρ) e = scaleOf t d * Expr.evalIn s ρ e
```

```lean
-- ToyUnits/ZeroInverse.lean:24
def unitDim (m : Nat) : Dim (m + 1) := fun i => if i = 0 then 1 else 0
```

Captures: the property, for a scalar domain and a number of base dimensions, that every well-typed expression is homogeneous under every unit change with nonzero factors.

Examples (all fully proved):

```lean
-- ToyUnits/ZeroInverse.lean:70
theorem allHomogeneous_rat (m : Nat) : AllHomogeneous m Rat := …
```

```lean
-- ToyUnits/ZeroInverse.lean:74
theorem not_allHomogeneous_ratJ : ¬ AllHomogeneous 1 RatJ := …
```

### Results at a glance

| # | Result id | Lean name (`Toy.Units.` omitted) | Kind | Tier | Depth |
|---|---|---|---|---|---|
| 1 | `plain_reading_iff_pos_unit_invariant` | `hasPlainReading_iff_posUnitInvariant` | characterization | T0 | definitional |
| 2 | `typed_expression_homogeneous_nonzero_scaling` | `evalIn_act_eq_scaleOf_mul` | theorem | T0 | shallow |
| 3 | `well_typed_formula_unit_invariant` | `unitInvariant_of_wellTyped` | theorem | T0 | shallow |
| 4 | `order_preserving_unit_change_preserves_typed_formulas` | `invariantAt_of_wellTypedAt` | theorem | T1 | shallow |
| 5 | `untyped_reading_unit_dependent` | `sumMixed_not_wellTyped_not_posUnitInvariant` | counterexample | T0 | definitional |
| 6 | `typing_sufficient_not_necessary` | `cubeSum_not_wellTyped_unitInvariant` | counterexample | T1 | shallow |
| 7 | `equality_only_formulas_tolerate_nonzero_scaling` | `invariantAt_of_wellTypedAt_noOrder_of_ne_zero` | theorem | T1 | shallow |
| 8 | `order_atoms_preserved_iff_scale_factor_positive` | `invariantAt_all_wellTypedAt_iff` | characterization | T1 | shallow |
| 9 | `offset_units_dimension_check_overclaims` | `sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant` | counterexample | T0 | definitional |
| 10 | `point_vector_typed_formulas_affine_invariant` | `affineInvariant_of_pointVectorTyped` | theorem | T0 | shallow |
| 11 | `one_var_length_polynomial_linear_everywhere` | `oneVarLength_poly_eval_eq_mul` | theorem | T0 | shallow |
| 12 | `one_var_length_rational_linear_everywhere` | `oneVarLength_eval_eq_mul` | theorem | T0 | shallow |
| 13 | `definable_on_positive_iff_linear` | `definableOnPos_iff` | characterization | T0 | shallow |
| 14 | `succ_not_definable_on_positive` | `not_definableOnPos_add_one` | impossibility | T0 | shallow |
| 15 | `max_one_not_definable_on_positive` | `not_definableOnPos_max_one` | impossibility | T0 | shallow |
| 16 | `inv_zero_convention_iff_typed_homogeneity` | `allHomogeneous_iff_invZero` | characterization | T1 | shallow |

### Result 1. `plain_reading_iff_pos_unit_invariant`

**Plain claim.** For every scalar type `K` with the operations `ScalarOps K` and no law assumed, every context `Γ` and every formula `φ`: `φ` has a plain reading (`HasPlainReading Γ φ`: some predicate `R` on the quotient, by positive unit-change steps `unitChangeStep Γ`, of the situations `PosSituation m K` — pairs of a unit system `s : Fin m → K` with positive factors and readings `ρ` — satisfies `Formula.holdsIn s ρ φ ↔ R (Quot.mk _ p)` for every situation `p = ⟨(s, ρ), _⟩`) if and only if `φ` keeps its truth value under every positive unit change between unit systems with positive factors (`PosUnitInvariant Γ φ`).

**Kind / tier / depth.** characterization / T0 / definitional.

Basis: execution (Lean kernel check) of `hasPlainReading_iff_posUnitInvariant` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/PlainReading.lean:34-35
theorem hasPlainReading_iff_posUnitInvariant (Γ : Ctx m) (φ : Formula m K) :
    HasPlainReading Γ φ ↔ PosUnitInvariant Γ φ := …
```

Unfolded left side of `hasPlainReading_iff_posUnitInvariant` (definition `HasPlainReading` expanded):

```lean
∃ R : Quot (unitChangeStep (K := K) Γ) → Prop,
  ∀ p : PosSituation m K, Formula.holdsIn p.1.1 p.1.2 φ ↔ R (Quot.mk _ p)
```

Unfolded right side of `hasPlainReading_iff_posUnitInvariant` (definitions `PosUnitInvariant`, `Positive`, `actEnv` expanded):

```lean
∀ (t s : Fin m → K) (ρ : Env K), (∀ i, 0 < t i) → (∀ i, 0 < s i) → (∀ i, 0 < t i * s i) →
  (Formula.holdsIn (fun i => t i * s i) (fun x => scaleOf t (Γ x) * ρ x) φ ↔ Formula.holdsIn s ρ φ)
```

**Hypothesis ledger.**

No hypotheses (a closed statement about concrete instances, or a universal statement with no premise).

**Non-vacuity witness.** No hypotheses: the statement is universal. Both sides are realized: `nonnegL` has a plain reading (`nonnegL_hasPlainReading`), `sumMixed` has none (`sumMixed_no_plainReading`).

```lean
-- ToyUnits/Counterexamples.lean:274
theorem nonnegL_hasPlainReading : HasPlainReading ctxL nonnegL := …
```

```lean
-- ToyUnits/Counterexamples.lean:278
theorem sumMixed_no_plainReading : ¬ HasPlainReading ctxL sumMixed := …
```

**Remarks.**

- Reference point for the package: it fixes what 'independent of the choice of units' means in the toy. The premise `Positive (fun i => t i * s i)` of `PosUnitInvariant` follows from the other two under the ordered-field laws (`posUnitInvariant_iff_of_orderedField`); it is part of the definition so that the equivalence needs no law.

**Non-claims.** Listed under Boundaries, "Non-claims of Result 1"; read them together with the plain claim.

**Prior art.** Suppes–Zinnes 1963; Roberts 1979; Stevens 1946; Krantz–Luce–Suppes–Tversky 1971/1990; Buckingham 1914; Kennedy 1997. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** When does a numeric statement about physical quantities hold or fail independently of the choice of units? This result fixes the toy's meaning of that phrase (invariance under every positive unit change between positive unit systems), which is the measurement-theory notion of meaningfulness for ratio scales restated in the toy's vocabulary.

### Result 2. `typed_expression_homogeneous_nonzero_scaling`

**Plain claim.** Assume the field laws (`FieldLaws K`) and the convention `0⁻¹ = 0` (`InvZeroLaw K`). For every context `Γ`, every expression `e` of dimension `d` (`HasDim Γ e d`), every unit change `t` whose factors are all nonzero, every unit system `s : Fin m → K` (including systems with zero or negative factors) and all readings `ρ`: the reading of `e` in the system `fun i => t i * s i` with the transformed readings `actEnv Γ t ρ` equals `scaleOf t d` times the reading of `e` in `s` with `ρ`.

**Kind / tier / depth.** theorem / T0 / shallow.

Basis: execution (Lean kernel check) of `evalIn_act_eq_scaleOf_mul` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/Homogeneity.lean:75-78
theorem evalIn_act_eq_scaleOf_mul (h : FieldLaws K) (hz : InvZeroLaw K) {Γ : Ctx m}
    {e : Expr m K} {d : Dim m} (he : HasDim Γ e d) {t : Fin m → K} (ht : ∀ i, t i ≠ 0)
    (s : Fin m → K) (ρ : Env K) :
    Expr.evalIn (fun i => t i * s i) (actEnv Γ t ρ) e = scaleOf t d * Expr.evalIn s ρ e := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : FieldLaws K` | Algebra for sums, products, quotients and integer powers of scale factors. | harmless: every field satisfies it (`ratLaws` proves it for `Rat`, `gf2_fieldLaws` for `GF2`); tightness of the individual laws in the bundle is not examined |
| `hz : InvZeroLaw K` | The rescaled reading of a quotient involves `0⁻¹` when a denominator reads `0`, and so does a negative integer power of a zero reading and, in a base system with a zero factor, a literal of negative dimension (`invLLit_not_homogeneous_zero_system_ratJ`); the convention `0⁻¹ = 0` commutes with rescaling. | tight: counterexample `divXY_not_homogeneous_ratJ` (`RatJ` (every ordered-field law, `0⁻¹ = 1`), expression `x / y` at `y = 0`, positive reference system `s = 1`, `t = 2`) |
| `he : HasDim Γ e d` | Homogeneity is claimed at the dimension of `e`. | tight: counterexample `var_wrongDim_not_homogeneous` (`Rat`, the length variable `x` claimed at dimension `1`, `t = 2`) |
| `ht : ∀ i, t i ≠ 0` | Integer powers of scale factors must satisfy `zpow a (j + k) = zpow a j * zpow a k`. | tight: counterexample `xTimesInvX_not_homogeneous_zero` (`Rat`, expression `x * (1 / x)`, `t = 0`) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/Tightness.lean:33-41
theorem divXY_not_homogeneous_ratJ :
    FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ HasDim ctxL divXY (Dim.div L L) ∧
      (∀ i : Fin 1, (fun _ => RatJ.ofRat 2) i ≠ 0) ∧
      Expr.evalIn (fun i => (fun _ => RatJ.ofRat 2) i * (fun (_ : Fin 1) => (1 : RatJ)) i)
          (actEnv ctxL (fun _ => RatJ.ofRat 2)
            (fun x => if x = 1 then RatJ.ofRat 0 else RatJ.ofRat 1)) divXY ≠
        scaleOf (fun _ => RatJ.ofRat 2) (Dim.div L L) *
          Expr.evalIn (fun _ => 1) (fun x => if x = 1 then RatJ.ofRat 0 else RatJ.ofRat 1)
            divXY := …
```

```lean
-- ToyUnits/Tightness.lean:15-21
theorem var_wrongDim_not_homogeneous :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (2 : Rat)) i ≠ 0) ∧
      ¬ HasDim ctxL xVar Dim.one ∧
      Expr.evalIn (fun i => (fun _ => (2 : Rat)) i * (fun _ => (1 : Rat)) i)
          (actEnv ctxL (fun _ => 2) (fun _ => 1)) xVar ≠
        scaleOf (fun (_ : Fin 1) => (2 : Rat)) Dim.one *
          Expr.evalIn (fun _ => 1) (fun _ => 1) xVar := …
```

```lean
-- ToyUnits/Counterexamples.lean:224-230
theorem xTimesInvX_not_homogeneous_zero :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ HasDim ctxL xTimesInvX (Dim.mul L (Dim.div Dim.one L)) ∧
      ¬ (∀ i : Fin 1, (fun _ => (0 : Rat)) i ≠ 0) ∧
      Expr.evalIn (fun i => (fun _ => (0 : Rat)) i * (fun _ => (1 : Rat)) i)
          (actEnv ctxL (fun _ => 0) (fun _ => 1)) xTimesInvX ≠
        scaleOf (fun _ => (0 : Rat)) (Dim.mul L (Dim.div Dim.one L)) *
          Expr.evalIn (fun _ => 1) (fun _ => 1) xTimesInvX := …
```

**Non-vacuity witness.** `Rat` with `xTimesInvX` at dimension `L * (1 / L)` and `t = 2` (`nonvacuous_homogeneity`).

```lean
-- ToyUnits/Examples.lean:122-124
theorem nonvacuous_homogeneity :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ HasDim ctxL xTimesInvX (Dim.mul L (Dim.div Dim.one L)) ∧
      (∀ i : Fin 1, (fun _ => (2 : Rat)) i ≠ 0) := …
```

**Remarks.**

- Over a field with an element other than `0` and `1`, and with at least one base dimension, `hz` is necessary as well as sufficient for every typed expression to be homogeneous under every unit change with nonzero factors (`allHomogeneous_iff_invZero`).

**Non-claims.** Listed under Boundaries, "Non-claims of Result 2"; read them together with the plain claim.

**Prior art.** Kennedy 1997; Atkey–Johann–Kennedy 2013; Kennedy 2010; Allen 2026; Bobbin–Jones–Velkey–Josephson 2025; Foster–Wolff 2023; Botta–Jansson 2023/2026. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Which conventions (total division, sign of factors) the homogeneity of unit-typed arithmetic depends on.

### Result 3. `well_typed_formula_unit_invariant`

**Plain claim.** Assume the ordered-field laws (`OrderedFieldLaws K`) and `0⁻¹ = 0` (`InvZeroLaw K`). Every formula that is well typed in context `Γ` (`WellTyped Γ φ`: atoms `≤` and `=` between expressions of one dimension, `∧`, `∨`, `¬`, and `∀`/`∃` over a variable of a declared dimension ranging over all of `K`) keeps its truth value under every positive multiplicative (ratio-scale) unit change `t`, applied to every base unit system `s : Fin m → K` (including systems with zero or negative factors) and all readings (`UnitInvariant Γ φ`).

**Kind / tier / depth.** theorem / T0 / shallow.

Basis: execution (Lean kernel check) of `unitInvariant_of_wellTyped` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/Homogeneity.lean:160-161
theorem unitInvariant_of_wellTyped (h : OrderedFieldLaws K) (hz : InvZeroLaw K) {Γ : Ctx m}
    {φ : Formula m K} (hφ : WellTyped Γ φ) : UnitInvariant Γ φ := …
```

Unfolded conclusion of `unitInvariant_of_wellTyped` (definitions `UnitInvariant`, `Positive`, `InvariantAt`, `actEnv` expanded):

```lean
∀ t : Fin m → K, (∀ i, 0 < t i) → ∀ (s : Fin m → K) (ρ : Env K),
  Formula.holdsIn (fun i => t i * s i) (fun x => scaleOf t (Γ x) * ρ x) φ ↔ Formula.holdsIn s ρ φ
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : OrderedFieldLaws K` | Positivity of `scaleOf t d` (order atoms) and field algebra (homogeneity). | harmless: every ordered field satisfies it (`ratLaws` proves it for `Rat`); tightness of the individual laws in the bundle is not examined |
| `hz : InvZeroLaw K` | The homogeneity of the typed subexpressions (`evalIn_act_eq_scaleOf_mul`) needs it wherever `0⁻¹` enters a reading: a quotient whose denominator reads `0`, a negative integer power of a zero reading, and, in a base system with a zero factor, a literal of negative dimension (at expression level: `invLLit_not_homogeneous_zero_system_ratJ`); the convention `0⁻¹ = 0` commutes with rescaling. | tight: counterexample `divLe_not_unitInvariant_ratJ` (`RatJ` (every ordered-field law, `0⁻¹ = 1`), formula `x / y ≤ z` at `y = 0`, positive reference system `s = 1`, `t = 2`) |
| `hφ : WellTyped Γ φ` | Atoms compare expressions of one dimension. | tight: counterexample `sumMixed_wellTyped_tight` (`Rat`, formula `x + x * x ≤ 2`, positive reference system `s = 1`, `t = 2`) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/Counterexamples.lean:254-256
theorem divLe_not_unitInvariant_ratJ :
    OrderedFieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ WellTyped ctxDiv divLe ∧
      ¬ PosUnitInvariant ctxDiv divLe ∧ ¬ UnitInvariant ctxDiv divLe := …
```

```lean
-- ToyUnits/Counterexamples.lean:75-77
theorem sumMixed_wellTyped_tight :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ ¬ WellTyped ctxL sumMixed ∧
      ¬ UnitInvariant ctxL sumMixed := …
```

**Non-vacuity witness.** `Rat` with the quantified formula `quantL` (`∀ y : L, x ≤ y ∨ y ≤ x`) (`nonvacuous_unitInvariant_of_wellTyped`).

```lean
-- ToyUnits/Examples.lean:139-140
theorem nonvacuous_unitInvariant_of_wellTyped :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ WellTyped ctxL quantL := …
```

**Remarks.**

- `UnitInvariant` implies the positive-systems notion `PosUnitInvariant` (`posUnitInvariant_of_unitInvariant`), so well-typed formulas have plain readings (`hasPlainReading_iff_posUnitInvariant`).

**Non-claims.** Listed under Boundaries, "Non-claims of Result 3"; read them together with the plain claim.

**Prior art.** Kennedy 1997; Atkey–Johann–Kennedy 2013; Allen 2026; Suppes–Zinnes 1963; Roberts 1979. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Does unit-typed syntax guarantee that a statement holds or fails independently of the choice of units, and under which hidden conventions?

### Result 4. `order_preserving_unit_change_preserves_typed_formulas`

**Plain claim.** Assume the field laws (`FieldLaws K`; no order law) and `0⁻¹ = 0`. Let `t` be a unit change whose factors are all nonzero, and `O` a set of dimensions such that for every `d` with `O d`, multiplication by `scaleOf t d` preserves and reflects `≤` (`∀ a b, scaleOf t d * a ≤ scaleOf t d * b ↔ a ≤ b`). Then every formula that is well typed with order atoms at dimensions in `O` (`WellTypedAt O Γ φ`) keeps its truth value under `t`, applied to every base unit system (including systems with zero or negative factors) and all readings (`InvariantAt Γ t φ`).

**Kind / tier / depth.** theorem / T1 / shallow.

Basis: execution (Lean kernel check) of `invariantAt_of_wellTypedAt` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/Homogeneity.lean:108-111
theorem invariantAt_of_wellTypedAt (h : FieldLaws K) (hz : InvZeroLaw K) {O : Dim m → Prop}
    {t : Fin m → K} (ht : ∀ i, t i ≠ 0)
    (hO : ∀ d, O d → ∀ a b : K, scaleOf t d * a ≤ scaleOf t d * b ↔ a ≤ b)
    {Γ : Ctx m} {φ : Formula m K} (hφ : WellTypedAt O Γ φ) : InvariantAt Γ t φ := …
```

Unfolded conclusion of `invariantAt_of_wellTypedAt` (definitions `InvariantAt`, `actEnv` expanded):

```lean
∀ (s : Fin m → K) (ρ : Env K),
  Formula.holdsIn (fun i => t i * s i) (fun x => scaleOf t (Γ x) * ρ x) φ ↔ Formula.holdsIn s ρ φ
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : FieldLaws K` | Homogeneity of expressions; cancellation of a nonzero scale factor in `=` atoms; inverting `scaleOf t d` for quantifiers. | harmless: every field satisfies it (`ratLaws` proves it for `Rat`, `gf2_fieldLaws` for `GF2`); tightness of the individual laws in the bundle is not examined |
| `hz : InvZeroLaw K` | The homogeneity of the typed subexpressions (`evalIn_act_eq_scaleOf_mul`) needs it wherever `0⁻¹` enters a reading: a quotient whose denominator reads `0`, a negative integer power of a zero reading, and, in a base system with a zero factor, a literal of negative dimension (at expression level: `invLLit_not_homogeneous_zero_system_ratJ`); the convention `0⁻¹ = 0` commutes with rescaling. | tight: counterexample `divLe_engine_tight_ratJ` (`RatJ`, `t = 2`, order atoms at every dimension, formula `x / y ≤ z`) |
| `ht : ∀ i, t i ≠ 0` | Homogeneity, cancellation in `=` atoms, and surjectivity of rescaling for quantifiers. | tight: counterexample `eqXY_engine_tight_zero` (`Rat`, `t = 0`, no order atom, formula `x = y`) |
| `hO : ∀ d, O d → ∀ a b : K, scaleOf t d * a ≤ scaleOf t d * b ↔ a ≤ b` | The order condition: order atoms at dimension `d` keep their truth value. | tight: counterexample `nonnegL_engine_tight_neg_one` (`Rat`, `t = -1`, order atoms at every dimension, formula `0 ≤ x`) |
| `hφ : WellTypedAt O Γ φ` | Atoms compare expressions of one dimension; order atoms sit at dimensions in `O`. | tight: counterexample `sumMixed_engine_tight` (`Rat`, `t = 2`, order atoms at every dimension, formula `x + x * x ≤ 2`) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/Tightness.lean:265-271
theorem divLe_engine_tight_ratJ :
    FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧
      (∀ i : Fin 1, (fun _ => RatJ.ofRat 2) i ≠ 0) ∧
      (∀ d : Dim 1, (fun _ => True) d → ∀ a b : RatJ,
        scaleOf (fun _ => RatJ.ofRat 2) d * a ≤ scaleOf (fun _ => RatJ.ofRat 2) d * b ↔ a ≤ b) ∧
      WellTypedAt (fun _ => True) ctxDiv divLe ∧
      ¬ InvariantAt ctxDiv (fun _ => RatJ.ofRat 2) divLe := …
```

```lean
-- ToyUnits/Tightness.lean:289-293
theorem eqXY_engine_tight_zero :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ ¬ (∀ i : Fin 1, (fun _ => (0 : Rat)) i ≠ 0) ∧
      (∀ d : Dim 1, (fun _ => False) d → ∀ a b : Rat,
        scaleOf (fun _ => (0 : Rat)) d * a ≤ scaleOf (fun _ => (0 : Rat)) d * b ↔ a ≤ b) ∧
      WellTypedAt (fun _ => False) ctxL eqXY ∧ ¬ InvariantAt ctxL (fun _ => (0 : Rat)) eqXY := …
```

```lean
-- ToyUnits/Tightness.lean:300-305
theorem nonnegL_engine_tight_neg_one :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (-1 : Rat)) i ≠ 0) ∧
      ¬ (∀ d : Dim 1, (fun _ => True) d → ∀ a b : Rat,
        scaleOf (fun _ => (-1 : Rat)) d * a ≤ scaleOf (fun _ => (-1 : Rat)) d * b ↔ a ≤ b) ∧
      WellTypedAt (fun _ => True) ctxL nonnegL ∧
      ¬ InvariantAt ctxL (fun _ => (-1 : Rat)) nonnegL := …
```

```lean
-- ToyUnits/Tightness.lean:315-320
theorem sumMixed_engine_tight :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (2 : Rat)) i ≠ 0) ∧
      (∀ d : Dim 1, (fun _ => True) d → ∀ a b : Rat,
        scaleOf (fun _ => (2 : Rat)) d * a ≤ scaleOf (fun _ => (2 : Rat)) d * b ↔ a ≤ b) ∧
      ¬ WellTypedAt (fun _ => True) ctxL sumMixed ∧
      ¬ InvariantAt ctxL (fun _ => (2 : Rat)) sumMixed := …
```

**Non-vacuity witness.** `Rat`, `t = 2`, order atoms everywhere, the quantified formula `quantL` (`nonvacuous_engine`).

```lean
-- ToyUnits/Examples.lean:128-132
theorem nonvacuous_engine :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (2 : Rat)) i ≠ 0) ∧
      (∀ d : Dim 1, (fun _ => True) d → ∀ a b : Rat,
        scaleOf (fun _ => (2 : Rat)) d * a ≤ scaleOf (fun _ => (2 : Rat)) d * b ↔ a ≤ b) ∧
      WellTypedAt (fun _ => True) ctxL quantL := …
```

**Remarks.**

- Shared engine: `unitInvariant_of_wellTyped`, `invariantAt_of_wellTypedAt_noOrder_of_ne_zero` and `invariantAt_all_wellTypedAt_iff` are proved from it. No order law is assumed; the order condition on `scaleOf t d` is the hypothesis `hO`.

**Non-claims.** Listed under Boundaries, "Non-claims of Result 4"; read them together with the plain claim.

**Prior art.** Atkey–Johann–Kennedy 2013; Kennedy 1997. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Which unit changes, including sign or orientation flips of a base dimension, preserve which typed statements?

### Result 5. `untyped_reading_unit_dependent`

**Plain claim.** The formula `sumMixed`, `x + x * x ≤ 2` with `x` a length and the literal `2` dimensionless (a length added to an area, compared with a number), is not well typed (`¬ WellTyped ctxL sumMixed`), and it is not invariant under positive unit changes between positive unit systems (`¬ PosUnitInvariant ctxL sumMixed`). Explicitly (`sumMixed_flips`): with `x = 1` in the reference units it holds (`1 + 1 ≤ 2`); after the unit change `t = 2` it fails (`2 + 4 ≤ 2`).

**Kind / tier / depth.** counterexample / T0 / definitional.

Basis: execution (Lean kernel check) of `sumMixed_not_wellTyped_not_posUnitInvariant` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/Counterexamples.lean:64-65
theorem sumMixed_not_wellTyped_not_posUnitInvariant :
    ¬ WellTyped ctxL sumMixed ∧ ¬ PosUnitInvariant ctxL sumMixed := …
```

**Hypothesis ledger.**

No hypotheses (a closed statement about concrete instances, or a universal statement with no premise).

**Non-vacuity witness.** Counterexample result with no hypotheses; the concrete flip is `sumMixed_flips`.

```lean
-- ToyUnits/Counterexamples.lean:53-56
theorem sumMixed_flips :
    Formula.holdsIn (fun _ => (1 : Rat)) (fun _ => 1) sumMixed ∧
    ¬ Formula.holdsIn (fun i => (fun _ => (2 : Rat)) i * (fun _ => (1 : Rat)) i)
        (actEnv ctxL (fun _ => 2) (fun _ => 1)) sumMixed := …
```

**Remarks.**

- A second witness isolates a literal written without its unit: `x ≤ 2` with a dimensionless `2` is ill typed and not `PosUnitInvariant` (`dropUnitLe_not_wellTyped_not_posUnitInvariant`), while `x ≤ 2` with `2` annotated as a length is well typed (`unitLe_wellTyped`) and hence `UnitInvariant` by `unitInvariant_of_wellTyped`.

**Non-claims.** Listed under Boundaries, "Non-claims of Result 5"; read them together with the plain claim.

**Prior art.** Suppes–Zinnes 1963; Roberts 1979; Buckingham 1914. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Does a statement that combines quantities of different dimensions depend on the unit choice?

**Further declarations cited in this result (verbatim).**

```lean
-- ToyUnits/Counterexamples.lean:93-94
theorem dropUnitLe_not_wellTyped_not_posUnitInvariant :
    ¬ WellTyped ctxL dropUnitLe ∧ ¬ PosUnitInvariant ctxL dropUnitLe := …
```

```lean
-- ToyUnits/Counterexamples.lean:88
theorem unitLe_wellTyped : WellTyped ctxL unitLe := …
```

### Result 6. `typing_sufficient_not_necessary`

**Plain claim.** The formula `cubeSum`, `x + x * x * x ≤ 0` with `x` a length (a length added to a cubed length), is not well typed, yet it keeps its truth value under every positive unit change from every base unit system (`UnitInvariant ctxL cubeSum`).

**Kind / tier / depth.** counterexample / T1 / shallow.

Basis: execution (Lean kernel check) of `cubeSum_not_wellTyped_unitInvariant` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/Counterexamples.lean:154-155
theorem cubeSum_not_wellTyped_unitInvariant :
    ¬ WellTyped ctxL cubeSum ∧ UnitInvariant ctxL cubeSum := …
```

**Hypothesis ledger.**

No hypotheses (a closed statement about concrete instances, or a universal statement with no premise).

**Non-vacuity witness.** Counterexample result with no hypotheses; `cubeSum_not_wellTyped` and `cubeSum_unitInvariant` are its two parts.

```lean
-- ToyUnits/Counterexamples.lean:144
theorem cubeSum_unitInvariant : UnitInvariant ctxL cubeSum := …
```

**Non-claims.** Listed under Boundaries, "Non-claims of Result 6"; read them together with the plain claim.

**Prior art.** Kennedy 1997; Suppes–Zinnes 1963. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Is dimension checking a complete test for unit invariance, or only a sufficient one?

**Further declarations cited in this result (verbatim).**

```lean
-- ToyUnits/Counterexamples.lean:113
theorem cubeSum_not_wellTyped : ¬ WellTyped ctxL cubeSum := …
```

```lean
-- ToyUnits/Counterexamples.lean:126
theorem rat_add_cube_nonpos_iff (a : Rat) : a + a * a * a ≤ 0 ↔ a ≤ 0 := …
```

```lean
-- ToyUnits/Counterexamples.lean:160
theorem cubeSum_not_invariantAt_neg_one : ¬ InvariantAt ctxL (fun _ => (-1 : Rat)) cubeSum := …
```

### Result 7. `equality_only_formulas_tolerate_nonzero_scaling`

**Plain claim.** Assume the field laws (`FieldLaws K`; no order law) and `0⁻¹ = 0`. For every unit change `t` whose factors are all nonzero (in an ordered field such factors may be negative), every formula that is well typed with no order atom (`WellTypedAt (fun _ => False) Γ φ`: dimension-typed `=` atoms, connectives and quantifiers) keeps its truth value under `t`, applied to every base unit system (including systems with zero or negative factors) and all readings (`InvariantAt Γ t φ`).

**Kind / tier / depth.** theorem / T1 / shallow.

Basis: execution (Lean kernel check) of `invariantAt_of_wellTypedAt_noOrder_of_ne_zero` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/Homogeneity.lean:171-173
theorem invariantAt_of_wellTypedAt_noOrder_of_ne_zero (h : FieldLaws K) (hz : InvZeroLaw K)
    {t : Fin m → K} (ht : ∀ i, t i ≠ 0) {Γ : Ctx m} {φ : Formula m K}
    (hφ : WellTypedAt (fun _ => False) Γ φ) : InvariantAt Γ t φ := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : FieldLaws K` | Homogeneity; cancellation of a nonzero scale factor in `=` atoms; inverting scale factors for quantifiers. | harmless: every field satisfies it (`ratLaws` proves it for `Rat`, `gf2_fieldLaws` for `GF2`); tightness of the individual laws in the bundle is not examined |
| `hz : InvZeroLaw K` | The homogeneity of the typed subexpressions (`evalIn_act_eq_scaleOf_mul`) needs it wherever `0⁻¹` enters a reading: a quotient whose denominator reads `0`, a negative integer power of a zero reading, and, in a base system with a zero factor, a literal of negative dimension (at expression level: `invLLit_not_homogeneous_zero_system_ratJ`); the convention `0⁻¹ = 0` commutes with rescaling. | tight: counterexample `divEq_not_invariant_ratJ` (`RatJ`, formula `x / y = z` at `y = 0`, `t = 2`) |
| `ht : ∀ i, t i ≠ 0` | Cancellation in `=` atoms and surjectivity of rescaling. | tight: counterexample `eqXY_engine_tight_zero` (`Rat`, formula `x = y`, `t = 0`) |
| `hφ : WellTypedAt (fun _ => False) Γ φ` | Two requirements in one: every atom is dimension-typed, and no atom is an order atom. | tight: counterexample `nonnegL_noOrder_tight_neg_one` (`Rat`, formula `0 ≤ x` (an order atom), `t = -1`) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/Tightness.lean:54-57
theorem divEq_not_invariant_ratJ :
    FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ WellTypedAt (fun _ => False) ctxDiv divEq ∧
      (∀ i : Fin 1, (fun _ => RatJ.ofRat 2) i ≠ 0) ∧
      ¬ InvariantAt ctxDiv (fun _ => RatJ.ofRat 2) divEq := …
```

```lean
-- ToyUnits/Tightness.lean:289-293
theorem eqXY_engine_tight_zero :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ ¬ (∀ i : Fin 1, (fun _ => (0 : Rat)) i ≠ 0) ∧
      (∀ d : Dim 1, (fun _ => False) d → ∀ a b : Rat,
        scaleOf (fun _ => (0 : Rat)) d * a ≤ scaleOf (fun _ => (0 : Rat)) d * b ↔ a ≤ b) ∧
      WellTypedAt (fun _ => False) ctxL eqXY ∧ ¬ InvariantAt ctxL (fun _ => (0 : Rat)) eqXY := …
```

```lean
-- ToyUnits/Tightness.lean:329-332
theorem nonnegL_noOrder_tight_neg_one :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (-1 : Rat)) i ≠ 0) ∧
      ¬ WellTypedAt (fun _ => False) ctxL nonnegL ∧
      ¬ InvariantAt ctxL (fun _ => (-1 : Rat)) nonnegL := …
```

**Non-vacuity witness.** `Rat`, `t = -1`, formula `eqXY` (`nonvacuous_noOrder`).

```lean
-- ToyUnits/Examples.lean:144-146
theorem nonvacuous_noOrder :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (-1 : Rat)) i ≠ 0) ∧
      WellTypedAt (fun _ => False) ctxL eqXY := …
```

**Non-claims.** Listed under Boundaries, "Non-claims of Result 7"; read them together with the plain claim.

**Prior art.** Atkey–Johann–Kennedy 2013. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Do statements without order comparisons survive sign or orientation flips of a base dimension?

### Result 8. `order_atoms_preserved_iff_scale_factor_positive`

**Plain claim.** Assume the ordered-field laws and `0⁻¹ = 0`, and let `t` be a unit change whose factors are all nonzero. For every set `O` of dimensions: `t` preserves the truth value of every formula that is well typed with order atoms at dimensions in `O` (`∀ Γ φ, WellTypedAt O Γ φ → InvariantAt Γ t φ`) if and only if the scale factor of every such dimension is positive (`∀ d, O d → 0 < scaleOf t d`). The condition is on `scaleOf t d = ∏ i, t i ^ d i` for `d ∈ O`, not on the base factors `t i`.

**Kind / tier / depth.** characterization / T1 / shallow.

Basis: execution (Lean kernel check) of `invariantAt_all_wellTypedAt_iff` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/Homogeneity.lean:180-183
theorem invariantAt_all_wellTypedAt_iff (h : OrderedFieldLaws K) (hz : InvZeroLaw K)
    (O : Dim m → Prop) {t : Fin m → K} (ht : ∀ i, t i ≠ 0) :
    (∀ (Γ : Ctx m) (φ : Formula m K), WellTypedAt O Γ φ → InvariantAt Γ t φ) ↔
      (∀ d, O d → 0 < scaleOf t d) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : OrderedFieldLaws K` | Positivity and multiplication by positive and negative scale factors; homogeneity. | harmless: every ordered field satisfies it (`ratLaws` proves it for `Rat`); tightness of the individual laws in the bundle is not examined |
| `hz : InvZeroLaw K` | For the `←` direction: the homogeneity of the typed subexpressions (`evalIn_act_eq_scaleOf_mul`) needs it wherever `0⁻¹` enters a reading: a quotient whose denominator reads `0`, a negative integer power of a zero reading, and, in a base system with a zero factor, a literal of negative dimension (at expression level: `invLLit_not_homogeneous_zero_system_ratJ`); the convention `0⁻¹ = 0` commutes with rescaling. | tight: counterexample `orderIff_fails_without_invZero_ratJ` (`RatJ`, `t = 2`, order atoms at every dimension: right side holds, left side fails at `divLe`) |
| `ht : ∀ i, t i ≠ 0` | Homogeneity and cancellation (the `←` direction). | tight: counterexample `orderIff_fails_at_zero_factor` (`Rat`, `t = 0`, no order atom: right side holds vacuously, left side fails at `eqXY`) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/Tightness.lean:230-235
theorem orderIff_fails_without_invZero_ratJ :
    OrderedFieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧
      (∀ i : Fin 1, (fun _ => RatJ.ofRat 2) i ≠ 0) ∧
      ¬ ((∀ (Γ : Ctx 1) (φ : Formula 1 RatJ),
            WellTypedAt (fun _ => True) Γ φ → InvariantAt Γ (fun _ => RatJ.ofRat 2) φ) ↔
          (∀ d : Dim 1, (fun _ => True) d → 0 < scaleOf (fun _ => RatJ.ofRat 2) d)) := …
```

```lean
-- ToyUnits/Tightness.lean:252-257
theorem orderIff_fails_at_zero_factor :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧
      ¬ (∀ i : Fin 1, (fun _ => (0 : Rat)) i ≠ 0) ∧
      ¬ ((∀ (Γ : Ctx 1) (φ : Formula 1 Rat),
            WellTypedAt (fun _ => False) Γ φ → InvariantAt Γ (fun _ => (0 : Rat)) φ) ↔
          (∀ d : Dim 1, (fun _ => False) d → 0 < scaleOf (fun _ => (0 : Rat)) d)) := …
```

**Non-vacuity witness.** `Rat` with `t = -1` (`nonvacuous_characterization`). Worked instances at `t = -1`: the order atom of `0 ≤ x` sits at `L`, where `scaleOf t L = -1 < 0`, and the formula flips (`nonnegL_not_invariantAt_neg_one`); the order atom of `0 ≤ x * x` sits at `L * L`, where `scaleOf t (L * L) = 1 > 0`, and that formula is invariant (`nonnegL2_invariantAt_neg_one`, from the `←` direction with `O = {L * L}`).

```lean
-- ToyUnits/Examples.lean:150-151
theorem nonvacuous_characterization :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ (∀ i : Fin 1, (fun _ => (-1 : Rat)) i ≠ 0) := …
```

**Non-claims.** Listed under Boundaries, "Non-claims of Result 8"; read them together with the plain claim.

**Prior art.** Atkey–Johann–Kennedy 2013; Kennedy 1997; Roberts 1979. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Exactly which unit changes, sign flips included, preserve which order comparisons?

**Further declarations cited in this result (verbatim).**

```lean
-- ToyUnits/Counterexamples.lean:177-178
theorem nonnegL_not_invariantAt_neg_one :
    (∀ i : Fin 1, (fun _ => (-1 : Rat)) i ≠ 0) ∧ ¬ InvariantAt ctxL (fun _ => (-1 : Rat)) nonnegL := …
```

```lean
-- ToyUnits/Counterexamples.lean:192
theorem nonnegL2_invariantAt_neg_one : InvariantAt ctxL (fun _ => (-1 : Rat)) nonnegL2 := …
```

### Result 9. `offset_units_dimension_check_overclaims`

**Plain claim.** In the affine toy with all variables temperature readings (points, `sortsPt`), the formula `sumTemps` (`t₁ + t₂ ≤ t₃`) passes plain dimension checking (`ADimCheckedF sortsPt sumTemps`), is rejected by the point/vector discipline (`¬ PointVectorTyped WeightsSumOne sortsPt sumTemps`), and is not invariant under positive affine scale changes between scales with positive factor (`¬ PosAffineInvariant sortsPt sumTemps`). Explicitly (`sumTemps_celsius_kelvin`): at `t₁ = t₂ = -10, t₃ = 0` it holds in °C (`-20 ≤ 0`) and fails for the same temperatures in K (`263.15 + 263.15 ≤ 273.15`).

**Kind / tier / depth.** counterexample / T0 / definitional.

Basis: execution (Lean kernel check) of `sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/AffineExamples.lean:106-108
theorem sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant :
    ADimCheckedF sortsPt sumTemps ∧ ¬ PointVectorTyped WeightsSumOne sortsPt sumTemps ∧
      ¬ PosAffineInvariant sortsPt sumTemps := …
```

**Hypothesis ledger.**

No hypotheses (a closed statement about concrete instances, or a universal statement with no premise).

**Non-vacuity witness.** Counterexample result with no hypotheses; the concrete flip is `sumTemps_celsius_kelvin`.

```lean
-- ToyUnits/AffineExamples.lean:90-94
theorem sumTemps_celsius_kelvin :
    ADimCheckedF sortsPt sumTemps ∧
    AFormula.holdsIn celsius sumTempsEnv sumTemps ∧
    ¬ AFormula.holdsIn (celsiusToKelvin.1 * celsius.1, celsiusToKelvin.1 * celsius.2 + celsiusToKelvin.2)
        (actA sortsPt celsiusToKelvin sumTempsEnv) sumTemps := …
```

**Non-claims.** Listed under Boundaries, "Non-claims of Result 9"; read them together with the plain claim.

**Prior art.** Stevens 1946; Roberts 1979; Suppes–Zinnes 1963; Pint 0.26.2 documentation; mp-units v2.5.0 documentation. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Where does dimension checking over-claim? For offset units it accepts statements whose truth depends on the zero of the scale.

**Further declarations cited in this result (verbatim).**

```lean
-- ToyUnits/AffineExamples.lean:76
theorem sumTemps_dimChecked : ADimCheckedF sortsPt sumTemps := …
```

```lean
-- ToyUnits/AffineExamples.lean:79
theorem sumTemps_not_pointVectorTyped : ¬ PointVectorTyped WeightsSumOne sortsPt sumTemps := …
```

### Result 10. `point_vector_typed_formulas_affine_invariant`

**Plain claim.** Assume the ordered-field laws and `0⁻¹ = 0`. Every formula typed by the point/vector discipline with weights summing to one (`PointVectorTyped WeightsSumOne S φ`: point − point, point ± vector and vector + point, vector-space operations, ratios of vectors, number arithmetic, binary affine combinations `w₁ * p + w₂ * q` of points with constant weights `w₁ + w₂ = 1`, comparisons within one sort, connectives, and quantifiers over a sort) keeps its truth value under every scale change `x ↦ a * x + b` with `a > 0`, applied to every scale `u` (including scales with `u.1 ≤ 0`) and all readings (`AffineInvariant S φ`).

**Kind / tier / depth.** theorem / T0 / shallow.

Basis: execution (Lean kernel check) of `affineInvariant_of_pointVectorTyped` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/Affine.lean:338-340
theorem affineInvariant_of_pointVectorTyped (h : OrderedFieldLaws K) (hz : InvZeroLaw K)
    {S : Nat → ASort} {φ : AFormula K} (hφ : PointVectorTyped WeightsSumOne S φ) :
    AffineInvariant S φ := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : OrderedFieldLaws K` | Monotonicity of `x ↦ a * x + b` for `a > 0`; field algebra; surjectivity for quantifiers. | harmless: every ordered field satisfies it (`ratLaws` proves it for `Rat`); tightness of the individual laws in the bundle is not examined |
| `hz : InvZeroLaw K` | Ratios of differences at a zero denominator (`vecDivVec`). | tight: counterexample `ratioLe_not_affineInvariant_ratJ` (`RatJ`, formula `(t₁ - t₂) / (t₃ - t₃) ≤ 1`, scale change `x ↦ 2 * x` from `u = (1, 0)`) |
| `hφ : PointVectorTyped WeightsSumOne S φ` | Typing rejects point + point and the like. | tight: counterexample `sumTemps_affine_tight` (`Rat`, formula `t₁ + t₂ ≤ t₃`, °C to K) |
| weight condition `WeightsSumOne` (the side condition `W` fixed in `hφ`) | Affine combinations of points are scale-independent when the weights sum to one. | tight: counterexample `combSumLe_weights_tight` (`Rat`, formula `1 * t₁ + 1 * t₂ ≤ t₃` typed with arbitrary weights, °C to K) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/AffineExamples.lean:184-186
theorem ratioLe_not_affineInvariant_ratJ :
    OrderedFieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ PointVectorTyped WeightsSumOne sortsPt ratioLe ∧
      ¬ AffineInvariant sortsPt ratioLe := …
```

```lean
-- ToyUnits/AffineExamples.lean:120-122
theorem sumTemps_affine_tight :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ ¬ PointVectorTyped WeightsSumOne sortsPt sumTemps ∧
      ¬ AffineInvariant sortsPt sumTemps := …
```

```lean
-- ToyUnits/AffineExamples.lean:162-164
theorem combSumLe_weights_tight :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ PointVectorTyped (fun _ _ => True) sortsPt combSumLe ∧
      ¬ WeightsSumOne (1 : Rat) 1 ∧ ¬ AffineInvariant sortsPt combSumLe := …
```

**Non-vacuity witness.** `Rat` with the mean formula `meanLe` (`(1/2) t₁ + (1/2) t₂ ≤ t₃`, an affine combination) and the quantified formula `quantPt` (`nonvacuous_affine`). With Result 9 (`offset_units_dimension_check_overclaims`) this shows that comparing the mean of two temperatures with a third is invariant while comparing their sum is not.

```lean
-- ToyUnits/Examples.lean:162-164
theorem nonvacuous_affine :
    OrderedFieldLaws Rat ∧ InvZeroLaw Rat ∧ PointVectorTyped WeightsSumOne sortsPt meanLe ∧
      PointVectorTyped WeightsSumOne sortsPt quantPt := …
```

**Non-claims.** Listed under Boundaries, "Non-claims of Result 10"; read them together with the plain claim.

**Prior art.** Atkey–Johann–Kennedy 2013; Stevens 1946; Roberts 1979; Baez 2009; Pint 0.26.2 documentation; mp-units v2.5.0 documentation. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Which typing discipline for offset quantities makes statements independent of the scale's zero and unit?

**Further declarations cited in this result (verbatim).**

```lean
-- ToyUnits/AffineExamples.lean:132
theorem meanLe_pointVectorTyped : PointVectorTyped WeightsSumOne sortsPt meanLe := …
```

```lean
-- ToyUnits/Affine.lean:254-257
theorem AExpr.evalIn_act (h : FieldLaws K) (hz : InvZeroLaw K) {S : Nat → ASort}
    {e : AExpr K} {σ : ASort} (he : HasSort WeightsSumOne S e σ) {g : K × K} (hg : g.1 ≠ 0)
    (u : K × K) (ρ : Env K) :
    AExpr.evalIn (g.1 * u.1, g.1 * u.2 + g.2) (actA S g ρ) e = σ.act g (AExpr.evalIn u ρ e) := …
```

### Result 11. `one_var_length_polynomial_linear_everywhere`

**Plain claim.** Assume the commutative-ring laws (`CommRingLaws K`; no inverse law, no order law, no `0⁻¹` convention). For every context `Γ`, variable `x` and expression `e` such that `e` has dimension `L` (`HasDim Γ e L`), mentions no variable other than `x` (`e.onlyVar x`), has dimensionless literals (`e.dimlessLits`) and is polynomial (`e.isPolynomial`: no division, no negative power), for every unit system `s`, all readings `ρ` and every reading `v` of `x`: the reading of `e` at `x = v` equals its reading at `x = 1` times `v`.

**Kind / tier / depth.** theorem / T0 / shallow.

Basis: execution (Lean kernel check) of `oneVarLength_poly_eval_eq_mul` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/FreeTheorem.lean:212-215
theorem oneVarLength_poly_eval_eq_mul (h : CommRingLaws K) {Γ : Ctx 1} {x : Nat}
    {e : Expr 1 K} (htyped : HasDim Γ e L) (hx : e.onlyVar x) (hd : e.dimlessLits)
    (hp : e.isPolynomial) (s : Fin 1 → K) (ρ : Env K) (v : K) :
    e.evalIn s (upd ρ x v) = e.evalIn s (upd ρ x 1) * v := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : CommRingLaws K` | Expanding sums and products of powers of the reading. | harmless: every commutative ring satisfies it (`ratLaws` proves it for `Rat`); tightness of the individual laws in the bundle is not examined |
| `htyped : HasDim Γ e L` | Fixes the degree: dimension `L` means degree one in `x`. | tight: counterexample `addOneDimless_not_linear` (`Rat`, `x + 1` with a dimensionless `1` (no dimension)) |
| `hx : e.onlyVar x` | No other variable enters the reading. | tight: counterexample `twoVarSum_not_linear` (`Rat`, `x + y` at `y = 1`) |
| `hd : e.dimlessLits` | Literals do not rescale. | tight: counterexample `addOneLength_not_linear` (`Rat`, `x + lit 1 L`, reference units) |
| `hp : e.isPolynomial` | Without division and negative powers no `0⁻¹` convention is needed. | tight: counterexample `sqOverZero_not_linear_ratJ` (`RatJ` (a commutative ring with `0⁻¹ = 1`), `x * x / (x - x)`, `v = 2`) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/Tightness.lean:87-92
theorem addOneDimless_not_linear :
    CommRingLaws Rat ∧ FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxL 0 = L ∧
      (∀ d, ¬ HasDim ctxL addOneDimless d) ∧ addOneDimless.onlyVar 0 ∧
      addOneDimless.dimlessLits ∧ addOneDimless.isPolynomial ∧
      addOneDimless.evalIn (fun _ => 1) (upd (fun _ => 0) 0 2) ≠
        addOneDimless.evalIn (fun _ => 1) (upd (fun _ => 0) 0 1) * 2 := …
```

```lean
-- ToyUnits/Tightness.lean:105-110
theorem twoVarSum_not_linear :
    CommRingLaws Rat ∧ FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxL 0 = L ∧
      HasDim ctxL twoVarSum L ∧ ¬ twoVarSum.onlyVar 0 ∧ twoVarSum.dimlessLits ∧
      twoVarSum.isPolynomial ∧
      twoVarSum.evalIn (fun _ => 1) (upd (fun _ => 1) 0 2) ≠
        twoVarSum.evalIn (fun _ => 1) (upd (fun _ => 1) 0 1) * 2 := …
```

```lean
-- ToyUnits/Tightness.lean:72-77
theorem addOneLength_not_linear :
    CommRingLaws Rat ∧ FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxL 0 = L ∧
      HasDim ctxL addOneLength L ∧ addOneLength.onlyVar 0 ∧ ¬ addOneLength.dimlessLits ∧
      addOneLength.isPolynomial ∧
      addOneLength.evalIn (fun _ => 1) (upd (fun _ => 0) 0 2) ≠
        addOneLength.evalIn (fun _ => 1) (upd (fun _ => 0) 0 1) * 2 := …
```

```lean
-- ToyUnits/FreeTheorem.lean:496-501
theorem sqOverZero_not_linear_ratJ :
    CommRingLaws RatJ ∧ FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ ctxL 0 = L ∧
      HasDim ctxL sqOverZero L ∧ sqOverZero.onlyVar 0 ∧ sqOverZero.dimlessLits ∧
      ¬ sqOverZero.isPolynomial ∧
      sqOverZero.evalIn (fun _ => 1) (upd (fun _ => RatJ.ofRat 0) 0 (RatJ.ofRat 2)) ≠
        sqOverZero.evalIn (fun _ => 1) (upd (fun _ => RatJ.ofRat 0) 0 1) * RatJ.ofRat 2 := …
```

**Non-vacuity witness.** `Rat`, `polyWitness` (`2 * x + x - x`) (`nonvacuous_poly`).

```lean
-- ToyUnits/Examples.lean:209-211
theorem nonvacuous_poly :
    CommRingLaws Rat ∧ HasDim ctxL polyWitness L ∧ polyWitness.onlyVar 0 ∧
      polyWitness.dimlessLits ∧ polyWitness.isPolynomial := …
```

**Remarks.**

- The hypothesis `Γ x = L` is not assumed: it follows from `htyped`, `hx`, `hd` and `hp` (`ctx_eq_L_of_poly`).

**Non-claims.** Listed under Boundaries, "Non-claims of Result 11"; read them together with the plain claim.

**Prior art.** Kennedy 1997; Atkey–Johann–Kennedy 2013; Luce 1959. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** What can a unit-typed program compute from a single length? A polynomial expression of dimension `L` in that one variable with dimensionless literals computes a multiple of it.

**Further declarations cited in this result (verbatim).**

```lean
-- ToyUnits/FreeTheorem.lean:132-134
theorem ctx_eq_L_of_poly {Γ : Ctx 1} {x : Nat} {e : Expr 1 K}
    (htyped : HasDim Γ e L) (hx : e.onlyVar x) (hd : e.dimlessLits) (hp : e.isPolynomial) :
    Γ x = L := …
```

### Result 12. `one_var_length_rational_linear_everywhere`

**Plain claim.** Assume the field laws (`FieldLaws K`; no order law) and `0⁻¹ = 0` (`InvZeroLaw K`). For every one-variable expression of dimension `L` in a length variable `x` with dimensionless literals (`OneVarLength Γ x e`: `Γ x = L`, `HasDim Γ e L`, `e.onlyVar x`, `e.dimlessLits`), every unit system `s`, all readings `ρ` and every reading `v` of `x` (zero included; in an ordered field, negative readings included): the reading of `e` at `x = v` equals its reading at `x = 1` times `v`.

**Kind / tier / depth.** theorem / T0 / shallow.

Basis: execution (Lean kernel check) of `oneVarLength_eval_eq_mul` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/FreeTheorem.lean:340-343
theorem oneVarLength_eval_eq_mul (h : FieldLaws K) (hz : InvZeroLaw K)
    {Γ : Ctx 1} {x : Nat} {e : Expr 1 K} (he : OneVarLength Γ x e)
    (s : Fin 1 → K) (ρ : Env K) (v : K) :
    e.evalIn s (upd ρ x v) = e.evalIn s (upd ρ x 1) * v := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : FieldLaws K` | Homogeneity at nonzero readings (rescale by `t = v`). | harmless: every field satisfies it (`ratLaws` proves it for `Rat`, `gf2_fieldLaws` for `GF2`); tightness of the individual laws in the bundle is not examined |
| `hz : InvZeroLaw K` | Quotients and negative powers at the reading `0`, and homogeneity at a zero denominator. | tight: counterexample `sqOverZero_not_linear_ratJ` (`RatJ` (every field law, `0⁻¹ = 1`), `x * x / (x - x)`, `v = 2`) |
| `he.ctx_x : Γ x = L` | The variable is a length. | tight: counterexample `invVar_not_linear` (`Rat`, `x` of dimension `1 / L`, `1 / x`) |
| `he.typed : HasDim Γ e L` | Fixes the degree. | tight: counterexample `addOneDimless_not_linear` (`Rat`, `x + 1` with a dimensionless `1`) |
| `he.only_x : e.onlyVar x` | No other variable enters the reading. | tight: counterexample `twoVarSum_not_linear` (`Rat`, `x + y` at `y = 1`) |
| `he.dimless : e.dimlessLits` | Literals do not rescale. | tight: counterexample `addOneLength_not_linear` (`Rat`, `x + lit 1 L`) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/FreeTheorem.lean:496-501
theorem sqOverZero_not_linear_ratJ :
    CommRingLaws RatJ ∧ FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ ctxL 0 = L ∧
      HasDim ctxL sqOverZero L ∧ sqOverZero.onlyVar 0 ∧ sqOverZero.dimlessLits ∧
      ¬ sqOverZero.isPolynomial ∧
      sqOverZero.evalIn (fun _ => 1) (upd (fun _ => RatJ.ofRat 0) 0 (RatJ.ofRat 2)) ≠
        sqOverZero.evalIn (fun _ => 1) (upd (fun _ => RatJ.ofRat 0) 0 1) * RatJ.ofRat 2 := …
```

```lean
-- ToyUnits/Tightness.lean:128-132
theorem invVar_not_linear :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxInvL 0 ≠ L ∧ HasDim ctxInvL invVar L ∧
      invVar.onlyVar 0 ∧ invVar.dimlessLits ∧ ¬ invVar.isPolynomial ∧
      invVar.evalIn (fun _ => 1) (upd (fun _ => 0) 0 2) ≠
        invVar.evalIn (fun _ => 1) (upd (fun _ => 0) 0 1) * 2 := …
```

```lean
-- ToyUnits/Tightness.lean:87-92
theorem addOneDimless_not_linear :
    CommRingLaws Rat ∧ FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxL 0 = L ∧
      (∀ d, ¬ HasDim ctxL addOneDimless d) ∧ addOneDimless.onlyVar 0 ∧
      addOneDimless.dimlessLits ∧ addOneDimless.isPolynomial ∧
      addOneDimless.evalIn (fun _ => 1) (upd (fun _ => 0) 0 2) ≠
        addOneDimless.evalIn (fun _ => 1) (upd (fun _ => 0) 0 1) * 2 := …
```

```lean
-- ToyUnits/Tightness.lean:105-110
theorem twoVarSum_not_linear :
    CommRingLaws Rat ∧ FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxL 0 = L ∧
      HasDim ctxL twoVarSum L ∧ ¬ twoVarSum.onlyVar 0 ∧ twoVarSum.dimlessLits ∧
      twoVarSum.isPolynomial ∧
      twoVarSum.evalIn (fun _ => 1) (upd (fun _ => 1) 0 2) ≠
        twoVarSum.evalIn (fun _ => 1) (upd (fun _ => 1) 0 1) * 2 := …
```

```lean
-- ToyUnits/Tightness.lean:72-77
theorem addOneLength_not_linear :
    CommRingLaws Rat ∧ FieldLaws Rat ∧ InvZeroLaw Rat ∧ ctxL 0 = L ∧
      HasDim ctxL addOneLength L ∧ addOneLength.onlyVar 0 ∧ ¬ addOneLength.dimlessLits ∧
      addOneLength.isPolynomial ∧
      addOneLength.evalIn (fun _ => 1) (upd (fun _ => 0) 0 2) ≠
        addOneLength.evalIn (fun _ => 1) (upd (fun _ => 0) 0 1) * 2 := …
```

**Non-vacuity witness.** `Rat` with the non-polynomial `cubeOverSquare` (`3 * (x ^ 3 / (x * x))`) (`nonvacuous_oneVarLength`); also `GF2`, a field with `0⁻¹ = 0` that admits no ordered-field laws (`nonvacuous_oneVarLength_gf2`).

```lean
-- ToyUnits/Examples.lean:183-184
theorem nonvacuous_oneVarLength :
    FieldLaws Rat ∧ InvZeroLaw Rat ∧ OneVarLength ctxL 0 cubeOverSquare := …
```

```lean
-- ToyUnits/Examples.lean:193-195
theorem nonvacuous_oneVarLength_gf2 :
    FieldLaws GF2 ∧ InvZeroLaw GF2 ∧ ¬ OrderedFieldLaws GF2 ∧
      OneVarLength ctxL 0 (linearWitness (1 : GF2)) := …
```

**Remarks.**

- The proof splits at `v = 0`: for `v ≠ 0` it rescales by `t = v` (`oneVarLength_eval_eq_mul_of_ne_zero`); at `v = 0` every subexpression of nonzero dimension reads `0` (`evalIn_zero_of_dim_ne_zero`).

**Non-claims.** Listed under Boundaries, "Non-claims of Result 12"; read them together with the plain claim.

**Prior art.** Kennedy 1997; Atkey–Johann–Kennedy 2013; Luce 1959. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** What can a unit-typed program compute from a single length, division included? Under the field laws and `0⁻¹ = 0`, a one-variable expression of dimension `L` in a length variable with dimensionless literals computes a multiple of it.

### Result 13. `definable_on_positive_iff_linear`

**Plain claim.** Assume the ordered-field laws and `0⁻¹ = 0`. A function `f : K → K` is definable on positive readings (`DefinableOnPos f`: for some context `Γ`, variable `x` with `Γ x = L` and expression `e` of dimension `L`, the reading of `e` at `x = v` equals `f v` for every `v > 0`, every unit system `s` and all readings `ρ` of the other variables) if and only if there is a constant `c` with `f v = c * v` for every `v > 0`.

**Kind / tier / depth.** characterization / T0 / shallow.

Basis: execution (Lean kernel check) of `definableOnPos_iff` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/FreeTheorem.lean:384-385
theorem definableOnPos_iff (h : OrderedFieldLaws K) (hz : InvZeroLaw K) (f : K → K) :
    DefinableOnPos f ↔ ∃ c : K, ∀ v : K, 0 < v → f v = c * v := …
```

Unfolded left side of `definableOnPos_iff` (definition `DefinableOnPos` expanded):

```lean
∃ (Γ : Ctx 1) (x : Nat) (e : Expr 1 K), Γ x = L ∧ HasDim Γ e L ∧
  ∀ (s : Fin 1 → K) (ρ : Env K) (v : K), 0 < v → e.evalIn s (upd ρ x v) = f v
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : OrderedFieldLaws K` | `0 < v` gives `v ≠ 0`; field algebra for homogeneity. | harmless: every ordered field satisfies it (`ratLaws` proves it for `Rat`); tightness of the individual laws in the bundle is not examined |
| `hz : InvZeroLaw K` | Homogeneity at a zero denominator. | tight: counterexample `definableOnPos_iff_fails_without_invZero_ratJ` (`RatJ`, `f = fun v => v + 1`: left side holds (junk constant of dimension `L`), right side fails) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/Tightness.lean:213-216
theorem definableOnPos_iff_fails_without_invZero_ratJ :
    OrderedFieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧
      ¬ (DefinableOnPos (fun v : RatJ => v + 1) ↔
        ∃ c : RatJ, ∀ v : RatJ, 0 < v → v + 1 = c * v) := …
```

**Non-vacuity witness.** `Rat` (`ratLaws`, `ratInvZero`) with `f = fun v => 2 * v` (`definableOnPos_two_mul`).

```lean
-- ToyUnits/Examples.lean:110
theorem definableOnPos_two_mul : DefinableOnPos (fun v : Rat => 2 * v) := …
```

```lean
-- ToyUnits/Instances.lean:18
theorem ratLaws : OrderedFieldLaws Rat where
```

```lean
-- ToyUnits/Instances.lean:41
theorem ratInvZero : InvZeroLaw Rat := …
```

**Non-claims.** Listed under Boundaries, "Non-claims of Result 13"; read them together with the plain claim.

**Prior art.** Kennedy 1997; Atkey–Johann–Kennedy 2013; Luce 1959. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Which functions of a length can a unit-typed program compute on positive readings, independently of the unit system?

### Result 14. `succ_not_definable_on_positive`

**Plain claim.** Assume the ordered-field laws and `0⁻¹ = 0`. The function `v ↦ v + 1` is not definable on positive readings (`¬ DefinableOnPos (fun v => v + 1)`): no expression of dimension `L` in a length variable computes `v + 1` at every positive reading `v`, in every unit system and for all readings of the other variables.

**Kind / tier / depth.** impossibility / T0 / shallow.

Basis: execution (Lean kernel check) of `not_definableOnPos_add_one` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/FreeTheorem.lean:412-413
theorem not_definableOnPos_add_one (h : OrderedFieldLaws K) (hz : InvZeroLaw K) :
    ¬ DefinableOnPos (fun v : K => v + 1) := …
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : OrderedFieldLaws K` | Characterization `definableOnPos_iff`; arithmetic at `v = 1` and `v = 1 + 1`. | harmless: every ordered field satisfies it (`ratLaws` proves it for `Rat`); tightness of the individual laws in the bundle is not examined |
| `hz : InvZeroLaw K` | Characterization `definableOnPos_iff`. | tight: counterexample `addOne_definableOnPos_ratJ` (`RatJ` (every ordered-field law, `0⁻¹ = 1`): `x + 1 / (1 / (x - x))` has dimension `L` and computes `v + 1`) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/Tightness.lean:196-197
theorem addOne_definableOnPos_ratJ :
    OrderedFieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ DefinableOnPos (fun v : RatJ => v + 1) := …
```

**Non-vacuity witness.** `Rat` satisfies both hypotheses (`ratLaws`, `ratInvZero`).

```lean
-- ToyUnits/Instances.lean:18
theorem ratLaws : OrderedFieldLaws Rat where
```

```lean
-- ToyUnits/Instances.lean:41
theorem ratInvZero : InvZeroLaw Rat := …
```

**Positive control.** Dropping `0⁻¹ = 0` makes `v ↦ v + 1` definable (`addOne_definableOnPos_ratJ`); dropping typing, the dimensionless-literal expression `x + 1` computes `v + 1` in every unit system but has no dimension (`addOneDimless_control`).

```lean
-- ToyUnits/FreeTheorem.lean:469-471
theorem addOneDimless_control :
    (∀ d, ¬ HasDim ctxL addOneDimless d) ∧ addOneDimless.onlyVar 0 ∧ addOneDimless.dimlessLits ∧
      ∀ (s : Fin 1 → Rat) (ρ : Env Rat) (v : Rat), addOneDimless.evalIn s (upd ρ 0 v) = v + 1 := …
```

**Non-claims.** Listed under Boundaries, "Non-claims of Result 14"; read them together with the plain claim.

**Prior art.** Kennedy 1997; Atkey–Johann–Kennedy 2013; Luce 1959. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Can a unit-typed program add a bare number to a length in a unit-independent way?

**Further declarations cited in this result (verbatim).**

```lean
-- ToyUnits/FreeTheorem.lean:457-459
theorem addOneLength_control :
    HasDim ctxL addOneLength L ∧ addOneLength.onlyVar 0 ∧ ¬ addOneLength.dimlessLits ∧
      ∀ (s : Fin 1 → Rat) (ρ : Env Rat) (v : Rat), addOneLength.evalIn s (upd ρ 0 v) = v + s 0 := …
```

### Result 15. `max_one_not_definable_on_positive`

**Plain claim.** Over `Rat` (which satisfies the ordered-field laws and `0⁻¹ = 0`), the function `v ↦ max v 1` is not definable on positive readings (`¬ DefinableOnPos (fun v : Rat => max v 1)`): no expression of dimension `L` in a length variable computes `max v 1` at every positive reading `v`, in every unit system and for all readings of the other variables.

**Kind / tier / depth.** impossibility / T0 / shallow.

Basis: execution (Lean kernel check) of `not_definableOnPos_max_one` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/FreeTheorem.lean:434
theorem not_definableOnPos_max_one : ¬ DefinableOnPos (fun v : Rat => max v 1) := …
```

**Hypothesis ledger.**

No hypotheses (a closed statement about concrete instances, or a universal statement with no premise).

**Non-vacuity witness.** No hypotheses (a closed statement about `Rat`).

**Positive control.** Clamping at the threshold `0` instead of `1` is definable on positive readings: `DefinableOnPos (fun v : Rat => max v 0)` holds (`definableOnPos_max_zero`). On positive readings `max v 0 = v`, so the defining function there is `v ↦ 1 * v` and no clamping takes place. The control shows that replacing the threshold `1` by `0` removes the impossibility; it does not show that clamping at any positive threshold is definable. On all readings, including `v ≤ 0`, `v ↦ max v 0` is not expected to be computable by a toy expression of dimension `L` (not proved here; `DefinableOnPos` places no requirement on readings `v ≤ 0`).

```lean
-- ToyUnits/FreeTheorem.lean:446
theorem definableOnPos_max_zero : DefinableOnPos (fun v : Rat => max v 0) := …
```

**Non-claims.** Listed under Boundaries, "Non-claims of Result 15"; read them together with the plain claim.

**Prior art.** Kennedy 1997; Atkey–Johann–Kennedy 2013. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Can a unit-typed program clamp a length at a bare number in a unit-independent way?

### Result 16. `inv_zero_convention_iff_typed_homogeneity`

**Plain claim.** Assume the field laws (`FieldLaws K`) and that `K` has an element `a` with `a ≠ 0` and `a ≠ 1`. With at least one base dimension (`m + 1` base dimensions), every well-typed expression is homogeneous under every unit change with nonzero factors (`AllHomogeneous (m + 1) K`: for every `Γ`, `e`, `d` with `HasDim Γ e d`, every `t` with nonzero factors, every unit system `s` and all readings `ρ`, the reading in `fun i => t i * s i` with `actEnv Γ t ρ` equals `scaleOf t d` times the reading in `s` with `ρ`) if and only if the total division returns `0` at a zero denominator (`InvZeroLaw K`).

**Kind / tier / depth.** characterization / T1 / shallow.

Basis: execution (Lean kernel check) of `allHomogeneous_iff_invZero` and of every witness quoted in this result.

**Lean statement (verbatim).**

```lean
-- ToyUnits/ZeroInverse.lean:47-48
theorem allHomogeneous_iff_invZero (h : FieldLaws K) (h2 : ∃ a : K, a ≠ 0 ∧ a ≠ 1) :
    AllHomogeneous (m + 1) K ↔ InvZeroLaw K := …
```

Unfolded left side of `allHomogeneous_iff_invZero` (definition `AllHomogeneous` expanded):

```lean
∀ (Γ : Ctx (m + 1)) (e : Expr (m + 1) K) (d : Dim (m + 1)), HasDim Γ e d →
  ∀ t : Fin (m + 1) → K, (∀ i, t i ≠ 0) → ∀ (s : Fin (m + 1) → K) (ρ : Env K),
    Expr.evalIn (fun i => t i * s i) (actEnv Γ t ρ) e = scaleOf t d * Expr.evalIn s ρ e
```

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
|---|---|---|
| `h : FieldLaws K` | Homogeneity (`←`, via `evalIn_act_eq_scaleOf_mul`); cancelling `0⁻¹` (`→`). | harmless: every field satisfies it (`ratLaws` proves it for `Rat`, `gf2_fieldLaws` for `GF2`); tightness of the individual laws in the bundle is not examined |
| `h2 : ∃ a : K, a ≠ 0 ∧ a ≠ 1` | A unit change other than the identity, to observe `a * 0⁻¹ = 0⁻¹` in `x / y` at `y = 0`. | tight: counterexample `allHomogeneous_iff_fails_gf2J` (`GF2J` (two-element field, `0⁻¹ = 1`), one base dimension: every nonzero unit change is the identity) |
| at least one base dimension (the `m + 1` in `AllHomogeneous (m + 1) K`) | Some dimension must rescale. | tight: counterexample `allHomogeneous_iff_fails_zero_dims_ratJ` (`RatJ`, no base dimension: every scale factor is `1`) |

Tightness witnesses (verbatim; each states that the other hypotheses hold and the conclusion fails):

```lean
-- ToyUnits/ZeroInverse.lean:86-88
theorem allHomogeneous_iff_fails_gf2J :
    FieldLaws GF2J ∧ ¬ (∃ a : GF2J, a ≠ 0 ∧ a ≠ 1) ∧
      ¬ (AllHomogeneous (0 + 1) GF2J ↔ InvZeroLaw GF2J) := …
```

```lean
-- ToyUnits/ZeroInverse.lean:113-115
theorem allHomogeneous_iff_fails_zero_dims_ratJ :
    FieldLaws RatJ ∧ (∃ a : RatJ, a ≠ 0 ∧ a ≠ 1) ∧
      ¬ (AllHomogeneous 0 RatJ ↔ InvZeroLaw RatJ) := …
```

**Non-vacuity witness.** `Rat` with `a = 2` (`nonvacuous_allHomogeneous_iff`); `Rat` has the property (`allHomogeneous_rat`), `RatJ` does not (`not_allHomogeneous_ratJ`).

```lean
-- ToyUnits/ZeroInverse.lean:79
theorem nonvacuous_allHomogeneous_iff : FieldLaws Rat ∧ ∃ a : Rat, a ≠ 0 ∧ a ≠ 1 := …
```

```lean
-- ToyUnits/ZeroInverse.lean:70
theorem allHomogeneous_rat (m : Nat) : AllHomogeneous m Rat := …
```

```lean
-- ToyUnits/ZeroInverse.lean:74
theorem not_allHomogeneous_ratJ : ¬ AllHomogeneous 1 RatJ := …
```

**Remarks.**

- Each other result of the package that assumes `0⁻¹ = 0` has a tightness witness over `RatJ` (every ordered-field law, `0⁻¹ = 1`) in which its remaining hypotheses hold and its conclusion fails: `divXY_not_homogeneous_ratJ` (Result 2), `divLe_not_unitInvariant_ratJ` (Result 3), `divLe_engine_tight_ratJ` (Result 4), `divEq_not_invariant_ratJ` (Result 7), `orderIff_fails_without_invZero_ratJ` (Result 8), `ratioLe_not_affineInvariant_ratJ` (Result 10), `sqOverZero_not_linear_ratJ` (Result 12), `definableOnPos_iff_fails_without_invZero_ratJ` (Result 13), `addOne_definableOnPos_ratJ` (Result 14). For those results no equivalence with `InvZeroLaw` is proved.

**Non-claims.** Listed under Boundaries, "Non-claims of Result 16"; read them together with the plain claim.

**Prior art.** Atkey–Johann–Kennedy 2013; Buzzard 2020. Full records, with what was verified and pinned quotations, are under Evidence, "Primary sources".

**Design question.** Which total-division convention is compatible with unit-safe typing? The convention is a hidden hypothesis of 'typed implies homogeneous'.

### Modeling bridge to real systems

Each remark compares the toy with documented behaviour of a real system. None is a theorem, none transfers a theorem to the real system (no model–system relation is proved), and none states a defect of the system. Pinned file references have the form `path@commit:lines`; the full records are under Evidence, "Primary sources".

- *Pint offset units.* Basis: derived (modeling bridge), from documentation: Pint 0.26.2, `docs/user/nonmult.rst@af817a6094fbc40005fadd7bcc59b138dbff233e`. The page states that "Subtraction of two temperatures given in offset units yields a *delta* unit" (line 51), that "You can add or subtract a quantity with *delta* unit and a quantity with offset unit" (lines 58-59), and that "Because of this ambiguity pint raises an error for the addition of two quantities with offset units (since pint-0.6)." (lines 96-97). This mirrors the point/vector discipline of `HasSort`: point − point is a difference (`ptSubPt`), point ± difference is a point (`ptAddVec`, `vecAddPt`, `ptSubVec`), and point + point has no sort (`hasSort_sum_none`). The same page documents a registry parameter `autoconvert_offset_to_baseunit` (lines 124-126). With it set to true, "Multiplication of a quantity with a single offset unit with order +1 by a number or ndarray yields the quantity in the given unit" (lines 128-129), and "Before all other multiplications, all divisions and in case of exponentiation [#f1]_ involving quantities with offset-units, pint will convert the quantities with offset units automatically to the corresponding base unit before performing the operation." (lines 138-141), where footnote f1 reads "If the exponent is +1, the quantity will not be converted to base unit but remains unchanged." (lines 197-198). The page describes this mode for multiplication, division and exponentiation; it does not describe it as changing addition, and the toy models neither mode's products. Reasoning: a comparison of the documented operations with the rules of `HasSort`; no Pint code was run.
- *mp-units affine space.* Basis: derived (modeling bridge), from documentation: mp-units v2.5.0, `docs/users_guide/framework_basics/the_affine_space.md@27d2def9082ce00d7eb4f75695dbead4a748f23f` and `src/core/include/mp-units/math.h` at the same commit. The documentation lists as "the primary operations one can do in the affine space" (line 22) vector ± vector, −vector, vector * scalar, scalar * vector, vector / scalar, point − point → vector, point + vector → point, vector + point → point and point − vector → point (lines 24-33), and states that it is not possible to add two points, subtract a point from a vector, or multiply or divide points with anything else (lines 37-41). `HasSort` has a rule for each listed operation (`vecAdd`, `vecSub`, `numMulVec`, `vecMulNum`, `vecDivNum`, `ptSubPt`, `ptAddVec`, `vecAddPt`, `ptSubVec`; negation is written as subtraction) and none for the excluded ones; it also has ratios of vectors (`vecDivVec`), number arithmetic, and binary affine combinations of points (`combPt`). The header documents `lerp` for two quantity points, "the result of `a + t(b − a)`" (`math.h` doc comment lines 464-470, the quoted phrase on line 468; `quantity_point` parameters at lines 476-477), and the midpoint of two points (doc comment lines 487-489; parameters at lines 495-496), that is, affine combinations whose weights sum to one; the toy's `combPt` with `WeightsSumOne` corresponds to these (the correspondence is not proved). Reasoning: documentation comparison; no mp-units code was compiled.
- *Dimension checking versus unit tags.* Basis: derived (modeling bridge), from the definitions. `HasDim` checks dimensions within one coherent unit system; it cannot detect two different units of the same dimension, such as pound-force seconds supplied where newton-seconds are expected, because the toy has no units below dimensions. That same-dimension mismatch is outside the model. Typed calculi with unit conversion (Allen 2026) address that setting.
- *Dropped units.* Basis: derived (modeling bridge), from Result 5 and its remark. A literal written without its unit is modeled as a literal annotated `Dim.one`. `dropUnitLe_not_wellTyped_not_posUnitInvariant` shows that `x ≤ 2` with a dimensionless `2` is ill typed and unit-dependent, while `x ≤ 2` with `2` annotated as a length is well typed (`unitLe_wellTyped`) and therefore `UnitInvariant` (`unitInvariant_of_wellTyped`). `sumMixed` is a different error: it adds a length to an area.
- *Junk division.* Basis: derived (modeling bridge), from Result 16 and a secondary source (Buzzard 2020). Lean core `Rat` uses the total convention `0⁻¹ = 0` (`ratInvZero`), which satisfies `InvZeroLaw`; Buzzard 2020 records that Lean, Coq and Isabelle define `1/0 = 0`. Over a field with an element other than `0` and `1`, and with at least one base dimension, `allHomogeneous_iff_invZero` shows that `0⁻¹ = 0` is exactly the total convention under which every typed expression is homogeneous under every unit change with nonzero factors. With `0⁻¹ = 1` the formula-level results fail as well; Result 16's remark lists the witness for each.
- *Offset versus absolute temperature.* Basis: derived (modeling bridge), from the definitions. The affine toy models offset (interval) scales with an arbitrary zero, such as °C and °F (and, by the same algebra, timestamps or altitudes). Thermodynamic temperature measured from absolute zero (kelvin, rankine) is a ratio scale: the change between kelvin and rankine is `x ↦ (9/5) x`, under which sums and ratios of absolute temperatures keep their truth value. In the toy that setting is an instance of the main (ratio-scale) language with a temperature base dimension, not of the affine toy (not proved here as a separate lemma).

### Auxiliary declarations cited by name (verbatim)

Package declarations named in this report and not quoted at a definition or in a result are quoted here.

```lean
-- ToyUnits/Scalar.lean:22
def AddAssocLaw : Prop := ∀ a b c : K, a + b + c = a + (b + c)
```

```lean
-- ToyUnits/Scalar.lean:24
def AddCommLaw : Prop := ∀ a b : K, a + b = b + a
```

```lean
-- ToyUnits/Scalar.lean:54
def AddLeMonoLaw : Prop := ∀ a b c : K, a ≤ b → a + c ≤ b + c
```

```lean
-- ToyUnits/Scalar.lean:28
def AddNegLaw : Prop := ∀ a : K, a + -a = 0
```

```lean
-- ToyUnits/Scalar.lean:26
def AddZeroLaw : Prop := ∀ a : K, a + 0 = a
```

```lean
-- ToyUnits/Scalar.lean:36
def DistribLaw : Prop := ∀ a b c : K, a * (b + c) = a * b + a * c
```

```lean
-- ToyUnits/Scalar.lean:48
def LeAntisymmLaw : Prop := ∀ a b : K, a ≤ b → b ≤ a → a = b
```

```lean
-- ToyUnits/Scalar.lean:44
def LeReflLaw : Prop := ∀ a : K, a ≤ a
```

```lean
-- ToyUnits/Scalar.lean:50
def LeTotalLaw : Prop := ∀ a b : K, a ≤ b ∨ b ≤ a
```

```lean
-- ToyUnits/Scalar.lean:46
def LeTransLaw : Prop := ∀ a b c : K, a ≤ b → b ≤ c → a ≤ c
```

```lean
-- ToyUnits/Scalar.lean:52
def LtIffLaw : Prop := ∀ a b : K, a < b ↔ a ≤ b ∧ ¬ b ≤ a
```

```lean
-- ToyUnits/Scalar.lean:30
def MulAssocLaw : Prop := ∀ a b c : K, a * b * c = a * (b * c)
```

```lean
-- ToyUnits/Scalar.lean:32
def MulCommLaw : Prop := ∀ a b : K, a * b = b * a
```

```lean
-- ToyUnits/Scalar.lean:56
def MulNonnegLaw : Prop := ∀ a b : K, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
```

```lean
-- ToyUnits/Scalar.lean:34
def MulOneLaw : Prop := ∀ a : K, a * 1 = a
```

```lean
-- ToyUnits/Scalar.lean:40
def ZeroNeOneLaw : Prop := (0 : K) ≠ 1
```

```lean
-- ToyUnits/AffineExamples.lean:207-208
theorem affPosConst_posAffineInvariant_not_affineInvariant :
    PosAffineInvariant sortsPt affPosConst ∧ ¬ AffineInvariant sortsPt affPosConst := …
```

```lean
-- ToyUnits/Examples.lean:168-169
def cubeOverSquare : Expr 1 Rat :=
  .mul (.lit 3 Dim.one) (.div (.zpow (.var 0) 3) (.mul (.var 0) (.var 0)))
```

```lean
-- ToyUnits/FreeTheorem.lean:290-294
theorem evalIn_zero_of_dim_ne_zero (h : CommRingLaws K) (hz : InvZeroLaw K)
    {Γ : Ctx 1} {x : Nat} {e : Expr 1 K} {d : Dim 1}
    (he : HasDim Γ e d) (hx : e.onlyVar x) (hd : e.dimlessLits) (hdim : d 0 ≠ 0)
    (s : Fin 1 → K) (ρ : Env K) :
    e.evalIn s (upd ρ x 0) = 0 := …
```

```lean
-- ToyUnits/Tightness.lean:148-154
theorem invLLit_not_homogeneous_zero_system_ratJ :
    FieldLaws RatJ ∧ ¬ InvZeroLaw RatJ ∧ HasDim ctxL invLLit (Dim.div Dim.one L) ∧
      invLLit.isPolynomial ∧ (∀ i : Fin 1, (fun _ => RatJ.ofRat 2) i ≠ 0) ∧
      invLLit.evalIn (fun i => (fun _ => RatJ.ofRat 2) i * (fun _ => RatJ.ofRat 0) i)
          (actEnv ctxL (fun _ => RatJ.ofRat 2) (fun _ => RatJ.ofRat 1)) ≠
        scaleOf (fun _ => RatJ.ofRat 2) (Dim.div Dim.one L) *
          invLLit.evalIn (fun _ => RatJ.ofRat 0) (fun _ => RatJ.ofRat 1) := …
```

```lean
-- ToyUnits/FreeTheorem.lean:86-89
theorem oneVarLength_eval_eq_mul_of_ne_zero (h : FieldLaws K) (hz : InvZeroLaw K)
    {Γ : Ctx 1} {x : Nat} {e : Expr 1 K} (he : OneVarLength Γ x e)
    (s : Fin 1 → K) (ρ : Env K) (v : K) (hv : v ≠ 0) :
    e.evalIn s (upd ρ x v) = e.evalIn s (upd ρ x 1) * v := …
```

```lean
-- ToyUnits/Examples.lean:199
def polyWitness : Expr 1 Rat := .sub (.add (.mul (.lit 2 Dim.one) (.var 0)) (.var 0)) (.var 0)
```

```lean
-- ToyUnits/AffineExamples.lean:144-149
theorem ptLe_not_invariant_neg :
    PointVectorTyped WeightsSumOne sortsPt ptLe ∧
    ¬ (AFormula.holdsIn (((-1 : Rat), (0 : Rat)).1 * celsius.1,
          ((-1 : Rat), (0 : Rat)).1 * celsius.2 + ((-1 : Rat), (0 : Rat)).2)
        (actA sortsPt ((-1 : Rat), (0 : Rat)) (fun x => if x = 0 then 0 else 1)) ptLe ↔
      AFormula.holdsIn celsius (fun x => if x = 0 then 0 else 1) ptLe) := …
```

## Boundaries

Non-claims come first, one list per result, exactly as recorded in `results.json`. Every list ends with the same scope statement (Model–system relation: none proved), repeated so that each list can be quoted together with its result. Escape hatches, tightness status, stronger conclusions that are not established, and any disproved or dropped statements follow the lists.

### Non-claims of Result 1

Result 1 is `plain_reading_iff_pos_unit_invariant` (`hasPlainReading_iff_posUnitInvariant`).

- The equivalence is the universal property of a quotient applied to the step relation; it carries no information about which formulas are invariant (see `unitInvariant_of_wellTyped`, `cubeSum_not_wellTyped_unitInvariant`). That it needs no scalar law reflects that `HasPlainReading` is defined through this quotient; identifying the quotient with a space of intrinsic physical quantities (for example readings normalized to the reference system) would use field and order laws and is not proved here.
- Does not show that `unitChangeStep Γ` is an equivalence relation; `Quot` uses the equivalence relation it generates. That each class is exactly the orbit of a situation under positive unit changes is not proved here.
- Situations range over unit systems with positive factors. The stronger `UnitInvariant`, which also quantifies over base systems with zero or negative factors, implies `PosUnitInvariant` (`posUnitInvariant_of_unitInvariant`) but is not implied by it (`posConstFormula_posUnitInvariant_not_unitInvariant`); a formula that is not `UnitInvariant` can still have a plain reading.
- Readings are exact elements of `K`; measurement error, rounding and floating point are outside the model.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 2

Result 2 is `typed_expression_homogeneous_nonzero_scaling` (`evalIn_act_eq_scaleOf_mul`).

- Does not cover operations outside the toy syntax (absolute value, square roots, transcendental functions, conditionals, `max`).
- Does not claim homogeneity when some factor of `t` is zero; `xTimesInvX_not_homogeneous_zero` refutes it for `t = 0`.
- Does not claim homogeneity for a total division whose value at `0` differs from `0`; `divXY_not_homogeneous_ratJ` refutes it for `0⁻¹ = 1`.
- Homogeneity without `InvZeroLaw` for expressions with no division and no negative power, read in base systems with nonzero factors, is not proved here; the one-variable polynomial case is `oneVarLength_poly_eval_eq_mul`, which assumes no `0⁻¹` convention.
- `HasDim` and `WellTyped` check dimensional consistency within one coherent unit system `s`: every variable and literal of dimension `d` is read in the same unit and rescales by the same factor `scaleOf t d`. The model has no per-variable unit tags and no unit conversions, so it says nothing about mixing two different units of the same dimension (for example metres with feet, or pound-force seconds where newton-seconds are expected); `HasDim` gives `x + y` dimension `L` for two lengths whatever units a writer had in mind for them. Unit-conversion calculi are studied elsewhere (Allen 2026, arXiv:2609.38242).
- Literals are rescaled with their annotated dimension; a literal annotated dimensionless is never rescaled. Whether an annotation matches a writer's intent is outside the model.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 3

Result 3 is `well_typed_formula_unit_invariant` (`unitInvariant_of_wellTyped`).

- Positive multiplicative unit changes `x ↦ a * x` (`a > 0`, a ratio-scale change) are covered; affine changes `x ↦ a * x + b` with an offset are not, and plain dimension checking is not enough for them (`sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant`).
- Quantifiers range over all of `K`. Over a bounded or discrete quantifier domain (integers, an interval) the result is not proved; multiplication by a scale factor need not map such a domain onto itself.
- Does not say that invariance is decidable, or that dimension checking is the only route to invariance (`cubeSum_not_wellTyped_unitInvariant`).
- `HasDim` and `WellTyped` check dimensional consistency within one coherent unit system `s`: every variable and literal of dimension `d` is read in the same unit and rescales by the same factor `scaleOf t d`. The model has no per-variable unit tags and no unit conversions, so it says nothing about mixing two different units of the same dimension (for example metres with feet, or pound-force seconds where newton-seconds are expected); `HasDim` gives `x + y` dimension `L` for two lengths whatever units a writer had in mind for them. Unit-conversion calculi are studied elsewhere (Allen 2026, arXiv:2609.38242).
- A literal annotated with the wrong dimension yields a well-typed formula that is invariant but means something else; the model cannot detect mis-annotation.
- Does not cover operations outside the toy syntax (absolute value, square roots, transcendental functions, conditionals, `max`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 4

Result 4 is `order_preserving_unit_change_preserves_typed_formulas` (`invariantAt_of_wellTypedAt`).

- The order condition is stated per dimension, on `scaleOf t d`, not on the sign of the base factors `t i`; its relation to signs (parity of exponents) is not proved here.
- Does not cover affine (offset) unit changes or operations outside the toy syntax.
- `HasDim` and `WellTyped` check dimensional consistency within one coherent unit system `s`: every variable and literal of dimension `d` is read in the same unit and rescales by the same factor `scaleOf t d`. The model has no per-variable unit tags and no unit conversions, so it says nothing about mixing two different units of the same dimension (for example metres with feet, or pound-force seconds where newton-seconds are expected); `HasDim` gives `x + y` dimension `L` for two lengths whatever units a writer had in mind for them. Unit-conversion calculi are studied elsewhere (Allen 2026, arXiv:2609.38242).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 5

Result 5 is `untyped_reading_unit_dependent` (`sumMixed_not_wellTyped_not_posUnitInvariant`).

- Shows non-invariance of particular ill-typed formulas; it does not say that every ill-typed formula is non-invariant (`cubeSum_not_wellTyped_unitInvariant`).
- `sumMixed` is a dimension mismatch (a length plus an area); it does not model a literal whose unit was dropped (that is `dropUnitLe`), nor two different units of the same dimension (for example pound-force seconds where newton-seconds are expected), which the toy's single coherent unit system does not represent.
- The literal `2` is annotated dimensionless; a writer who meant '2 square metres' or '2 metres' wrote a different formula, which the toy cannot recover from the bare numeral.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 6

Result 6 is `typing_sufficient_not_necessary` (`cubeSum_not_wellTyped_unitInvariant`).

- Over `Rat`, `cubeSum` is equivalent to the well-typed `x ≤ 0` (`rat_add_cube_nonpos_iff`). The witness shows that `WellTyped` is a syntactically incomplete test for `UnitInvariant`; it does not show that dimension typing loses any unit-invariant meaning.
- `cubeSum` is invariant under positive unit changes; it is not invariant under the negative unit change `t = -1` (`cubeSum_not_invariantAt_neg_one`).
- Does not characterize the invariant formulas syntactically or say whether invariance is decidable.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 7

Result 7 is `equality_only_formulas_tolerate_nonzero_scaling` (`invariantAt_of_wellTypedAt_noOrder_of_ne_zero`).

- Requires nonzero factors (`eqXY_engine_tight_zero` refutes `t = 0`) and `0⁻¹ = 0` (`divEq_not_invariant_ratJ`); ill-typed equalities are not covered.
- Does not extend to affine (offset) unit changes: for example `t₁ + t₂ = t₃` between °C and K changes truth value (not proved here); affine changes are treated in the affine toy.
- Does not cover operations outside the toy syntax such as absolute value (whose scaling is `|t|`, as in Atkey-Johann-Kennedy 2013).
- `HasDim` and `WellTyped` check dimensional consistency within one coherent unit system `s`: every variable and literal of dimension `d` is read in the same unit and rescales by the same factor `scaleOf t d`. The model has no per-variable unit tags and no unit conversions, so it says nothing about mixing two different units of the same dimension (for example metres with feet, or pound-force seconds where newton-seconds are expected); `HasDim` gives `x + y` dimension `L` for two lengths whatever units a writer had in mind for them. Unit-conversion calculi are studied elsewhere (Allen 2026, arXiv:2609.38242).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 8

Result 8 is `order_atoms_preserved_iff_scale_factor_positive` (`invariantAt_all_wellTypedAt_iff`).

- The left side quantifies over all formulas with order atoms in `O`. Failing `0 < scaleOf t d` for some `d ∈ O` does not make every individual formula with an order atom at `d` non-invariant under `t`: for example `x ≤ x` and `x ≤ y ∨ y ≤ x` keep their truth value under `t = -1` (not proved here).
- Requires nonzero factors: at `t = 0` with no order atom the right side holds vacuously while `x = y` changes truth value (`orderIff_fails_at_zero_factor`).
- A parity description of the sign of `scaleOf t d` for nonzero `t` is not proved here.
- `HasDim` and `WellTyped` check dimensional consistency within one coherent unit system `s`: every variable and literal of dimension `d` is read in the same unit and rescales by the same factor `scaleOf t d`. The model has no per-variable unit tags and no unit conversions, so it says nothing about mixing two different units of the same dimension (for example metres with feet, or pound-force seconds where newton-seconds are expected); `HasDim` gives `x + y` dimension `L` for two lengths whatever units a writer had in mind for them. Unit-conversion calculi are studied elsewhere (Allen 2026, arXiv:2609.38242).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 9

Result 9 is `offset_units_dimension_check_overclaims` (`sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant`).

- The point sort models offset (interval) scales with a conventional zero, such as °C and °F. Thermodynamic temperature measured from absolute zero (kelvin, rankine) is a ratio scale, under whose changes sums of absolute temperatures keep their truth value; that setting is the main, ratio-scale language, not the affine toy (not proved here as a separate lemma).
- Does not show that `t₁ + t₂` has no meaningful reading in some other convention (Pint documents '383.15 °C' as one reasonable reading of '10 degC + 100 degC'); it shows that the toy formula's truth depends on the scale.
- A point literal `lit c .pt` denotes a fixed reference point converted into each scale (for example `0 °C` reads `273.15` in kelvin), not the numeral `c` in every scale.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 10

Result 10 is `point_vector_typed_formulas_affine_invariant` (`affineInvariant_of_pointVectorTyped`).

- The affine toy is an ordered one-dimensional affine space over `K` (an interval scale: positive scaling and translation, ratios of differences, affine combinations, order), with a single point dimension; it is not a general torsor and has no products of temperature differences with other dimensions (such as `J / K`).
- `AffineInvariant` quantifies over every scale `u`, including scales with `u.1 ≤ 0`, so it is strictly stronger than the positive-scales notion `PosAffineInvariant` (`posAffineInvariant_of_affineInvariant`; `affPosConst_posAffineInvariant_not_affineInvariant` shows the converse fails).
- The positive factor `a > 0` is part of `AffineInvariant`; the change `x ↦ -x` reverses the typed comparison `t₁ ≤ t₂` (`ptLe_not_invariant_neg`).
- `InvZeroLaw` is used by the rule for ratios of vectors (`vecDivVec`); that the fragment without such ratios is invariant without `InvZeroLaw` is not proved here. Expression covariance holds for every `a ≠ 0` (`AExpr.evalIn_act`), so formulas without order atoms are expected to tolerate `a < 0`; that formula-level corollary is not stated.
- Weights of affine combinations are constants of `K`, not computed numbers, and combinations are binary. Nesting binary combinations to get an n-ary one requires renormalized partial weights, which divide by zero when a partial weight sum vanishes (for example weights `(1, -1, 1)`); n-ary combinations are not proved here.
- Quantifiers range over all of `K`; a physical lower bound such as absolute zero is not modeled.
- The point sort models offset (interval) scales with a conventional zero, such as °C and °F. Thermodynamic temperature measured from absolute zero (kelvin, rankine) is a ratio scale, under whose changes sums of absolute temperatures keep their truth value; that setting is the main, ratio-scale language, not the affine toy (not proved here as a separate lemma).
- A point literal `lit c .pt` denotes a fixed reference point converted into each scale (for example `0 °C` reads `273.15` in kelvin), not the numeral `c` in every scale.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 11

Result 11 is `one_var_length_polynomial_linear_everywhere` (`oneVarLength_poly_eval_eq_mul`).

- One base dimension and one variable; expressions in several variables are not covered.
- Polynomial fragment; the rational fragment is `oneVarLength_eval_eq_mul`, which needs `0⁻¹ = 0` (`sqOverZero_not_linear_ratJ`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 12

Result 12 is `one_var_length_rational_linear_everywhere` (`oneVarLength_eval_eq_mul`).

- One base dimension and one variable; expressions in several variables are not covered.
- Does not cover operations outside the toy syntax (roots, absolute value, `max`, conditionals).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 13

Result 13 is `definable_on_positive_iff_linear` (`definableOnPos_iff`).

- The defining expression may mention other variables and dimensioned literals; the quantification over all unit systems and all readings of the other variables removes their influence. A notion that fixes the unit system, or fixes the other variables, is a different notion (see the escape hatches of `succ_not_definable_on_positive`).
- The requirement `Γ x = L` in `DefinableOnPos` matters: with `x` of dimension `1 / L`, the expression `1 / x` has dimension `L` and is not linear (`invVar_not_linear`).
- Functions of several variables, and readings `v ≤ 0`, are not covered by `DefinableOnPos`.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 14

Result 14 is `succ_not_definable_on_positive` (`not_definableOnPos_add_one`).

- Escape hatches proved to defeat the impossibility: (i) a total division with `0⁻¹ ≠ 0` (`addOne_definableOnPos_ratJ`); (ii) giving up dimension typing (`addOneDimless_control`); (iii) fixing one unit system: `x + lit 1 L` reads `v + s 0` in system `s`, so it computes `v + 1` in the reference system `s = 1` and not across systems (`addOneLength_control`). Further variations that are expected to defeat it but are not proved here: (iv) making `x` dimensionless (then `x + 1` is well typed); (v) fixing a second length variable `y = 1`, as in `x + y` (a parametrized notion that `DefinableOnPos`, which quantifies over all readings of the other variables, does not cover).
- Does not say that adding a constant length is meaningless: `x + lit 1 L` is well typed and adds one reference length, which reads differently in different unit systems.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 15

Result 15 is `max_one_not_definable_on_positive` (`not_definableOnPos_max_one`).

- The toy syntax has no `max`; the result is about computing the function `v ↦ max v 1` with toy expressions. It does not show that `max` is inadmissible on lengths: binary `max x y` and `max x (1 m)` are positive-homogeneous (not proved here, and not expressible in the toy syntax). The bare threshold `1` is what makes `v ↦ max v 1` scale-dependent.
- Stated as a closed instance over `Rat`; whether `v ↦ max v 1` is definable over `RatJ` (junk division) is not examined.
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Non-claims of Result 16

Result 16 is `inv_zero_convention_iff_typed_homogeneity` (`allHomogeneous_iff_invZero`).

- Does not show that `0⁻¹ = 0` is the right human reading of division by zero; it shows that among total conventions it is exactly the one compatible with homogeneity of typed expressions (under the stated hypotheses).
- Partial division (undefined at `0`) and IEEE 754 floating-point division (`±∞`, `NaN`) are outside the field model; these results neither establish nor refute homogeneity under partial or floating-point division.
- In the two-element field with `0⁻¹ = 1` and one base dimension, every nonzero unit change is the identity, so every typed expression is homogeneous although `0⁻¹ ≠ 0` (`allHomogeneous_iff_fails_gf2J`).
- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about real unit libraries (F# units of measure, Pint, mp-units, Boost.Units), about physical measurement practice, or about the calculi of the cited papers.

### Escape hatches

These are the weakenings proved, or expected, to defeat the impossibility results and the characterizations.

- **Result 14 (`succ_not_definable_on_positive`).** Proved to defeat it: (i) a total division with `0⁻¹ ≠ 0` (`addOne_definableOnPos_ratJ`, over `RatJ`); (ii) giving up dimension typing, since the dimensionless-literal expression `x + 1` computes `v + 1` in every unit system but has no dimension (`addOneDimless_control`); (iii) fixing one unit system, since `x + lit 1 L` reads `v + s 0` in system `s` (`addOneLength_control`). Expected to defeat it but not proved here: (iv) making `x` dimensionless; (v) fixing a second length variable `y = 1`, as in `x + y`, which `DefinableOnPos` does not cover because it quantifies over all readings of the other variables.
- **Result 15 (`max_one_not_definable_on_positive`).** A closed statement over `Rat`. Replacing the threshold `1` by `0` gives a definable function on positive readings (`definableOnPos_max_zero`, the positive control). Whether `v ↦ max v 1` is definable over `RatJ` is not examined. A binary `max x y`, or `max x (1 m)` with a dimensioned threshold, is outside the toy syntax, so the result says nothing about them.
- **Characterizations.** The `↔` of Result 8 fails without `InvZeroLaw` (`orderIff_fails_without_invZero_ratJ`) and at a zero factor (`orderIff_fails_at_zero_factor`); the `↔` of Result 13 fails without `InvZeroLaw` (`definableOnPos_iff_fails_without_invZero_ratJ`); the `↔` of Result 16 fails in the two-element field `GF2J` with one base dimension (`allHomogeneous_iff_fails_gf2J`) and over `RatJ` with no base dimension (`allHomogeneous_iff_fails_zero_dims_ratJ`). Result 1 has no hypotheses to weaken.

### Tightness status `unknown` and sub-hypotheses not examined

No hypothesis in any ledger has tightness `unknown`. Each bundled law hypothesis (`CommRingLaws K`, `FieldLaws K`, `OrderedFieldLaws K`) is marked `harmless` because every structure of the intended kind satisfies it; whether each individual law inside a bundle is needed is not examined. In Result 1, the third premise of `PosUnitInvariant` (`Positive (fun i => t i * s i)`) is part of the definition; it follows from the other two premises under `OrderedFieldLaws K` (`posUnitInvariant_iff_of_orderedField`), and whether the equivalence of Result 1 would fail without it in a lawless scalar domain is not proved here.

### Stronger conclusions that are not established

Each of these readings is tempting and is not a result of this package; refutations cite the proved theorem, and open cases are marked.

- *Every ill-typed formula changes truth value under some positive unit change.* Refuted in the toy: `cubeSum` is ill typed and `UnitInvariant` (`cubeSum_not_wellTyped_unitInvariant`, Result 6).
- *Dimension checking makes statements in real unit libraries or programs unit-independent.* Not established: no model–system relation is proved.
- *Typed expressions are homogeneous under any total-division convention.* Refuted in the toy for `0⁻¹ = 1` (`divXY_not_homogeneous_ratJ`). Homogeneity without `InvZeroLaw` for expressions with no division and no negative power, read in base systems with nonzero factors, is not proved here.
- *Plain dimension checking suffices for offset units.* Refuted in the toy by Result 9 (`sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant`).
- *An order atom at a dimension with a negative scale factor always changes truth value.* Not established: Result 8 quantifies over all formulas with order atoms in `O`, and individual formulas such as `x ≤ x` keep their truth value under `t = -1` (not proved here).
- *Clamping a length is inadmissible.* Not established: Result 15 concerns `v ↦ max v 1` computed by toy expressions; binary `max` is not expressible in the toy syntax.
- *`0⁻¹ = 0` is the correct reading of division by zero.* Not established: Result 16 characterizes it among total conventions by homogeneity, under its stated hypotheses.
- *The quotient used for plain readings is the space of physical quantities.* Not proved (Result 1, non-claims).
- *Affine invariance extends to affine combinations of more than two points.* Not proved (Result 10, non-claims).

### Disproved or dropped statements

None. Every statement listed in `results.json` is proved as stated in Lean, with the axioms recorded under Evidence; no statement was found false and none was dropped as unprovable.

## Evidence

### Kernel-check record

- **Toolchain.** `leanprover/lean4:v4.34.1`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52` (a lightweight tag, resolved through the GitHub API on 2026-11-21). Core Lean only; `lean/lakefile.toml` declares one `[[lean_lib]]` (`ToyUnits`) and no `[[require]]`.
- **Build.** `lake build` of a fresh copy of `lean/` succeeds under the pinned toolchain, with Lake's artifact cache disabled so that every proof is re-elaborated and kernel-checked. The sources contain no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declaration, `implemented_by`, `@[extern]`, `unsafe`, or `debug.skipKernelTC`.
- **Axioms.** `Lean.collectAxioms` was run on every declaration of the library (920 declarations; `audit/axioms.json`). Each depends on a subset of `propext`, `Classical.choice`, `Quot.sound`: 637 depend on none, 76 on `propext` alone, 67 on `propext` and `Quot.sound`, and 140 on all three.
- **Statement hashes.** For each Lean name referenced by `results.json`, `audit/statements.json` records the SHA-256 of the statement, i.e. of the Lean `repr` of the declaration's type, and the SHA-256 of its definition closure: the sorted list of lines `name : repr(type)`, followed by ` := repr(value)` for constants that are not theorems, over every package constant reachable from the statement through types, non-theorem values and inductive constructors, joined by newlines. Theorem bodies are excluded, so a re-proof leaves both hashes unchanged and a change to a statement or to any definition it depends on changes them.

### Result theorems

| # | Lean name | Axioms (`#print axioms`) | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|---|
| 1 | `Toy.Units.hasPlainReading_iff_posUnitInvariant` | `Quot.sound`, `propext` | `adc6cd4bf55a92bdc290ee5052617937535df669035c42ba495fdbdf1f1d1844` | `d8cb73aba580542ef7930b3b23622d6982c4991054e4abecadaeb2fe42cf9f2a` (61) |
| 2 | `Toy.Units.evalIn_act_eq_scaleOf_mul` | `Classical.choice`, `Quot.sound`, `propext` | `7a2c83ece1ddca157e2d9763504fd9a75c1e6799009e054df51483a34ec7c222` | `2b084fe0bb02ecc69213f1c90f6dd2a99a44a9101b8eafaeb8dd44be4eaa4386` (63) |
| 3 | `Toy.Units.unitInvariant_of_wellTyped` | `Classical.choice`, `Quot.sound`, `propext` | `3ed1bc5fe99e94d3c7d9a4b943e793f562abd059b3a549f13941ab8c8df13ea6` | `cc7724a2d2dae2d2cbd20d4709806e2bcb083e54364507b05c4746f80b2099c7` (103) |
| 4 | `Toy.Units.invariantAt_of_wellTypedAt` | `Classical.choice`, `Quot.sound`, `propext` | `fefe29bed84a0b5e0232cd4bcf6cc0ed701b623e95f9ae4ec3861ecbc9f2f9d7` | `842ad9cb45e511a2ad9d9a689d4c7e583c9580d7d6d169ff398a38c52111579b` (90) |
| 5 | `Toy.Units.sumMixed_not_wellTyped_not_posUnitInvariant` | `Classical.choice`, `Quot.sound`, `propext` | `fcbe5f97e0a5c3fd44b07bb82df2acec280a9e7b48ceddb87aa1c8b6de4ac494` | `7cbd617ce8f43431f9379e84b60bc59bd5af5a87279a05fd1205ba881ad7ea54` (83) |
| 6 | `Toy.Units.cubeSum_not_wellTyped_unitInvariant` | `Classical.choice`, `Quot.sound`, `propext` | `70f331c95640e68d2caf42f8691218f1d7bb2137d74cdc88fbde4ed154a63b61` | `4e2447df513b06871ad7b3df9466574b7a1f2cf8ed3d0b73b3d58adad37de13e` (83) |
| 7 | `Toy.Units.invariantAt_of_wellTypedAt_noOrder_of_ne_zero` | `Classical.choice`, `Quot.sound`, `propext` | `2fa9f35d0e25c6f6936a41a87a3cd8b62e841b399169e3a2a430c20bcb127df0` | `842ad9cb45e511a2ad9d9a689d4c7e583c9580d7d6d169ff398a38c52111579b` (90) |
| 8 | `Toy.Units.invariantAt_all_wellTypedAt_iff` | `Classical.choice`, `Quot.sound`, `propext` | `6b241d27d9d2abebdf13e02052b24dea74e3b9a2989f30648b2cb14737d35453` | `a84070ec2dcf51c7b27f932708745f00c96ac94ecd4e11e45ada0c9307d7351e` (100) |
| 9 | `Toy.Units.sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant` | `Classical.choice`, `Quot.sound`, `propext` | `af651caa91d06cca91f8bcd006a2da3aefb55de9dadfc44dfe42cc21d42ab2c3` | `a53a85e117b6ae4ca9a98435c8f363d11530841dae43c036b91707f68589a30d` (102) |
| 10 | `Toy.Units.affineInvariant_of_pointVectorTyped` | `Classical.choice`, `Quot.sound`, `propext` | `f00130f8eefe7855dd529251f93455f26c0a4518a0fa6696a996b29fba193ad6` | `a6f9c9fd680502f31fb4038c7bc021dd6d655a7d55c5c6d58ecc41ab5d480617` (105) |
| 11 | `Toy.Units.oneVarLength_poly_eval_eq_mul` | `Quot.sound`, `propext` | `d1358c4db252658b94051fc67cd619105fe52f977fdbb78d2a0f1e3312cdcc01` | `961f7e669d6332502a3ec0755cd8d2cdd336eae1cae401b9fd3bbaf799f73d3d` (67) |
| 12 | `Toy.Units.oneVarLength_eval_eq_mul` | `Classical.choice`, `Quot.sound`, `propext` | `8999bdc14b501f71adafbe9d33aa17f8ba065822e6c00cc3b457ca9d7d27220b` | `92f5ef59a43d1a0bee23ccc5f0c4220662b0946dae537a219c72e73f5b542a40` (72) |
| 13 | `Toy.Units.definableOnPos_iff` | `Classical.choice`, `Quot.sound`, `propext` | `2c85ffb9f2404af803d7bba1a5a6e5d59dff2ef0c831110a71472a7e57de21c2` | `60eab1c9d80521570e6da1d74e2912a1adf413a4b71145807534eda4fbc8f71a` (76) |
| 14 | `Toy.Units.not_definableOnPos_add_one` | `Classical.choice`, `Quot.sound`, `propext` | `6bbdd1b64e547f42914145138a1ed725dafdd9606c11f26082af390374101873` | `60eab1c9d80521570e6da1d74e2912a1adf413a4b71145807534eda4fbc8f71a` (76) |
| 15 | `Toy.Units.not_definableOnPos_max_one` | `Classical.choice`, `Quot.sound`, `propext` | `d055f04f0493cab4bdf6d4aaf1546f06a2a309623eb9ed29bf114d45f178f711` | `7c83039f58507bf1f6929d0476d5f5e491dea809aa3880f052af71d7e11bff06` (52) |
| 16 | `Toy.Units.allHomogeneous_iff_invZero` | `Classical.choice`, `Quot.sound`, `propext` | `dd0a409a04030a216c7a55939b4c248e544058ec1d2c66bfb43cb52bcb98c25d` | `7bf9351c6bb233fa9849955afb64bcd5f807c18ba94b534787997b71b39ddd3d` (64) |

### All declarations referenced by the result cards

Every Lean name that `results.json` references (results, auxiliary names, tightness counterexamples, non-vacuity witnesses and positive controls): 236 names, each with its axioms and its recorded hashes (`audit/statements.json`).

| Lean name (`Toy.Units.` omitted) | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|
| `ADimChecked` | none | `cc2fc837ef9e9cef858e06a3d6e20d4abca9f413239f731cb7a26d911ac907a8` | `470d1d7bb1f90361838c09f84b6226435f066fa8a196c8b3b26103be5d57990c` (12) |
| `ADimCheckedF` | none | `172fb7f54a0bb98ae9695761904cff7fd1f73f308351e60dc0b5032a3fbd98b6` | `d4e483d7a4cea7db51476ed1065cb4c20ad41f5f2d9ecbf3f8d9073706b7e9a6` (20) |
| `AExpr` | none | `3ea0c33f34748419e66520c18a218d1b21749a7a2b2bbcf2281dfdddc4b5088b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `AExpr.evalIn` | none | `29f6c53aceb2bce98a659a17b5b583a6f322aaef57091dd38c27bdc0b7ce0ed9` | `c43e863cbfe0f0dd921b0a40623eb6f51c31352e09af1508fed69157b571a83a` (15) |
| `AExpr.evalIn_act` | `Classical.choice`, `Quot.sound`, `propext` | `5f3c2c2f3bc0983a3f46cb2e94df979086918fa9fd79130939c7184173bc1f9f` | `9ddee59d49b0f78b033ac2e4e420d943b5b68bc4a138c3701d7b14044372abf4` (68) |
| `AFormula` | none | `3ea0c33f34748419e66520c18a218d1b21749a7a2b2bbcf2281dfdddc4b5088b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `AFormula.holdsIn` | none | `1a0384095a9f88682bda9dfaa96f82d75c468b6a533e53738e3f233f91796123` | `8b26a780d49e1c1e5ab52fe91c6e7edb8e1f947f92231994ad425eb97ed38ab0` (23) |
| `ASort` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ASort.act` | none | `d9d350afecfd0f211f8f77f16064adc9ac98fbc627be0d99c9447f1f9e4cfe7c` | `d8660fd25f290369db56df4cc4781dd164f6f2a60b16aa41095082f7883c21c0` (6) |
| `ASort.exp` | none | `d8ab68b9d66a33e8b2c61feed2cee109aa5857eedebe8a075305929ab00bc23a` | `b9eb5cd205dc8332238ebba9dab70c5be247a42123b3ff5c75bb835c3f2b28fd` (4) |
| `AddAssocLaw` | none | `db9ff872112c80b7cc817a0faaf44727a1d05b2194745bf8f2a524801750c062` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `AddCommLaw` | none | `54914844ba73b08e47c58e0edc175ca261ad0c2d3aaf72c943f73d21b8876743` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `AddLeMonoLaw` | none | `da0b857fbf9e29c28dc49330d5b8f02b62e191d04e03c5453bc01e7e949b9e40` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `AddNegLaw` | none | `652df4182b9a0abf3fb9d314f2eff23e725f2a8b9866478db7684e3581467617` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `AddZeroLaw` | none | `1ffe3ba17af59bc2b9b04479be85dc177d373c74a1e6798963eb51ebfad65eee` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `AffineInvariant` | none | `ceb5f05a4085b607b6e67cf7eec3384ecb76bd1b488014c7537e8c37efd434de` | `be090224d40eae5931560a3ba77f14c8a264d1b4f3c34106bdcb23075973f697` (22) |
| `AllHomogeneous` | `propext` | `84053bda6bb084175eb01af04526112ff6e21ec8be8b06da7de1fad43e539e5f` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `CommRingLaws` | none | `9b7457655cec7f39c786124875ea59ae25bb68852ad8f17b6f39c9f8a210e9df` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `Ctx` | none | `f90689f02c7655dad6c5a27959ac8ac133356b1596ff28fa512baf22ef8416cd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `DefinableOnPos` | `propext` | `e7c4085b339ab5c110ccbe5fbe42debdc6429e314cd43193c04a0e15ac34261b` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `Dim` | none | `f90689f02c7655dad6c5a27959ac8ac133356b1596ff28fa512baf22ef8416cd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Dim.div` | none | `e299b681cc3b6e30021aa9fc453778ef80299d0471ad5072d0682a5ea705d1ed` | `6bb1fa3d0c12d93e3bfbdb4dda2d8c1369da504c2a91f5f49aa770cbc1ddaa87` (1) |
| `Dim.mul` | none | `e299b681cc3b6e30021aa9fc453778ef80299d0471ad5072d0682a5ea705d1ed` | `6bb1fa3d0c12d93e3bfbdb4dda2d8c1369da504c2a91f5f49aa770cbc1ddaa87` (1) |
| `Dim.one` | none | `f0e351e803af60080a45d1fa0800280960e60cdf0513592eec0cab7d824f2707` | `6bb1fa3d0c12d93e3bfbdb4dda2d8c1369da504c2a91f5f49aa770cbc1ddaa87` (1) |
| `Dim.pow` | none | `d6497791eb5ccdb90f8c468e81f39e6b6ae76c55ab91af800bf51253264003de` | `6bb1fa3d0c12d93e3bfbdb4dda2d8c1369da504c2a91f5f49aa770cbc1ddaa87` (1) |
| `DistribLaw` | none | `fb11c5110e3ff9a0604bcaaa232407240e48953726e57f67b0e2c6f4b47d5e64` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `Env` | none | `3ea0c33f34748419e66520c18a218d1b21749a7a2b2bbcf2281dfdddc4b5088b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Expr` | none | `65ef5322577b04f59765d5245fac8cbe698a8dca1c25a4bb27b0b38fa03039ef` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Expr.dimlessLits` | none | `eee9475b19aa05ac2f7beaee96255ea46da7ecb23fcf585075960ba884bdc2a9` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `Expr.evalIn` | `propext` | `88eb1c7e19b83c9f831f46e53d866a0a1f3449f67691d1674047c7a59da476a3` | `a2bd78dcc958ebf841e660e9bd0b2bdac3543bb3c448d59d496e915bf59eb70f` (12) |
| `Expr.isPolynomial` | none | `eee9475b19aa05ac2f7beaee96255ea46da7ecb23fcf585075960ba884bdc2a9` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `Expr.onlyVar` | none | `7868f2e0dc7d5f396fe3f4a84526898562dd7db1d18331732a7e64d10a21a362` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `FieldLaws` | none | `10462e0be6db48b5602ee711f6a5a088a5a4e25cc3179cba49762176aaaec44a` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `Formula` | none | `65ef5322577b04f59765d5245fac8cbe698a8dca1c25a4bb27b0b38fa03039ef` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Formula.holdsIn` | `propext` | `b1914f57c411e36c64d24fe19570e93ec032109cf4507996c2f85b20316bcb88` | `087d7b7e35476f4e375086252899b7b208fc4854b2d4e8cde3e9030f366a24be` (20) |
| `GF2` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `GF2J` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `HasDim` | none | `086f319736203b46f5989fb28338dbde64fab9044b13b92ab769a0440ca976b5` | `d1e0ed360e7299c30b72aca038821477e3ae90bd98cf41ee382e24c5a5deced3` (10) |
| `HasPlainReading` | `propext` | `6041c06eeb8ca1067ea700dd19e68ad1c2af755a5ea4f1bfe5f5b91e5c1a8088` | `bbe0ca1d4fa0de958b992e3aeb0854c2e60c052a2d5063df6810fcdaecbd89bb` (20) |
| `HasSort` | none | `662ec1c2e2e8643d6a1f4006332a6142c3aadc18a95a8924c97c4772d50b0732` | `470d1d7bb1f90361838c09f84b6226435f066fa8a196c8b3b26103be5d57990c` (12) |
| `InvZeroLaw` | none | `932c81af9c33e5eaff44898068bae306d348d9b188c9c915ac12593cc6999b14` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `InvariantAt` | `propext` | `c87bad9667d54fb2e78f964fd18a150308710dc7756ae72913e62f85cfb8a560` | `bbe0ca1d4fa0de958b992e3aeb0854c2e60c052a2d5063df6810fcdaecbd89bb` (20) |
| `L` | none | `a56887fe74d96a869bc72c5bb52909ebeffaea6c8f7a162b9780717139e24958` | `6bb1fa3d0c12d93e3bfbdb4dda2d8c1369da504c2a91f5f49aa770cbc1ddaa87` (1) |
| `LeAntisymmLaw` | none | `bf9854d3f7fc3bab4d6c6f28e94c5e9a381e8aa94ea9a9894fca1373e335ca93` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `LeReflLaw` | none | `d634384b7cef04a75e28ba6b81de6ac2c0118d8fd1e815aa175d82263feb1a8e` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `LeTotalLaw` | none | `958c35fcb3d99c9682d3e279141154dfd9b05ed9967511857d844436f93dcdbf` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `LeTransLaw` | none | `19bce3e71559238a2df2df9e20f29a52be9cb7b3ad417815b2281119780436ea` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `LtIffLaw` | none | `cec83d8efb033c813191de285c895dc1ae5037152b4aaef62a82ed3bd9009012` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `MulAssocLaw` | none | `7010621cacadf8cba1bd851ba838c16899bf4b7c1101369304fd4d5deab5d9a1` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `MulCommLaw` | none | `e06ddf3e3c4a6d5f22fa8e65509a585ab161de47c6754542a0793f15f53faffe` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `MulInvLaw` | none | `dcce1b9ef5d4642f0220058c299f0b46cc17481322b6759743a4eb8d5d0e84bc` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `MulNonnegLaw` | none | `35960bd1e41c899f667322548c27c6d50cd80e9d1902cef86a7e5203bdd70888` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `MulOneLaw` | none | `6f8ccf9d1d31ac0326ee56c7f5fa06c6968c09ec18d9503b39ff6c468852e7b9` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `OneVarLength` | none | `2c2e46569dc290cb38c495998846d24f19551dc00edcee94c34f69c92badc537` | `d1e0ed360e7299c30b72aca038821477e3ae90bd98cf41ee382e24c5a5deced3` (10) |
| `OrderedFieldLaws` | none | `734bc322deb9ddfe8103d908e8a6a318903c27da4d95349fba056ba2ebcd7db8` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `PointVectorTyped` | none | `1d0c56b4bc340971884b6f4a1f78488248e7408874c9ef4a62b58bb9dc672b04` | `d4e483d7a4cea7db51476ed1065cb4c20ad41f5f2d9ecbf3f8d9073706b7e9a6` (20) |
| `PosAffineInvariant` | none | `3627d0f4e972879b543a0ae62917cca803df8e47bd04e79b8900830ffc0b8464` | `be090224d40eae5931560a3ba77f14c8a264d1b4f3c34106bdcb23075973f697` (22) |
| `PosSituation` | none | `6a5e240a3851fe6618afaf4f7f666d6d8099da7a7f129bf8f5d5df8da0666cba` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `PosUnitInvariant` | `propext` | `a0ac00d842ef134053fa2cf368d764a4e802430710c95dfc62391a1fbfc3d0a6` | `bbe0ca1d4fa0de958b992e3aeb0854c2e60c052a2d5063df6810fcdaecbd89bb` (20) |
| `Positive` | none | `11b3f90c826b7435342a304293c56f144c4a891cee3e8e70ea7d67c459479d77` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `RatJ` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `RatJ.ofRat` | none | `72347abf8ed5ad1fc536ea791e709ddd264a4db969f086843aa129aca71fb121` | `7fbb471429be92edcd5e6d02494ce1e0f1c3586a35aa0edb6d4b97cf8970921f` (1) |
| `RatJ.toRat` | none | `e9d22cc76b5bf29cb9249adf47db30131d8d48d58bfec577e67708a4234fa504` | `7fbb471429be92edcd5e6d02494ce1e0f1c3586a35aa0edb6d4b97cf8970921f` (1) |
| `ScalarOps` | none | `3ea0c33f34748419e66520c18a218d1b21749a7a2b2bbcf2281dfdddc4b5088b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `UnitInvariant` | `propext` | `fd8f7f8d257568fa4bac70992e4746e5516846551c4ccd04fa8cc58c1bbf1c9c` | `bbe0ca1d4fa0de958b992e3aeb0854c2e60c052a2d5063df6810fcdaecbd89bb` (20) |
| `WeightsSumOne` | none | `04d8cf109ed28d965f37316c85fb0aa3d92dfd6b262a273d8d986bb8460ac9d7` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `WellTyped` | none | `16dc07fa8f9f8cd46780dc9385c82fe44866c362e5491eb2a68df7ed411afaa9` | `b75ac567a74e3dece0efba519a6e65ddc69c19a17eb02ead9408685d5c285610` (18) |
| `WellTypedAt` | none | `0cfb29e5b8d81add8793272fe764ac70bdc69545b4e19606299607960a236160` | `b75ac567a74e3dece0efba519a6e65ddc69c19a17eb02ead9408685d5c285610` (18) |
| `ZeroNeOneLaw` | none | `676c52e63407b91693478ad2a62124debbde59d27735f83fe6b6edacc00da78e` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `aDimChecked_mixed_none` | `Quot.sound`, `propext` | `92a0731c80753228062b83ece3997f06ff9d589a7fa96d87d45b3775cea6d644` | `8cb9bec3f48b372b7258b39c71adcaf6deba866bd4c131fb48e114f6e6e03225` (25) |
| `aDimChecked_sum_example` | none | `a7489b8d64c919fe458cb083c00e2c27c0f9ee2e216f9b583d1fb9988c96ea8b` | `8cb9bec3f48b372b7258b39c71adcaf6deba866bd4c131fb48e114f6e6e03225` (25) |
| `actA` | none | `a40e557ac35737b455eebb6177ea48e6a90cbd3286acce68118c38c22b6484d8` | `2f61af6f960ea2a972842219217336b1191807e5819e4832d5580db7ee215612` (7) |
| `actEnv` | `propext` | `bd32ccc57c9f83eda9337a9016eb76bf19dc09147b7bad70bf3ca6a6dd9fda12` | `23b61b3daf18776d317717788f9329b6efb9bf147bda8dcbdfa4e697e0d07af0` (5) |
| `actEnv_example` | `Classical.choice`, `Quot.sound`, `propext` | `ac5a89889f4cc50faa84f96b0a70eb4853ac4360413ed874ec215a13a4719db9` | `68e01661212d4c3987dfca107ed42e49da61bb6c59eddbb266563c177d5a44ea` (21) |
| `act_examples` | `Classical.choice`, `Quot.sound`, `propext` | `de11d63ad33228d9683443340df01dffd71f8daef7d0bc359d1ea80f0523501c` | `e27086bdda8ac57c8b657598652e68306efc794de26c035d37ed56263c883c48` (15) |
| `act_vec_no_offset` | `Classical.choice`, `Quot.sound`, `propext` | `629ceb5510e2749120dd58b9c75876c4dca8240e962b1c20851a78da5d001654` | `e4d6469d5041ccbe8e22bc8faa19374cba3443bdb997cc865bd1cdf777ef123c` (14) |
| `addOneDimless` | `Quot.sound`, `propext` | `09187b89bb8b96ce2e3819c7e47c0eec2dcc87376b6dd7460f477616c5d07b60` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `addOneDimless_control` | `Classical.choice`, `Quot.sound`, `propext` | `006dcdc12d9c765647dea9e977a3391ab237cb84d3bcc426a326465c5c45f643` | `3a2416846c04544bebc06e99fcf165e87e3f07876f8a9d4380129d61348959b7` (57) |
| `addOneDimless_not_linear` | `Classical.choice`, `Quot.sound`, `propext` | `e844bc03cbcd40e0feb3d93e010310167da5b0457608c183796d2c7fb912b8e2` | `2f5a99e1fefab6766aee080417b4ab1df09653162cf761fe2d6033430ccabd10` (75) |
| `addOneLength` | `Quot.sound`, `propext` | `09187b89bb8b96ce2e3819c7e47c0eec2dcc87376b6dd7460f477616c5d07b60` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `addOneLength_control` | `Classical.choice`, `Quot.sound`, `propext` | `55c0d99a40e8188ad5f262927f13d37851b6ca686b8f08b16c9641add21e7364` | `7fd1dfa3e948674225c1bcf9bd91704caae8998f34d4e2578140a277e58dd0ea` (57) |
| `addOneLength_not_linear` | `Classical.choice`, `Quot.sound`, `propext` | `f151a36dd0247ed2bda311b769b9390cb4244448c376cad15db79aca443623e0` | `7ed2d7e3af749b9e400c3aaac661e2adc2abfea53217b2da0f42fcc0217e71f0` (75) |
| `addOneLength_not_oneVarLength` | `Classical.choice`, `Quot.sound`, `propext` | `cc8d794b6a203a5943022cb3dea96ddba2b599cbe26ae484b4cc5ba465c43265` | `dd9de2ab1ea45706734eb0c36a358510bbe0cb817092e08acfcd1dcac26ee45a` (37) |
| `addOne_definableOnPos_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `dcf18ef23fd9586b08526fe469122f7b7a3f0026ab73102ea9e21b92d5b0a8be` | `ec48a6c61187d77a5695b8b5f9c0c039c22d950342be60a7095b63faefe5b15c` (80) |
| `affPosConst` | `Quot.sound`, `propext` | `bafdb2a1cf90a31fea0037a85822eb5841ebd8e90e68a2faf75e0ec768f07d8b` | `d4e483d7a4cea7db51476ed1065cb4c20ad41f5f2d9ecbf3f8d9073706b7e9a6` (20) |
| `affPosConst_posAffineInvariant_not_affineInvariant` | `Classical.choice`, `Quot.sound`, `propext` | `bb2a531537057540384820c3a58d9ddf9a631245e62dcc14c606156449f9af1c` | `00c0e49565f1c2ff0e5d2d5ebc2eefd4488318ba0edd7ee1bf29cc3ab62de5d7` (57) |
| `affineInvariant_of_pointVectorTyped` | `Classical.choice`, `Quot.sound`, `propext` | `f00130f8eefe7855dd529251f93455f26c0a4518a0fa6696a996b29fba193ad6` | `a6f9c9fd680502f31fb4038c7bc021dd6d655a7d55c5c6d58ecc41ab5d480617` (105) |
| `allHomogeneous_iff_fails_gf2J` | `Quot.sound`, `propext` | `9ff5dcf404b786f9cf269317ee37823f01578b1c5684358d85b76f4b1655179c` | `6c4d4c46180280410cc60b91829c5ba35715aff31a9ae604a3df9582f3497f2a` (66) |
| `allHomogeneous_iff_fails_zero_dims_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `10b07a20c2cc92518c63ffd455310d08ae5d53f4e6aaa4f765252ecc43a95de4` | `86fc0ddaeccd65ce9e5340b4733804c7a154c925d7b396ba091a8ad61cca0676` (68) |
| `allHomogeneous_iff_invZero` | `Classical.choice`, `Quot.sound`, `propext` | `dd0a409a04030a216c7a55939b4c248e544058ec1d2c66bfb43cb52bcb98c25d` | `7bf9351c6bb233fa9849955afb64bcd5f807c18ba94b534787997b71b39ddd3d` (64) |
| `allHomogeneous_rat` | `Classical.choice`, `Quot.sound`, `propext` | `2018213923d86a49beb1a651612758796575692528d62e859e6b83232cb19b5c` | `37bd42ad355f9099639488e702cb93bedd74bce9b79394572e0858e917752e00` (50) |
| `celsius` | `Quot.sound`, `propext` | `347435015892c2d54e15756ec3b580c4198bb1f242b1442ccf598cb3efc48aef` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `celsiusToFahrenheit` | `Classical.choice`, `Quot.sound`, `propext` | `347435015892c2d54e15756ec3b580c4198bb1f242b1442ccf598cb3efc48aef` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `celsiusToKelvin` | `Classical.choice`, `Quot.sound`, `propext` | `347435015892c2d54e15756ec3b580c4198bb1f242b1442ccf598cb3efc48aef` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `combSumLe` | `Quot.sound`, `propext` | `bafdb2a1cf90a31fea0037a85822eb5841ebd8e90e68a2faf75e0ec768f07d8b` | `d4e483d7a4cea7db51476ed1065cb4c20ad41f5f2d9ecbf3f8d9073706b7e9a6` (20) |
| `combSumLe_weights_tight` | `Classical.choice`, `Quot.sound`, `propext` | `5d30ab09e51c16e992f2e0af8ed045adb5addb5899aa10494ea4ca686b169104` | `3abfd08b218d01707fc2c1956b6d0667f19846b16ee4375a7286155b136587b4` (108) |
| `ctxDiv` | none | `9e00ed91cdc1cb02bf1b6fe1a3c782d22bc33351d12e498c2bf3f842fa05268f` | `e855eb732b6c61216ccf12330d02a92fbd24a12a851f8adad2f97eced1d6b50a` (2) |
| `ctxInvL` | none | `9e00ed91cdc1cb02bf1b6fe1a3c782d22bc33351d12e498c2bf3f842fa05268f` | `e855eb732b6c61216ccf12330d02a92fbd24a12a851f8adad2f97eced1d6b50a` (2) |
| `ctxL` | none | `9e00ed91cdc1cb02bf1b6fe1a3c782d22bc33351d12e498c2bf3f842fa05268f` | `e855eb732b6c61216ccf12330d02a92fbd24a12a851f8adad2f97eced1d6b50a` (2) |
| `ctx_eq_L_of_poly` | `Quot.sound`, `propext` | `9546325728790649aa174de8731728b0aa4b74ad07ccd3700ccde20927803b2a` | `622d8baef6e19052dc0ce26b49f75f141687be2f09c814779f263d2c30349e83` (35) |
| `cubeOverSquare` | `Quot.sound`, `propext` | `09187b89bb8b96ce2e3819c7e47c0eec2dcc87376b6dd7460f477616c5d07b60` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `cubeSum` | `Quot.sound`, `propext` | `cca76e884bf0eedebedb9a1426de8f7c2a1c34c57df5df45e7607e7aa154c0a0` | `298f7a73d66da2bec60a99fbc3e69916c8f0b410af8823fdfcc25e091cb224dc` (17) |
| `cubeSum_not_invariantAt_neg_one` | `Classical.choice`, `Quot.sound`, `propext` | `dab077fb57b9181b8ccd291fc7550b6321233063ab9b49f48ef8eb926e0ee902` | `d1e1b79a6e532063251c3817075c411e136f28b556134fda7025cfefc9d88087` (59) |
| `cubeSum_not_wellTyped` | `Quot.sound`, `propext` | `5def22422458218f163eed17e04ad311297f2f155a8396a3e59221d4914d4b0e` | `8c6b6a1d45bc2b74a95d65dd6e1268bc9e0c6869d4858d13476d048351af877d` (42) |
| `cubeSum_not_wellTyped_unitInvariant` | `Classical.choice`, `Quot.sound`, `propext` | `70f331c95640e68d2caf42f8691218f1d7bb2137d74cdc88fbde4ed154a63b61` | `4e2447df513b06871ad7b3df9466574b7a1f2cf8ed3d0b73b3d58adad37de13e` (83) |
| `cubeSum_unitInvariant` | `Classical.choice`, `Quot.sound`, `propext` | `57f8e3f3b014791bbc1140fbb1c31b37ef5698913827f6e5fc168f07477ee260` | `711f91051494669f8224e804919b9a0052520b476772dd7b8958bc00b46e471c` (63) |
| `definableOnPos_iff` | `Classical.choice`, `Quot.sound`, `propext` | `2c85ffb9f2404af803d7bba1a5a6e5d59dff2ef0c831110a71472a7e57de21c2` | `60eab1c9d80521570e6da1d74e2912a1adf413a4b71145807534eda4fbc8f71a` (76) |
| `definableOnPos_iff_fails_without_invZero_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `246db48abd939013d77b37e29a60bfe3aca357936af55c6eef8fb2580e915d57` | `ec48a6c61187d77a5695b8b5f9c0c039c22d950342be60a7095b63faefe5b15c` (80) |
| `definableOnPos_max_zero` | `Classical.choice`, `Quot.sound`, `propext` | `a3fda596d91f0e3dcbfc07f7b5cd5316e457358730ca619d46c8f30bedaec190` | `7c83039f58507bf1f6929d0476d5f5e491dea809aa3880f052af71d7e11bff06` (52) |
| `definableOnPos_two_mul` | `Classical.choice`, `Quot.sound`, `propext` | `6a23d9e4c719de1399d3decd3274c4570543ee5e01a4b77059ee45d6ace8194b` | `7c83039f58507bf1f6929d0476d5f5e491dea809aa3880f052af71d7e11bff06` (52) |
| `dim_area_ne_length` | `propext` | `ec688be641091158d541d590083ba2ef3f9e1a42e923bfe39dd5a1b656fcc278` | `eb77161027d9607814891a6635cc4739ced3c4c9d945b255133b3a654ef99c77` (3) |
| `dim_examples` | `Quot.sound`, `propext` | `ec33da0cb327caf273823f68babdae7d97139e49d528ed35c2b1f793adc58f47` | `498365a279ac674c4d4c2b93629ad10be3d6204d86901f71c7d5bd0f2c54b968` (5) |
| `divEq` | none | `7f69d6efd87d8cd581cc8728de5116f8528b4398b2743e7b8345d961ed021146` | `6bb921daf452231a8e0035420b13825d5781e498967c86a339ff124a99d5b539` (18) |
| `divEq_not_invariant_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `a858791eb8dbf457cbcdd16103fc41c7ac65e5ad5a09cd12a9a80e34faf2733a` | `a85df76bd75d6861c7ead55955a332dad012e0deb94c527e4ff1f3f953056eeb` (97) |
| `divLe` | none | `7f69d6efd87d8cd581cc8728de5116f8528b4398b2743e7b8345d961ed021146` | `6bb921daf452231a8e0035420b13825d5781e498967c86a339ff124a99d5b539` (18) |
| `divLe_engine_tight_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `4edb2bda9dd3f7741adea31292291157b26886bf69aedc473f6e9bef42150331` | `13e9b0eeb0a245a8fbf56fe28828d32c001504662058b28e531f57d22eecd776` (97) |
| `divLe_not_unitInvariant_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `6f53b1640dd8313ed2a86607d13117d95b317abd847690a83509f5f57bf5200f` | `450597c836dea9a3ce1817c18d4ba3fa4fb8050c7e514acccd857caea3cf5ca0` (111) |
| `divXY` | none | `085073b6bd217e517b51ee0d6ce81f196f5483eeee72d95ad20a829ae4c57828` | `6a7904e2137053ff75e306211fd8462140d7da9210ee5a50ca409b78ced758d6` (10) |
| `divXY_not_homogeneous_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `3c98a09198c85d2a6ee626724bbfd7aba3048cb4a4a5c00b450597626cccd657` | `11f160462b308bd7152892bc3dd20e59f587cf02b6c193909d6576ee15b0c529` (70) |
| `dropUnitLe` | `Quot.sound`, `propext` | `cca76e884bf0eedebedb9a1426de8f7c2a1c34c57df5df45e7607e7aa154c0a0` | `298f7a73d66da2bec60a99fbc3e69916c8f0b410af8823fdfcc25e091cb224dc` (17) |
| `dropUnitLe_not_wellTyped_not_posUnitInvariant` | `Classical.choice`, `Quot.sound`, `propext` | `dfd8a96f34c5927a79eeb6046f545f30bbff3903fba6c6ffa54e7430864f1240` | `79fe97e8ab43ef5dfa4eb4cea392ce0bd287ceef8a632fc45997975296639eb6` (83) |
| `eqXY` | none | `cca76e884bf0eedebedb9a1426de8f7c2a1c34c57df5df45e7607e7aa154c0a0` | `298f7a73d66da2bec60a99fbc3e69916c8f0b410af8823fdfcc25e091cb224dc` (17) |
| `eqXY_engine_tight_zero` | `Classical.choice`, `Quot.sound`, `propext` | `b49cc1663d496b84a9b93580ec74ebebfa5960ff1a5b3747762c15c8f3755db1` | `f207d7702970d23963d2fb2d3818c9931465c683d94d82238116c8a0bcef77ed` (94) |
| `evalIn_act_eq_scaleOf_mul` | `Classical.choice`, `Quot.sound`, `propext` | `7a2c83ece1ddca157e2d9763504fd9a75c1e6799009e054df51483a34ec7c222` | `2b084fe0bb02ecc69213f1c90f6dd2a99a44a9101b8eafaeb8dd44be4eaa4386` (63) |
| `evalIn_lit_examples` | `Classical.choice`, `Quot.sound`, `propext` | `c6acc2c40683f9441ac7917ef1c89c21584639e1c79157e7363c045f0c996e3a` | `6115c17cb8a19022e78b362920b2640dd4c48c1a36c2cd654a98634628da6b99` (37) |
| `evalIn_zero_of_dim_ne_zero` | `Classical.choice`, `Quot.sound`, `propext` | `f2f55e6b6c077c4d30a31a5ce4abbfd2a05c92b6346a36217926837e366d582e` | `65028c5e182adcf6e313c5a7092c153c56484a3c2514dedcd4c5a16f0ea0d194` (65) |
| `finProd` | `propext` | `af1ad2f325fe688e11c591be876474b9ed2500734403a4c5d2b6ec5d6f7836b8` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `gf2J_eq_zero_or_one` | none | `d1fe1e99f7db59f78e7ff3bf6cf6be9492168b3ccd4a83b51e301a6ce537740f` | `ccf96aeb9b004f8ecb4812f2aed4025e39454b85f6a0401d67a6145c532b9dda` (6) |
| `gf2J_fieldLaws` | none | `29aeacdaf574fdc4e1ec7fb81d2ded7dc332f4de16edf606179d9886c20c3c1e` | `9cbb221cf197854bf10ec00a149f63a365b1a5cd1a0af83129cd8b187fe01514` (24) |
| `gf2J_not_invZero` | none | `aeb1b1ebd71707186e7b62f7a27beec041ca924bc776038c11833dfcc70f14ff` | `20c2f6940cfb7cc26e5d9c08a618e582a4d209864c972e35988d9184a90eef6d` (7) |
| `gf2_fieldLaws` | none | `d8073a24c0cc9f8d9cdd5f64877958002f4c9cc337c0be181db47bd4116923d9` | `e19e492cba55b77981c8c2c22db3f266789905cffa2dc55601217861901a09aa` (24) |
| `gf2_invZero` | none | `4ed28afc2ad752fd97b651b8de2c867d599b574bf36a5317d99e6854585ccee5` | `60da946931fe363af72e6766f4c4d51f3e13b021ee7705a76ee353e72aae21c8` (7) |
| `gf2_not_orderedFieldLaws` | none | `e714e315d949dc409767ac6fc4caf014b4d485047e3777d568912009ac397ec0` | `c72e6b2f1b48b25a50b9497c4f541ef28765099024924f37873c05991a008840` (35) |
| `gf2_one_add_one_eq_zero` | none | `00b3db3cf1137be8f15352ce5a8f5b619c4456f056f963fd4756c1f722032e42` | `a629abe4be26c57aa2e0675e44d76524693139887108e59435623fd9d6da2c9f` (7) |
| `hasDim_area_example` | none | `eafb5e90160da38f7744667716e65f49564df0ecc34db788c653c3fd5a555f0c` | `e48d929db1a7d4416d90c6efb8ee47772c422b99c7aebf8786d8e53b23cea158` (23) |
| `hasDim_sumMixed_none` | `propext` | `cb0beecccd512592db820e2e48c08c3c730a97a24404a4b0b2fe9e5a74c09892` | `e48d929db1a7d4416d90c6efb8ee47772c422b99c7aebf8786d8e53b23cea158` (23) |
| `hasPlainReading_iff_posUnitInvariant` | `Quot.sound`, `propext` | `adc6cd4bf55a92bdc290ee5052617937535df669035c42ba495fdbdf1f1d1844` | `d8cb73aba580542ef7930b3b23622d6982c4991054e4abecadaeb2fe42cf9f2a` (61) |
| `hasSort_ptSubPt_example` | `Classical.choice`, `Quot.sound`, `propext` | `2153f8cade175f3ebc64aee5d21a6766fd621915f38e8cc2e5832bd1884bc798` | `3b57e1f79d81bf7a3eeecedcf2d23a8af055a3a6ede440dedc9e3ec22472932a` (37) |
| `hasSort_sum_none` | `Classical.choice`, `Quot.sound`, `propext` | `5b0850bb40428268cceb4f24417cb896931333251042a080f5f158d32decacdc` | `3b57e1f79d81bf7a3eeecedcf2d23a8af055a3a6ede440dedc9e3ec22472932a` (37) |
| `instScalarOpsGF2` | none | `b6f158c76e90fe5c901c30b9668d162dbdc0f68b1723c8e758dd295bb2d746d1` | `13d5763e47f2f98cd99a4cb11186ae05686138484bedb82d1a5bf5d84e45374b` (3) |
| `instScalarOpsGF2J` | none | `4ab723ed3ad435b33dcb368fdaccd70da79a9c17e27261bf773cbfc82d0874ae` | `452c9e90478cd4740b671cab047c2548a17eb25b972e4ff8dd05ad0c92988aff` (3) |
| `instScalarOpsRat` | `Classical.choice`, `Quot.sound`, `propext` | `a0628f96942fbf3840cd52d0757de699abaacac0b21baea67dec156e9da5bc2a` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `instScalarOpsRatJ` | `Classical.choice`, `Quot.sound`, `propext` | `f9fec4410c694042218fdaddd69dd43f0cee9b1f2d66ed03e1cc2893aa179e11` | `64b3a361e1e4ad30584ddc4beee604f0f74588648e1a8c889e3d679c3011ed29` (3) |
| `intOps` | none | `05ca5a1a6c9a34cc8676924cd4cb66e32e882be8bc127f4e7e7afaaacb674364` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `intOps_not_mulInv` | none | `eaba7b357b31793a458201f4a238398c915a5d48bbbbdb606d93c25999db77c7` | `b1cc0b28be7c01618d44a0ebab32b9f492b99ac9fe488ef148d503287e11a5bc` (8) |
| `invLLit` | `Quot.sound`, `propext` | `085073b6bd217e517b51ee0d6ce81f196f5483eeee72d95ad20a829ae4c57828` | `6a7904e2137053ff75e306211fd8462140d7da9210ee5a50ca409b78ced758d6` (10) |
| `invLLit_not_homogeneous_zero_system_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `fd54fdc633601ace2140c0e03b805fac389fd518ab81f80a52ebbf08ecebec77` | `91bb604644e49819fc967f55eae5ec92681ddc32226750cf19ab47174f08cdfa` (74) |
| `invVar` | `Quot.sound`, `propext` | `09187b89bb8b96ce2e3819c7e47c0eec2dcc87376b6dd7460f477616c5d07b60` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `invVar_not_linear` | `Classical.choice`, `Quot.sound`, `propext` | `feeb618f0096268ac12bb8fd64528fd7fb543fa04abcb90075f96ba677d6005a` | `f36ce17a02ba52b2c744b5d2b281b08b56e8b974238fa6f33f9c3df67c33a52b` (75) |
| `invariantAt_all_wellTypedAt_iff` | `Classical.choice`, `Quot.sound`, `propext` | `6b241d27d9d2abebdf13e02052b24dea74e3b9a2989f30648b2cb14737d35453` | `a84070ec2dcf51c7b27f932708745f00c96ac94ecd4e11e45ada0c9307d7351e` (100) |
| `invariantAt_of_wellTypedAt` | `Classical.choice`, `Quot.sound`, `propext` | `fefe29bed84a0b5e0232cd4bcf6cc0ed701b623e95f9ae4ec3861ecbc9f2f9d7` | `842ad9cb45e511a2ad9d9a689d4c7e583c9580d7d6d169ff398a38c52111579b` (90) |
| `invariantAt_of_wellTypedAt_noOrder_of_ne_zero` | `Classical.choice`, `Quot.sound`, `propext` | `2fa9f35d0e25c6f6936a41a87a3cd8b62e841b399169e3a2a430c20bcb127df0` | `842ad9cb45e511a2ad9d9a689d4c7e583c9580d7d6d169ff398a38c52111579b` (90) |
| `linearWitness` | none | `cc0dd9a8f9bebdab8073d1d91999dd5f4e035b577f39b601365e2c9dd8162114` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `meanLe` | `Classical.choice`, `Quot.sound`, `propext` | `bafdb2a1cf90a31fea0037a85822eb5841ebd8e90e68a2faf75e0ec768f07d8b` | `d4e483d7a4cea7db51476ed1065cb4c20ad41f5f2d9ecbf3f8d9073706b7e9a6` (20) |
| `meanLe_pointVectorTyped` | `Classical.choice`, `Quot.sound`, `propext` | `1c56a248168e24792cd28ff2df269151c9fa512f4e2aab2f0ea42260e90d6fff` | `ed28b582576cc9fadf3ae9b2ee7b6d1d4423bb6dd14b044f88443c2d8fdf344b` (55) |
| `nonnegL` | `Quot.sound`, `propext` | `cca76e884bf0eedebedb9a1426de8f7c2a1c34c57df5df45e7607e7aa154c0a0` | `298f7a73d66da2bec60a99fbc3e69916c8f0b410af8823fdfcc25e091cb224dc` (17) |
| `nonnegL2` | `Quot.sound`, `propext` | `cca76e884bf0eedebedb9a1426de8f7c2a1c34c57df5df45e7607e7aa154c0a0` | `298f7a73d66da2bec60a99fbc3e69916c8f0b410af8823fdfcc25e091cb224dc` (17) |
| `nonnegL2_invariantAt_neg_one` | `Classical.choice`, `Quot.sound`, `propext` | `8a6275508747358fc2a2f0859ac861f2ca9076e4f53b2377ad26607cfcec8dbc` | `f51bda5fd901a7239b9193a3caf33bfcd19e86cf26c07dd0524fdbb63cc13556` (60) |
| `nonnegL_engine_tight_neg_one` | `Classical.choice`, `Quot.sound`, `propext` | `1bde3d3efa3862cc6ee3e003fb1ffa323904e49e0b0b72fb89596489e7b29dd0` | `6618d7da3e8cb6af038d6461a02d1bdabe1e910047144535d448f8d9d8c1c80a` (94) |
| `nonnegL_hasPlainReading` | `Classical.choice`, `Quot.sound`, `propext` | `bbe09fc64ba636b13aaf7dc46fdd7625c10ebd532116b4c70b6b2d8fd3faa37c` | `f75f7d66dd84948b65ce4fa29c826df6bafc357a32c5ecb9bd37e5814c34185b` (64) |
| `nonnegL_noOrder_tight_neg_one` | `Classical.choice`, `Quot.sound`, `propext` | `fc58cae485d2f6c8f340a3da3ad08b809110cd7a1b8d6a34eca9e4642c4efdb2` | `6618d7da3e8cb6af038d6461a02d1bdabe1e910047144535d448f8d9d8c1c80a` (94) |
| `nonnegL_not_invariantAt_neg_one` | `Classical.choice`, `Quot.sound`, `propext` | `726cbc72c670620fd940e8c4de18bd6d2bef66ea5d1f803e96d3b84cc2fea27e` | `0a9057131521c12298918be7b7f20d6d22ea3431061a228843ae9da457e0194b` (59) |
| `nonnegL_not_wellTypedAt_noOrder` | `Quot.sound`, `propext` | `2c02658a5ca671a4705672e79d0fcca86fc6dfa4f708b67d92ca5319df559430` | `2065e4c6c980d1d0bdd2c19a3895ac0d98afcda8a771c6a1965d11a961221a3c` (41) |
| `nonvacuous_affine` | `Classical.choice`, `Quot.sound`, `propext` | `940e3c30662917087c7bc8c779fae93ab3ae1354c5d5039a4703b6491ebd094c` | `e02570d41dfb39eef1986f731589faff91ecfd017c5355183339548032add6f7` (86) |
| `nonvacuous_allHomogeneous_iff` | `Classical.choice`, `Quot.sound`, `propext` | `b832151716d54ad7d2b9c84082d878d63147c1a4544278cf3cc0e2523afe24e1` | `25d7234cff65aa694ebba7ba9f9f23ddfc4f1e92de58d87dbdc031c2889265dd` (23) |
| `nonvacuous_characterization` | `Classical.choice`, `Quot.sound`, `propext` | `621e2de11f98b9a18d3008d9d27ea6da5584c0538cd1fb9a04666dc04444e1f7` | `98dfebcece554fa29557bd1a0fce245e3877d4b19131670338982e49753f6f02` (35) |
| `nonvacuous_engine` | `Classical.choice`, `Quot.sound`, `propext` | `ffcfd737334a59762e240e5b5de773dd16ae8c291051b09cc2e1d576f5d2b376` | `67fb5264e90be7b6cf501215ef807f639c9fbd4a19fe56a5ca5195287d0edcaa` (74) |
| `nonvacuous_homogeneity` | `Classical.choice`, `Quot.sound`, `propext` | `2ba7f74870b01dfa3a18aa40095882fa5ccce7625387d392b96d11ad36e626dd` | `a4390ebf537e37e66e4cef0f742cd7a3a87cfab89e6487cd60eca3de5691298e` (49) |
| `nonvacuous_noOrder` | `Classical.choice`, `Quot.sound`, `propext` | `b48dfd65e3cb8e7df1112a4e4fda8ae8b7854ec0fcf70fc6b536191383ee1b9e` | `2708481c5a57a2e2cab3fb38617a06b7e5dbd1cb7c801af31e915be57d3a5a37` (65) |
| `nonvacuous_oneVarLength` | `Classical.choice`, `Quot.sound`, `propext` | `afc5e0be46b008dfa87f811e9d39e404738f86715111559cd37bccfe2479302f` | `af1ce3d90eb584a28de1e424a016525a9fa7cfe68a457cd86d7f07a7f60367db` (61) |
| `nonvacuous_oneVarLength_gf2` | `Quot.sound`, `propext` | `576d47463cdecc31ab93c1072b4e647bc3f7967ef5a4cdce130baec93f7504cf` | `c04d8175e5937447d09822e58215c7305c65fcdd282704e98b7d71bd0109ca1f` (73) |
| `nonvacuous_poly` | `Classical.choice`, `Quot.sound`, `propext` | `0a752f83cb549eb8028758ce6818bd5156c47b5b9d80b3d5777e20e4cbae64c5` | `3d0e8f1e9b98e16673f8e8afe8fccde7b1fd867e1b58b683431dcb22fe343857` (55) |
| `nonvacuous_unitInvariant_of_wellTyped` | `Classical.choice`, `Quot.sound`, `propext` | `f5e308249488e8a1a36d5c4da8c1fe540558834a0d22c221f4d008f51f1f8b55` | `c0a2fd15848cf857aa9877add59402ef023a0d0b0735ab07d9f20f2c557cc3c1` (77) |
| `not_allHomogeneous_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `31246c6bccc003a609850f365b0591fe3581af3987e854f7a76279a95e1ad5b9` | `0890448daedf8449789831a49dce3a7097e2083e15c4c7a6566f31e0a877710b` (53) |
| `not_definableOnPos_add_one` | `Classical.choice`, `Quot.sound`, `propext` | `6bbdd1b64e547f42914145138a1ed725dafdd9606c11f26082af390374101873` | `60eab1c9d80521570e6da1d74e2912a1adf413a4b71145807534eda4fbc8f71a` (76) |
| `not_definableOnPos_max_one` | `Classical.choice`, `Quot.sound`, `propext` | `d055f04f0493cab4bdf6d4aaf1546f06a2a309623eb9ed29bf114d45f178f711` | `7c83039f58507bf1f6929d0476d5f5e491dea809aa3880f052af71d7e11bff06` (52) |
| `npow` | none | `affc49b5dbf6ffbab122d3d3ee0b187bca21fd693e10a075070230ad3b71939f` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |
| `oneVarLength_eval_eq_mul` | `Classical.choice`, `Quot.sound`, `propext` | `8999bdc14b501f71adafbe9d33aa17f8ba065822e6c00cc3b457ca9d7d27220b` | `92f5ef59a43d1a0bee23ccc5f0c4220662b0946dae537a219c72e73f5b542a40` (72) |
| `oneVarLength_eval_eq_mul_of_ne_zero` | `Classical.choice`, `Quot.sound`, `propext` | `d449bbc4b75036da14fb372e8720b877415c5b1f211486e9686f986de06deed3` | `92f5ef59a43d1a0bee23ccc5f0c4220662b0946dae537a219c72e73f5b542a40` (72) |
| `oneVarLength_poly_eval_eq_mul` | `Quot.sound`, `propext` | `d1358c4db252658b94051fc67cd619105fe52f977fdbb78d2a0f1e3312cdcc01` | `961f7e669d6332502a3ec0755cd8d2cdd336eae1cae401b9fd3bbaf799f73d3d` (67) |
| `orderIff_fails_at_zero_factor` | `Classical.choice`, `Quot.sound`, `propext` | `d0e3d686606c3948deb3e4d9e236dc8b98e51cde498600c7d4b51ae02b0e6833` | `ff22ef2562c70b768cb37c75d6103b6fdc2105300d18fee986309e16ce633149` (101) |
| `orderIff_fails_without_invZero_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `b0cc645112d6c29bf40759988aea73389119f603714b21bf03dc301aa34339d0` | `0d15e2f845b5d625656d7d11017ee3fb76e380ac02aefdd019f71b6439273a5a` (104) |
| `polyWitness` | `Quot.sound`, `propext` | `09187b89bb8b96ce2e3819c7e47c0eec2dcc87376b6dd7460f477616c5d07b60` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `posAffineInvariant_of_affineInvariant` | none | `76770c53ee4c82ef8745d00d090e60b7b8a4b5562c11770ebfbdb7b0e1f35206` | `16b72b49ddd0fee17b919d494c694f2cf9ae077a69be5d7f6b2ccb6cb36b2f1f` (54) |
| `posConstFormula` | `Quot.sound`, `propext` | `cca76e884bf0eedebedb9a1426de8f7c2a1c34c57df5df45e7607e7aa154c0a0` | `298f7a73d66da2bec60a99fbc3e69916c8f0b410af8823fdfcc25e091cb224dc` (17) |
| `posConstFormula_posUnitInvariant_not_unitInvariant` | `Classical.choice`, `Quot.sound`, `propext` | `2dea226e3109b1a1a93606c9dc4e3419686987c1f4f3aeda1b4d6613c8d162a9` | `9dadca4e3fac4ec89df1b600c7f3eee0375b3fc18e0166945926be0aacecdc45` (65) |
| `posUnitInvariant_iff_of_orderedField` | `Classical.choice`, `Quot.sound`, `propext` | `89f5c9ef119ba65d7b8c14d690b437bf521a1ea34ca79e17d97fcbdd075126bf` | `65c2220e73941c8397468257a84faaa4e8b2942053627714c3161ab1481a5d3a` (81) |
| `posUnitInvariant_of_unitInvariant` | `propext` | `2f228efcbdcd8cd5b6362bbcea7481a51759b1d972ca4742053199ad7c105fce` | `703245989377a0c4e03fd3786f1d0f5c2b716876ee1140b6dfb6364ffe892263` (60) |
| `positive_examples` | `Classical.choice`, `Quot.sound`, `propext` | `5cf1fedc19f563525f3bcd6e57ffcfdb49fdd2b285d42e85197106bed574f1d3` | `369bff93ff66177966effaba78d3d3fbb5bc05d3a33c3d2a20a24f7922de5ec8` (6) |
| `ptLe` | none | `bafdb2a1cf90a31fea0037a85822eb5841ebd8e90e68a2faf75e0ec768f07d8b` | `d4e483d7a4cea7db51476ed1065cb4c20ad41f5f2d9ecbf3f8d9073706b7e9a6` (20) |
| `ptLe_not_invariant_neg` | `Classical.choice`, `Quot.sound`, `propext` | `04f4c1baee5d977d2f79fe8a09e6853dec0eb355254a9c8b06b12a6a15b4cf5d` | `de9dc5bf1d0cb86b38e53e4c0c1fbab2b529ee49803ab121d96e8e352fe02ba2` (82) |
| `quantL` | none | `cca76e884bf0eedebedb9a1426de8f7c2a1c34c57df5df45e7607e7aa154c0a0` | `298f7a73d66da2bec60a99fbc3e69916c8f0b410af8823fdfcc25e091cb224dc` (17) |
| `quantPt` | none | `bafdb2a1cf90a31fea0037a85822eb5841ebd8e90e68a2faf75e0ec768f07d8b` | `d4e483d7a4cea7db51476ed1065cb4c20ad41f5f2d9ecbf3f8d9073706b7e9a6` (20) |
| `ratInvZero` | `Classical.choice`, `Quot.sound`, `propext` | `ed32e38653ef999a005b7b7027b0ccb81fa1c5920f39d305b0cb7cb86fcdf76c` | `69d7577e1c42dc0c808c981a1d5dc1da1d22322e0e82141ceb1a4ce7081b0dc1` (6) |
| `ratJLaws` | `Classical.choice`, `Quot.sound`, `propext` | `fe1233976280bd00f32db8a06f2e7330761a9c1d8a15c5baf004ee73689d0e4e` | `176dc72af657fccefc970dc9082afd51469fe2e341466ccaca7f081c477436cb` (37) |
| `ratJ_not_invZero` | `Classical.choice`, `Quot.sound`, `propext` | `71e3b1054d09d3bb19b64029c4c2d66d2ba0320e6bd867d7a61c23d4d6b3a4d9` | `c106677cdfe73bd8dac388e095aaf7cbfccc9b22b7c75e25e3ab130951306429` (9) |
| `ratLaws` | `Classical.choice`, `Quot.sound`, `propext` | `321044bb3b8e553a0ce71e3b4cbfe8be03be65fceb9d7521fe1b6acede29b1a7` | `719c85cdda71c5733dcad6aa6b4fdf285173e593e50849fced6b333ed801558a` (34) |
| `rat_add_cube_nonpos_iff` | `Classical.choice`, `Quot.sound`, `propext` | `b934ed511783d4725db5ffaf93017c76a2cc243476a9f1becfc2af63734051a5` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ratioLe` | `Classical.choice`, `Quot.sound`, `propext` | `9377c9d6d823d650fe491b8d500d346325997a8fffb3acb165267a39031689e4` | `a8ce6583238899409d81d4653dde7347e6c112f301cbe33a1b832601512a1017` (21) |
| `ratioLe_not_affineInvariant_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `9293520665ab29b28dbb0da1245effb83d305fa1c6855d6a27e59b7117910c2f` | `0a4d092ce7e5cccd3e6691da9733a43ec36fa3abf6095b85a861e06414110ab0` (111) |
| `scaleOf` | `propext` | `a29d3ab6c8fedb1572432da21928de07d9f71e7bf5571cc620b404e0a6d3d3bb` | `ff786a1106786cbd32e866777817ada51cd26a791dd7f99d2886ccd6edbe089b` (3) |
| `scaleOf_area_ne_length` | `Classical.choice`, `Quot.sound`, `propext` | `8078e9106edaf5c66ce2ed8a9c38f1a2d34c6c5ed6a7235010a9a342f5a2dc0d` | `b331944cf154218f976557bff2237b5aa3595894db2aea921f7cb7cc82668c0a` (18) |
| `scaleOf_mm_examples` | `Classical.choice`, `Quot.sound`, `propext` | `fae007948338529aa9c0abf7ed11603d02abb7cbdde2295b8f5b468394bcaf1c` | `b331944cf154218f976557bff2237b5aa3595894db2aea921f7cb7cc82668c0a` (18) |
| `sortsPt` | none | `dddb13c354787c7d78a2a19ea6f588ecb050e841e82f870090159f0224266ffa` | `b9eb5cd205dc8332238ebba9dab70c5be247a42123b3ff5c75bb835c3f2b28fd` (4) |
| `sqOverZero` | none | `085073b6bd217e517b51ee0d6ce81f196f5483eeee72d95ad20a829ae4c57828` | `6a7904e2137053ff75e306211fd8462140d7da9210ee5a50ca409b78ced758d6` (10) |
| `sqOverZero_not_linear_ratJ` | `Classical.choice`, `Quot.sound`, `propext` | `2f21e5f0fbaf52283256acfe0e0f5a924ccea6d79e1eb493305fd433a737b595` | `47f90e36cca8713ebb1cbf79385c6ccfb1def7120d69a5f552ece34001406b87` (78) |
| `sumMixed` | `Quot.sound`, `propext` | `cca76e884bf0eedebedb9a1426de8f7c2a1c34c57df5df45e7607e7aa154c0a0` | `298f7a73d66da2bec60a99fbc3e69916c8f0b410af8823fdfcc25e091cb224dc` (17) |
| `sumMixed_engine_tight` | `Classical.choice`, `Quot.sound`, `propext` | `81c96f36d961e0557d7d5594f4de8e04d668466525b2f5601b83f54a1bc35d41` | `f4a49f2d711b92bd87d1d1efed83df2d8ab9acd601d7ee08ed1404d4cbf33393` (95) |
| `sumMixed_flips` | `Classical.choice`, `Quot.sound`, `propext` | `8cf87512ff9895ec029528a9815d8be375334409e7a2b0a12ef6af8b63329d87` | `852bf76a83396b123fdfe0f646a0291426f81b3f74caacc78d8bd58f826dd88f` (59) |
| `sumMixed_no_plainReading` | `Classical.choice`, `Quot.sound`, `propext` | `21805041d06e36c434aec0a302d5d3593a9ca43411e0fb77b3e56c2bd4a6f8a0` | `31d98b16812d413e9a232f97fe72b85a8e1380be72791d9f3ebc2aaa22c4b4af` (65) |
| `sumMixed_not_wellTyped_not_posUnitInvariant` | `Classical.choice`, `Quot.sound`, `propext` | `fcbe5f97e0a5c3fd44b07bb82df2acec280a9e7b48ceddb87aa1c8b6de4ac494` | `7cbd617ce8f43431f9379e84b60bc59bd5af5a87279a05fd1205ba881ad7ea54` (83) |
| `sumMixed_wellTyped_tight` | `Classical.choice`, `Quot.sound`, `propext` | `697d37b4fe43886e8189a022595e6878ba6f2df8fb231cb1bf458fc4e05c9d72` | `36d1a5224f5881ccc17d544647883304c232cb67de37e4ec22dc4ac921cfffb4` (108) |
| `sumTemps` | none | `bafdb2a1cf90a31fea0037a85822eb5841ebd8e90e68a2faf75e0ec768f07d8b` | `d4e483d7a4cea7db51476ed1065cb4c20ad41f5f2d9ecbf3f8d9073706b7e9a6` (20) |
| `sumTempsEnv` | `Quot.sound`, `propext` | `9fcd164d2e11b69fc399ea4325a3d4f5f1b4057170860cb006bdcc7c7425cf72` | `fdffdf532dc4412dfb5f9eaca39a4cb6b48197551575eab4042a0f52f9c08c0a` (1) |
| `sumTemps_affine_tight` | `Classical.choice`, `Quot.sound`, `propext` | `4ab0b360b164a5774b4b90473908d870f47fe7d1467730754fface6a105c9791` | `507bfab63c215bc621668fb1d8a0e13f1bb334c72ca62f81fbcccc517988b347` (108) |
| `sumTemps_celsius_kelvin` | `Classical.choice`, `Quot.sound`, `propext` | `60b98de5efe9577f54e11dae73a2668e56755d40a46afece2deea10a686af0a5` | `eda24cecbf390eee57547741885dd93c723d5dfc7a9989ac06fe60de097e0e57` (74) |
| `sumTemps_dimChecked` | none | `d210426a7474fac80c5c7ace0c24363110542c2b6b870ef2e12895f3120fe6c7` | `8b932055a4c34757a76e34cbd0f80b051789474279eb98aa49ca3d36351201d3` (43) |
| `sumTemps_dimChecked_not_pointVectorTyped_not_posAffineInvariant` | `Classical.choice`, `Quot.sound`, `propext` | `af651caa91d06cca91f8bcd006a2da3aefb55de9dadfc44dfe42cc21d42ab2c3` | `a53a85e117b6ae4ca9a98435c8f363d11530841dae43c036b91707f68589a30d` (102) |
| `sumTemps_not_pointVectorTyped` | `Classical.choice`, `Quot.sound`, `propext` | `a23eb4844bc883726b41b81a1a36503748402ea369a60c6e2cbd751866430a6e` | `befb59398a65e0ff0a56699a0343383b3af5876066ac2461c5b2a37148e4c38b` (55) |
| `twoVarSum` | none | `09187b89bb8b96ce2e3819c7e47c0eec2dcc87376b6dd7460f477616c5d07b60` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `twoVarSum_not_linear` | `Classical.choice`, `Quot.sound`, `propext` | `9cbbd1970f6c398665071a3c938908877bf1c481594ca9359c5e47a6ec54cf31` | `053d5bc8744789a046bcc2dcff0a1a243ad5f4583de21fd04f0a820ad905a217` (75) |
| `unitChangeStep` | `propext` | `df1ec873c14b8a9e42b8e21f2283bdbcfbfc1ec77d3cfc2de0b4cf24928a9d48` | `a0763f14f45dda974f7ef7da1bb8014345689729bf05a29609efc6cb8531cc27` (9) |
| `unitChangeStep_example` | `Classical.choice`, `Quot.sound`, `propext` | `03dab81169ab166cc74459ef729ed046814c489f103c0f7ce11d96274d421dd7` | `dbad9b3dbee97a8494151a146e78239e1b71d9bbdb7c61f7ddfbe162100deecb` (27) |
| `unitChangeStep_readings_unchanged_not` | `Classical.choice`, `Quot.sound`, `propext` | `f5bafa5f3ccf5b4bbd94f5d21596e35de078cc95396f0096f69c7229d0c942d4` | `aadaed08113da46c58ee61bd1d066005c2bbf64b39edc24065a99b2801cb49fa` (26) |
| `unitDim` | `propext` | `96986f5063ae62d0f7f2a19c71e17552dd7c846838f97b9f857d1d3e8a90e570` | `6bb1fa3d0c12d93e3bfbdb4dda2d8c1369da504c2a91f5f49aa770cbc1ddaa87` (1) |
| `unitInvariant_of_wellTyped` | `Classical.choice`, `Quot.sound`, `propext` | `3ed1bc5fe99e94d3c7d9a4b943e793f562abd059b3a549f13941ab8c8df13ea6` | `cc7724a2d2dae2d2cbd20d4709806e2bcb083e54364507b05c4746f80b2099c7` (103) |
| `unitLe` | `Quot.sound`, `propext` | `cca76e884bf0eedebedb9a1426de8f7c2a1c34c57df5df45e7607e7aa154c0a0` | `298f7a73d66da2bec60a99fbc3e69916c8f0b410af8823fdfcc25e091cb224dc` (17) |
| `unitLe_wellTyped` | `Quot.sound`, `propext` | `c5b20a1be813d4363c9fb73aa3f863e2f6621eb69358dc4fc45162b87de2f301` | `ac31f94a42bc3c434a20e356595a320f8eb791250be334ec46203b1d4f4739ac` (42) |
| `upd` | none | `4a73c1519862d0077fbb8513a9e58bc27f8b9d7c885ae6ce72eed5383901b6eb` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `var_wrongDim_not_homogeneous` | `Classical.choice`, `Quot.sound`, `propext` | `6371d2b541ba9506e8f8e7bc550ba691d6cd8a3555265a832dd4f033571070e8` | `cbc18825f6d293e8dfbca1d01dec7adc795162e9e8685aa76ae353c58244a461` (68) |
| `weightsSumOne_examples` | `Classical.choice`, `Quot.sound`, `propext` | `c4062307d54a281b8f5d1979cb1a1e0d5bf92e4bcae2c4d8df8c99850fc6e1d5` | `0718cd143b4c4c16e369c036ebfba845e5648fbc7825dbc895cb5cb8f4c61f13` (6) |
| `xTimesInvX` | `Quot.sound`, `propext` | `09187b89bb8b96ce2e3819c7e47c0eec2dcc87376b6dd7460f477616c5d07b60` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `xTimesInvX_not_homogeneous_zero` | `Classical.choice`, `Quot.sound`, `propext` | `8e71cfa2bf5cad10937299e72708e259060de580afd2d0fb9f9d60978890f47d` | `72d7ff87db9b25eb4ad91b14b6a5e84e90c39ef42ac34c1146462b4bf73a9360` (68) |
| `xTimesInvX_not_polynomial` | `Quot.sound`, `propext` | `c3968bf1422ade0251d54c7c5006c91a481337101215650058ffd88545e0dcd0` | `d887ea3583080eddadcb83cbddd85d9cd5f435308e806e5f9bd89e7b43781ade` (19) |
| `xVar` | none | `09187b89bb8b96ce2e3819c7e47c0eec2dcc87376b6dd7460f477616c5d07b60` | `59c2249bd21631a72a3eb8890d8c5e422d97e7cc6c4d6ada4d21028b5fd3ef9b` (9) |
| `zpow` | none | `978776b725c6b52ad375af1d90310c1bb8dc711579cd8ad6910f5c5710cac8c7` | `298781db8b8bc6b19e53d7e5b10eb1a34bf80422c5616c037bf72f17673ffc42` (2) |

### Primary sources

Each record states what was verified and how. "Search index" means that bibliographic data (and, where stated, a content summary) were checked through a web search index without retrieving the full text; such a source is cited for the statement attributed to it and for nothing more. Verbatim quotations from pinned files give the file, the commit and the full line range of the quoted text. The repositories, tags and commits of Pint 0.26.2 and mp-units v2.5.0 were resolved through the GitHub API (both are annotated tags whose target commits are the ones given).

- **Stevens 1946.** S. S. Stevens, "On the Theory of Scales of Measurement", Science 103(2684):677-680, 1946, DOI 10.1126/science.103.2684.677 (bibliographic data and a content summary verified through a search index; full text not retrieved): scales classified by their admissible transformations; interval scales (for example temperature in °C or °F) admit x -> a x + b, ratio scales (length, mass, kelvin temperature) admit x -> a x.
- **Suppes–Zinnes 1963.** P. Suppes, J. L. Zinnes, "Basic Measurement Theory", in R. D. Luce, R. R. Bush, E. Galanter (eds.), Handbook of Mathematical Psychology, Vol. 1, Wiley, 1963, pp. 1-76 (bibliographic data and a content summary verified through a search index; full text not retrieved): a numerical statement is meaningful if its truth value is invariant under the admissible transformations of the scales involved.
- **Roberts 1979.** F. S. Roberts, Measurement Theory with Applications to Decisionmaking, Utility, and the Social Sciences, Addison-Wesley, 1979 (bibliographic data and a content summary verified through a search index; full text not retrieved): meaningfulness as invariance of truth value under admissible transformations, with similarity transformations x -> a x (a > 0) for ratio scales and positive linear transformations x -> a x + b (a > 0) for interval scales.
- **Krantz–Luce–Suppes–Tversky 1971/1990.** D. H. Krantz, R. D. Luce, P. Suppes, A. Tversky, Foundations of Measurement, Vol. I: Additive and Polynomial Representations (1971) and Vol. III: Representation, Axiomatization, and Invariance (1990), Academic Press (bibliographic data verified through a search index; full text not retrieved; Vol. III treats invariance and meaningfulness).
- **Luce 1959.** R. D. Luce, "On the Possible Psychophysical Laws", Psychological Review 66(2):81-95, 1959, DOI 10.1037/h0043178 (bibliographic data and a content summary verified through a search index; full text not retrieved): if the independent and dependent variables are ratio scales and the law is invariant under their admissible transformations, the law is a power function. The one-variable results of this package are the exponent-1 case for length-to-length maps expressible in the toy syntax.
- **Buckingham 1914.** E. Buckingham, "On Physically Similar Systems; Illustrations of the Use of Dimensional Equations", Physical Review 4(4):345-376, 1914, DOI 10.1103/PhysRev.4.345 (bibliographic data verified through a search index; cited for context, full text not retrieved).
- **Kennedy 1997.** A. J. Kennedy, "Relational Parametricity and Units of Measure", POPL 1997, pp. 442-455, DOI 10.1145/263699.263761 (bibliographic data verified through a search index; full text not retrieved). Its content as relevant here is taken from the description in Atkey-Johann-Kennedy 2013 (paper source read, see that entry; paper/popl049-atkey.tex lines 1149-1160 and 1200-1210 at the pinned commit): Kennedy interprets units-of-measure types by invariance under strictly positive scaling factors, and shows that no term of type forall s. real<s^2> -> real<s> other than a constantly-zero one is definable (no square root).
- **Kennedy 2010.** A. Kennedy, "Types for Units-of-Measure: Theory and Practice", Central European Functional Programming School (CEFP 2009), Revised Selected Lectures, LNCS 6299, Springer, 2010, pp. 268-305, DOI 10.1007/978-3-642-17685-2_8 (bibliographic data verified through a search index; full text not retrieved; cited as background).
- **Atkey–Johann–Kennedy 2013.** R. Atkey, P. Johann, A. Kennedy, "Abstraction and Invariance for Algebraically Indexed Types", POPL 2013, pp. 87-100, DOI 10.1145/2480359.2429082 (DOI confirmed on the first author's paper page). Paper source read at github.com/bobatkey/algebraically-indexed-types commit d882ca31c8a08ecee6c0dfcfe883c1770d9b5da3, file paper/popl049-atkey.tex (3374 lines; LaTeX transcribed into ASCII below): in Section 'Affine and Vector Operations' (from line 777), affComb : forall t:T(2). vec<t> -> real -> vec<t> -> vec<t> with [[affComb]] v1 r v2 = (1-r)v1 + r v2 (lines 790-794), whose index-erasure interpretation 'is invariant under all changes of origin' (line 798); the figure 'Operations on vectors' (lines 1223-1255) generalizes this to affComb : forall B:GL(2), t:T(2). vec<B,t> -> real<1> -> vec<B,t> -> vec<B,t> (lines 1240-1244). Section 'Scale Invariance and Dimensional Analysis' (from line 1146) states 'Semantically, our type indexes by non-zero scaling factors, whereas Kennedy's indexes by strictly positive ones' (lines 1157-1160, omitting the LaTeX comment line 1158); the figure 'Operations on scaled real numbers' (lines 1046-1064) types division as forall s1,s2:GL1. real<s1> -> real<s2> -> real<s1 s2^-1> + unit, a partial operation (lines 1054-1058), and gives abs the type forall s:GL1. real<s> -> real<|s|> (line 1059). The framework is a higher-order polymorphic lambda calculus; the authors state that the framework and most examples are formalised in Coq (line 477); the cited figures have no order atoms. The introduction observes that the type of areaCircle is isomorphic to real<1>, because the only unary functions whose outputs scale as the square of the scaling of their inputs are those of the form lambda x. k x^2 (lines 304-312); the paragraph 'Scalings' derives this from the isomorphism (eqn:scaleiso) forall s:GL1. real<s> -> A ≅ A[1/s] × forall s:GL1. A (lines 2440-2460). The one-variable results of this package restate the first-order, exponent-1 analogue in the toy syntax.
- **Allen 2026.** E. Allen, "A Calculus for Units of Measure with Conversion", arXiv:2609.38242 [cs.PL], submitted 29 September 2026 (abstract read on arXiv): a typed lambda calculus with unit conversion and quantification over units and dimensions; for terms without unit constants, a convert-free term is invariant under every rescaling, and a term with conversions is invariant under every rescaling that scales all units of one dimension by the same factor; the abstract states that every theorem is mechanized in Lean 4. Mechanized prior art for 'typed implies invariant' in a richer, higher-order setting that also tracks units of one dimension separately.
- **Bobbin–Jones–Velkey–Josephson 2025.** M. P. Bobbin, C. Jones, J. Velkey, T. R. Josephson, "Formalizing dimensional analysis using the Lean theorem prover", arXiv:2509.13142 [physics.chem-ph], submitted 16 September 2025 (abstract read on arXiv): Lean 4 formalization of dimensions as maps from base dimensions to exponents (an Abelian group), dimensional homogeneity theorems, SI base units and the Buckingham Pi theorem.
- **Foster–Wolff 2023.** S. Foster, B. Wolff, "Automated Reasoning for Physical Quantities, Units, and Measurements in Isabelle/HOL", arXiv:2302.07629 [cs.LO], submitted 15 February 2023 (abstract read on arXiv): a mechanisation of the International System of Quantities and the SI unit system in Isabelle/HOL, with quantities parameterised by dimension types.
- **Botta–Jansson 2023/2026.** N. Botta, P. Jansson, "Types, equations, dimensions and the Pi theorem", arXiv:2308.09481 [cs.PL], v6 of 22 June 2026 (abstract read on arXiv): an Idris domain-specific language formalizing dimension functions, physical quantities, homomorphic measurement, the covariance principle and Buckingham's Pi theorem.
- **Baez 2009.** J. Baez, "Torsors Made Easy", 27 December 2009, https://math.ucr.edu/home/baez/torsors.html (page read): energies, positions and similar quantities whose zero is conventional form a torsor of a group of differences. The affine toy is richer than a torsor of translations: it also has positive scaling, ratios of differences and order (an ordered one-dimensional affine space).
- **Buzzard 2020.** K. Buzzard, "Division by zero in type theory: a FAQ", Xena Project blog, 5 July 2020, https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/ (page read): Lean (as well as Coq and Isabelle) defines 1/0 = 0; the symbol / there denotes a total function that agrees with mathematical division away from 0.
- **Pint 0.26.2 documentation.** Pint 0.26.2 (github.com/hgrecco/pint tag 0.26.2, commit af817a6094fbc40005fadd7bcc59b138dbff233e), docs/user/nonmult.rst (198 lines; read at that commit): 'the temperature units fahrenheits and celsius are non-multiplicative units' (lines 7-8); 'Subtraction of two temperatures given in offset units yields a *delta* unit' (line 51); 'In contrast to subtraction, the addition of quantities with offset units is ambiguous, e.g. for *10 degC + 100 degC* two different result are reasonable depending on the context, *110 degC* or *383.15 °C (= 283.15 K + 373.15 K)*. Because of this ambiguity pint raises an error for the addition of two quantities with offset units (since pint-0.6).' (lines 93-97). With the registry parameter autoconvert_offset_to_baseunit set to true (lines 124-126): 'Before all other multiplications, all divisions and in case of exponentiation [#f1]_ involving quantities with offset-units, pint will convert the quantities with offset units automatically to the corresponding base unit before performing the operation.' (lines 138-141), where footnote f1 reads 'If the exponent is +1, the quantity will not be converted to base unit but remains unchanged.' (lines 197-198).
- **mp-units v2.5.0 documentation.** mp-units v2.5.0 (github.com/mpusz/mp-units tag v2.5.0, commit 27d2def9082ce00d7eb4f75695dbead4a748f23f), read at that commit: docs/users_guide/framework_basics/the_affine_space.md introduces 'the primary operations one can do in the affine space' (line 22) and lists 'vector + vector -> vector', 'vector - vector -> vector', '-vector -> vector', 'vector * scalar -> vector', 'scalar * vector -> vector', 'vector / scalar -> vector', 'point - point -> vector', 'point + vector -> point', 'vector + point -> point', 'point - vector -> point' (lines 24-33; Markdown emphasis omitted), then 'It is not possible to: add two points, subtract a point from a vector, multiply nor divide points with anything else.' (lines 37-41; list markup and emphasis omitted). src/core/include/mp-units/math.h documents lerp for two quantity points (doc comment lines 464-470, including 'Linear interpolation or extrapolation' (line 465) and 'the result of `a + t(b − a)`' (line 468); quantity_point parameters at lines 476-477) and midpoint ('Computes the midpoint of two points', line 488; quantity_point parameters at lines 495-496).

### Observation dates

All evidence in this report was acquired or re-verified on 2026-11-21: the Lean build and axiom and hash audit; the toolchain, Pint and mp-units tag resolutions; the pinned documentation files and paper source, read at the commits given; and the arXiv abstract pages and web pages cited as read.

## Revalidation

Requirements: `elan`, which installs the toolchain pinned in `lean/lean-toolchain` (`leanprover/lean4:v4.34.1`) on first use, and `python3`. No other dependency is fetched: the Lake project has no `[[require]]`.

**Primary check.** From the package directory, run:

```bash
python3 support/revalidate.py .
```

The script never modifies the package: it copies `lean/` to a temporary directory and there (1) runs `lake build`; (2) scans every Lean source for `sorry`, `admit`, `native_decide` and `axiom` declarations; (3) builds a generated audit program that runs `Lean.collectAxioms` on every declaration of the `ToyUnits` library and fails if any depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`; and (4) for every Lean name referenced by `results.json` and every name recorded in `audit/statements.json`, recomputes the statement hash and the closure hash exactly as described under Evidence, "Kernel-check record", and compares them with `audit/statements.json`. It prints one line per check and ends with `REVALIDATED` when all pass (exit status 0).

**Manual axiom check of the sixteen result theorems.** From the package directory:

```bash
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` is outside the library target. It imports `ToyUnits` and runs `#print axioms` on each result theorem; each reported axiom list should be a subset of `propext`, `Classical.choice`, `Quot.sound`.

**What a pass establishes.** A pass shows that, under the pinned toolchain, every recorded statement and definition closure is unchanged and kernel-checked with the standard axioms. It does not re-check the prose of this report, the modeling-bridge remarks, or the citations. Hashes are computed from Lean's `repr` output, so under a different toolchain they may change without any change in meaning; in that case compare the verbatim statements quoted in Findings with the sources instead.

**Revalidating the modeling bridge.** Re-read the pinned line ranges given under Findings, "Modeling bridge to real systems", and Evidence, "Primary sources": `docs/user/nonmult.rst` lines 7-8, 51, 58-59, 93-97, 124-129, 138-141 and 197-198 at Pint commit `af817a6094fbc40005fadd7bcc59b138dbff233e`; `docs/users_guide/framework_basics/the_affine_space.md` lines 22-41 and `src/core/include/mp-units/math.h` lines 464-498 at mp-units commit `27d2def9082ce00d7eb4f75695dbead4a748f23f`. For a newer release of either library, read the same documentation at that release; the theorems of this package are unaffected by library changes, and the remarks may need revision.
