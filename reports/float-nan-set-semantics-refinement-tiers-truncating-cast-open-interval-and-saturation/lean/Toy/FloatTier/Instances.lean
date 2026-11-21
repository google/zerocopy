/-
Toy.FloatTier.Instances
=======================

Concrete small formats and literals used by examples, counterexamples and
non-vacuity witnesses.
-/
import Toy.FloatTier.CastStatements

namespace Toy.FloatTier

variable {f : Fmt}

/-- Format with exponent field width 3 and precision 3 (`qneg = 4`: one unit is
`1/16`; largest finite value `14`). -/
def F33 : Fmt := ⟨3, 3, by decide, by decide⟩
/-- Format with exponent field width 3 and precision 2 (`qneg = 3`; largest
finite value `12`). -/
def F32 : Fmt := ⟨3, 2, by decide, by decide⟩
/-- Format with exponent field width 2 and precision 3 (`qneg = 2`; largest
finite value `3.5`; two NaN payloads). -/
def F23 : Fmt := ⟨2, 3, by decide, by decide⟩

/-- `1.0` as a payload-carrying value (biased exponent `bias`, trailing
significand `0`). -/
def V.one (f : Fmt) : V f := .fin false ⟨f.bias, f.bias_lt_expCount⟩ ⟨0, f.fracCount_pos⟩

/-- A finite value of `FP f` given by its fields (helper for literals). -/
def FP.mk' (f : Fmt) (s : Bool) (E M : Nat) (hE : E < f.expCount := by decide)
    (hM : M < f.fracCount := by decide) : FP f := .fin s ⟨E, hE⟩ ⟨M, hM⟩

/-- `3.5` in `F33` (56 units). -/
def f33_3p5 : FP F33 := FP.mk' F33 false 4 3
/-- `-3.5` in `F33`. -/
def f33_m3p5 : FP F33 := FP.mk' F33 true 4 3
/-- `-0.5` in `F33` (8 units). -/
def f33_m0p5 : FP F33 := FP.mk' F33 true 2 0
/-- `4.0` in `F33` (64 units). -/
def f33_4 : FP F33 := FP.mk' F33 false 5 0
/-- `5.0` in `F33` (80 units). -/
def f33_5 : FP F33 := FP.mk' F33 false 5 1

/-- The program `toBits (0.0 * +∞)` is `progBitsZeroMulInf`; this is
`isNaN (0.0 * +∞)`. -/
def progIsNaNZeroMulInf (f : Fmt) : Prog f :=
  .isNaN (.prim .mul (.lit (V.zero f false)) (.lit (.inf false)))

/-- `toBits (copysign (var 0) (+∞ * -∞))` (no NaN is produced: `+∞ * -∞ = -∞`). -/
def progBitsCopysignVarInfMulNegInf (f : Fmt) : Prog f :=
  .toBits (.copysign (.var 0) (.prim .mul (.lit (.inf false)) (.lit (.inf true))))

/-- `0.0 < copysign(1.0, 0.0 * +∞)`: a value-level observation of a `copysign`
whose sign argument is a NaN. -/
def progCopysignNaN (f : Fmt) : Prog f :=
  .lt (.lit (V.zero f false))
    (.copysign (.lit (V.one f)) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))

/-- `signBit (min(+0.0, -0.0))`. -/
def progMinZeroSign (f : Fmt) : Prog f :=
  .signBit (.prim .min (.lit (V.zero f false)) (.lit (V.zero f true)))

/-- `min(+0.0, -0.0) == +0.0`. -/
def progMinZeroEq (f : Fmt) : Prog f :=
  .eq (.prim .min (.lit (V.zero f false)) (.lit (V.zero f true))) (.lit (V.zero f false))

/-- `signBit (if 0.0 * +∞ < 0.0 then 1.0 else +∞ * -∞)`: a NaN is produced and
compared, and the bit-level observation receives `-∞`. -/
def progNaNBranchSign (f : Fmt) : Prog f :=
  .signBit (.selLt (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))) (.lit (V.zero f false))
    (.lit (V.one f)) (.prim .mul (.lit (.inf false)) (.lit (.inf true))))

/-- `0.0 < (if 0.0 * +∞ < 0.0 then copysign(1.0, 0.0 * +∞) else 1.0)`: the
`then`-branch contains a `copysign` whose sign argument is a NaN, but no
`S`-execution takes that branch (a comparison with a NaN is false). -/
def progGuardedDeadCopysign (f : Fmt) : Prog f :=
  .lt (.lit (V.zero f false))
    (.selLt (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))) (.lit (V.zero f false))
      (.copysign (.lit (V.one f)) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))
      (.lit (V.one f)))

/-- `0.0 < (if 0.0 < var 0 then copysign(1.0, var 0) else 1.0)`: a `copysign`
on the input, guarded by a comparison that is false for NaN and zero inputs. -/
def progGuardedInputCopysign (f : Fmt) : Prog f :=
  .lt (.lit (V.zero f false))
    (.selLt (.lit (V.zero f false)) (.var 0)
      (.copysign (.lit (V.one f)) (.var 0))
      (.lit (V.one f)))

/-- `signBit (abs (0.0 * +∞))`: a bit-level observation of a NaN whose sign bit
has been cleared. -/
def progSignBitAbsNaN (f : Fmt) : Prog f :=
  .signBit (.abs (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))

/-- `toBits (lit (negative preferred quiet NaN))`: a bit-level observation of a
NaN literal (a NaN built from bits). -/
def progBitsNaNLit (f : Fmt) : Prog f :=
  .toBits (.lit (V.prefNaN f true))

/-- `isNaN (lit (negative preferred quiet NaN) + 1.0)`: a NaN literal used by
arithmetic and observed at the value level. -/
def progIsNaNLitAdd (f : Fmt) : Prog f :=
  .isNaN (.prim .add (.lit (V.prefNaN f true)) (.lit (V.one f)))

/-- `copysign(1.0, 0.0 * +∞) == copysign(1.0, 0.0 * +∞)`: two syntactic
occurrences of the same NaN-producing expression. -/
def progSelfEqCopysignNaN (f : Fmt) : Prog f :=
  .eq (.copysign (.lit (V.one f)) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))
    (.copysign (.lit (V.one f)) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))

/-- A tier that always returns `+∞` (unsound). -/
def tierBad : Tier f := fun _ _ _ => .inf false

/-- A tier for `F23` that behaves like `tierCtfe`, except that every NaN result
carries the quiet bit and payload `1` (an extra payload). -/
def tierExtraPay1 : Tier F23 := fun p x y =>
  if (tierCtfe p x y).isNaN then V.qnan (tierCtfe p x y).signBit ⟨1, by decide⟩
  else tierCtfe p x y

/-- The extra-payload set of `F23` that allows exactly payload `1`. -/
def extraPay1 : Extra F23 := fun _ _ k => k == 1

end Toy.FloatTier
