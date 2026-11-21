/-
Toy.Float.Rewrites
==================

The rewrites of the flag table, each as a `Rewrite f n` over `n` variables
(`.var 0`, `.var 1`, `.var 2` play the roles of `x`, `y`, `z`), and named
flag sets.
-/
import Toy.Float.Instances

namespace Toy.Float

/-! ### Named flag sets -/

/-- `{nnan}` -/
def fNnan : Flags := { nnan := true }
/-- `{nsz}` -/
def fNsz : Flags := { nsz := true }
/-- `{nnan, nsz}` -/
def fNnanNsz : Flags := { nnan := true, nsz := true }
/-- `{nnan, ninf, nsz}` -/
def fNnanNinfNsz : Flags := { nnan := true, ninf := true, nsz := true }
/-- `{reassoc}` -/
def fReassoc : Flags := { reassoc := true }
/-- `{contract}` -/
def fContract : Flags := { contract := true }

/-! ### Rewrites -/

/-- `x + (-0.0) → x` -/
def rwAddNegZero (f : Fmt) : Rewrite f 1 := ⟨.add (.var 0) (.lit (negZero f)), .var 0⟩
/-- `x + (+0.0) → x` -/
def rwAddPosZero (f : Fmt) : Rewrite f 1 := ⟨.add (.var 0) (.lit (posZero f)), .var 0⟩
/-- `x * 1.0 → x` -/
def rwMulOne (f : Fmt) : Rewrite f 1 := ⟨.mul (.var 0) (.lit (one f)), .var 0⟩
/-- `x * (-1.0) → -x` -/
def rwMulNegOne (f : Fmt) : Rewrite f 1 := ⟨.mul (.var 0) (.lit (one f).neg), .neg (.var 0)⟩
/-- `x * 2.0 → x + x` -/
def rwMulTwo (f : Fmt) : Rewrite f 1 :=
  ⟨.mul (.var 0) (.lit (ofDyadic f false 1 1)), .add (.var 0) (.var 0)⟩
/-- `x - x → +0.0` -/
def rwSubSelf (f : Fmt) : Rewrite f 1 := ⟨.sub (.var 0) (.var 0), .lit (posZero f)⟩
/-- `x * (+0.0) → +0.0` -/
def rwMulPosZero (f : Fmt) : Rewrite f 1 := ⟨.mul (.var 0) (.lit (posZero f)), .lit (posZero f)⟩
/-- `(+0.0) - x → -x` -/
def rwPosZeroSub (f : Fmt) : Rewrite f 1 := ⟨.sub (.lit (posZero f)) (.var 0), .neg (.var 0)⟩
/-- `(-0.0) - x → -x` -/
def rwNegZeroSub (f : Fmt) : Rewrite f 1 := ⟨.sub (.lit (negZero f)) (.var 0), .neg (.var 0)⟩
/-- `-(x - y) → y - x` -/
def rwNegSub (f : Fmt) : Rewrite f 2 := ⟨.neg (.sub (.var 0) (.var 1)), .sub (.var 1) (.var 0)⟩
/-- `x + y → y + x` -/
def rwAddComm (f : Fmt) : Rewrite f 2 := ⟨.add (.var 0) (.var 1), .add (.var 1) (.var 0)⟩
/-- `(x + y) + z → x + (y + z)` -/
def rwAddAssoc (f : Fmt) : Rewrite f 3 :=
  ⟨.add (.add (.var 0) (.var 1)) (.var 2), .add (.var 0) (.add (.var 1) (.var 2))⟩
/-- `(x * y) * z → x * (y * z)` -/
def rwMulAssoc (f : Fmt) : Rewrite f 3 :=
  ⟨.mul (.mul (.var 0) (.var 1)) (.var 2), .mul (.var 0) (.mul (.var 1) (.var 2))⟩
/-- `x * y + z → fma x y z` (contraction) -/
def rwContract (f : Fmt) : Rewrite f 3 :=
  ⟨.add (.mul (.var 0) (.var 1)) (.var 2), .fma (.var 0) (.var 1) (.var 2)⟩
/-- `fma x y z → x * y + z` (splitting a fused operation) -/
def rwUncontract (f : Fmt) : Rewrite f 3 :=
  ⟨.fma (.var 0) (.var 1) (.var 2), .add (.mul (.var 0) (.var 1)) (.var 2)⟩

/-- The expression `x*y - x*y`, the classic contraction hazard. -/
def eMulSubMul (f : Fmt) : Expr f 2 := .sub (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))

/-- Environments from one, two or three values. -/
def env1 {f : Fmt} (a : FP f) : Fin 1 → FP f := fun _ => a
def env2 {f : Fmt} (a b : FP f) : Fin 2 → FP f := fun i => if i.val = 0 then a else b
def env3 {f : Fmt} (a b c : FP f) : Fin 3 → FP f :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else c

/-! ### Vocabulary used by the statements -/

section
variable {f : Fmt}

/-- The witness `a = 2^(emin + p)` (with `emin = 1 - bias`). -/
def assocRoundA (f : Fmt) : FP f := ofDyadic f false 1 ((1 : Int) - f.bias + f.p)
/-- The witness `b = 2^emin`, the smallest positive normal number. -/
def assocRoundB (f : Fmt) : FP f := ofDyadic f false 1 ((1 : Int) - f.bias)

/-- The forms of `e` permitted by `S` all agree with `e` on every input, i.e.
using the permissions in `S` is a refinement of the flag-free semantics. -/
def PermittedFormsAgree {n : Nat} (S : Flags) (e : Expr f n) : Prop :=
  ∀ env, ∀ v ∈ e.variants S, v.eval env = e.eval env

/-- Exactly one operand is NaN, or the operands are `+0` and `-0` in some
order. -/
def OneNaNOrOppositeZeros (a b : FP f) : Prop :=
  a.isNaN ≠ b.isNaN ∨ (a.isZero = true ∧ b.isZero = true ∧ a ≠ b)

/-- The forms of `e` permitted by `S` all agree with `e` at the input `env`. -/
def PermittedFormsAgreeAt {n : Nat} (S : Flags) (e : Expr f n) (env : Fin n → FP f) : Prop :=
  ∀ v ∈ e.variants S, v.eval env = e.eval env

instance {n : Nat} (S : Flags) (e : Expr f n) (env : Fin n → FP f) :
    Decidable (PermittedFormsAgreeAt S e env) := by
  unfold PermittedFormsAgreeAt; infer_instance

instance (a b : FP f) : Decidable (OneNaNOrOppositeZeros a b) := by
  unfold OneNaNOrOppositeZeros; infer_instance

instance {n : Nat} (S : Flags) (e : Expr f n) : Decidable (PermittedFormsAgree S e) := by
  unfold PermittedFormsAgree; infer_instance

end

end Toy.Float
