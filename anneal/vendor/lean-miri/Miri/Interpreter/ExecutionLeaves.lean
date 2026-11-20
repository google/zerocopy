import Miri.Interpreter.Rvalue
import Miri.Interpreter.Discriminant

/-! Genuine surviving execution inputs. Operational callbacks replaced by
canonical assembly are deliberately absent, rather than accepted and ignored. -/
namespace Miri.Interpreter.ExecutionLeaves
open Miri.Memory
structure Rvalue (S C : Type) where
  threadLocalPointer : C → MIR.DefId → RvalueM S (Pointer (Option Provenance))
  normalize : C → MIR.TyId → RvalueM S MIR.TyId
structure Discriminant (S C : Type) where
  discriminantLayout : C → MIR.TyId → RvalueM S LocalLayout
  tagLayout : C → ABI.Scalar → RvalueM S LocalLayout
  discriminantValue : C → MIR.TyId → Nat → RvalueM S (Option (MIR.TyId × ABI.U128))
  variantForDiscriminant : C → MIR.TyId → ABI.U128 → RvalueM S (Option Nat)
  adtVariantCount : C → MIR.TyId → RvalueM S Nat
  scalarMayBeNull : C → Scalar Provenance → RvalueM S Bool

def Discriminant.ofHooks (h : DiscriminantHooks Provenance S C V) : Discriminant S C :=
  ⟨h.discriminantLayout,h.tagLayout,h.discriminantValue,h.variantForDiscriminant,h.adtVariantCount,h.scalarMayBeNull⟩
structure Operand (S C : Type) where
  checkPlaceType : C → MIR.Place → OpTy Provenance → RvalueM S Unit
  dereference : C → OpTy Provenance → RvalueM S (MPlaceTy Provenance)
  runtimeChecks : C → MIR.RuntimeChecks → RvalueM S Bool
  boolLayout : C → RvalueM S LocalLayout
  constantAt : C → OperandPath → MIR.ConstOperand → Option LocalLayout → RvalueM S (OpTy Provenance)
structure Control (P L E : Type) where
  bodySpan : Frame P L E → Except StepError MIR.SpanRef
end Miri.Interpreter.ExecutionLeaves
