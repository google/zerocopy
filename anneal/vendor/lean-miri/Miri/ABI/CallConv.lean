import Miri.ABI.Layout

/-! Source-shaped `rustc_target::callconv` argument records and ABI equality.
Equality deliberately ignores attributes that are not calling-convention bits,
as the pinned source does. This does not classify a target's calling convention. -/
namespace Miri.ABI

inductive ArgExtension where
  | None | Zext | Sext
  deriving DecidableEq, Repr
structure ArgAttributes where
  regular : UInt16
  argExt : ArgExtension
  pointeeSize : Size
  pointeeAlign : Option Align
  deriving DecidableEq, Repr
namespace ArgAttributes

def new : ArgAttributes := ⟨0,.None,Size.ZERO,none⟩
def contains (attrs : ArgAttributes) (mask : UInt16) : Bool := attrs.regular &&& mask == mask
def eqAbi (left right : ArgAttributes) : Bool :=
  left.contains 64 == right.contains 64 && left.argExt == right.argExt
end ArgAttributes

structure Uniform where
  unit : Reg
  total : Size
  isConsecutive : Bool
  deriving DecidableEq, Repr
structure CastTarget where
  «prefix» : Array Reg
  restOffset : Option Size
  rest : Uniform
  attrs : ArgAttributes
  deriving DecidableEq, Repr
namespace CastTarget

def eqAbi (left right : CastTarget) : Bool :=
  left.prefix == right.prefix && left.restOffset == right.restOffset &&
  left.rest == right.rest && left.attrs.eqAbi right.attrs
end CastTarget

inductive IndirectMode where
  | Pointer | OnStack | AmdgpuKernelArg
  deriving DecidableEq, Repr
inductive PassMode where
  | Ignore
  | Direct (attrs : ArgAttributes)
  | Pair (first second : ArgAttributes)
  | Cast (padI32Count : UInt8) (cast : CastTarget)
  | Indirect (attrs : ArgAttributes) (addressSpace : Option AddressSpace) (mode : IndirectMode)
  | IndirectUnsized (attrs metaAttrs : ArgAttributes)
  deriving DecidableEq, Repr
namespace PassMode

def eqAbi : PassMode → PassMode → Bool
  | .Ignore,.Ignore => true
  | .Direct a,.Direct b => a.eqAbi b
  | .Pair a b,.Pair c d => a.eqAbi c && b.eqAbi d
  | .Cast pad a,.Cast pad' b => a.eqAbi b && pad == pad'
  | .Indirect a space mode,.Indirect b space' mode' => a.eqAbi b && space == space' && mode == mode'
  | .IndirectUnsized a metadata,.IndirectUnsized b metadata' => a.eqAbi b && metadata.eqAbi metadata'
  | _,_ => false

def isIgnore : PassMode → Bool | .Ignore => true | _ => false
def isDirect : PassMode → Bool | .Direct _ => true | _ => false
def isUnsizedIndirect : PassMode → Bool | .IndirectUnsized .. => true | _ => false
end PassMode

structure ArgAbi (Ty : Type) where
  layout : TyAndLayout Ty
  mode : PassMode
  deriving DecidableEq, Repr
namespace ArgAbi

def eqAbi [DecidableEq Ty] (left right : ArgAbi Ty) : Bool :=
  left.layout.layout.eqAbi right.layout.layout && left.mode.eqAbi right.mode &&
  (if left.mode.isDirect then
    match left.layout.layout.backendRepr with
    | .Memory => left.layout.ty == right.layout.ty
    | _ => true
   else true)

def isIgnore (arg : ArgAbi Ty) : Bool := arg.mode.isIgnore
def isUnsizedIndirect (arg : ArgAbi Ty) : Bool := arg.mode.isUnsizedIndirect
end ArgAbi
end Miri.ABI
