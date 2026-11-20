import Miri.Interpreter.Native.Types

/-! Native mod.rs:367–435/444–490 direct ABI and closure preparation. Compiler
queries are separated from memory operations; building a host trampoline never
requires fabricated NativeHooks read/write callbacks. -/
namespace Miri.Interpreter.NativeAbi
open Miri.ABI Miri.Memory Miri.MIR
structure Queries (S C : Type) where
  typeShape : C → LocalLayout → RvalueM S Native.TypeShape
  layoutOf : C → TyId → RvalueM S (Except Unit LocalLayout)
private def queryLayout (q : Queries S C) (choice : C) (ty : TyId) : RvalueM S LocalLayout := do
  match ← q.layoutOf choice ty with
  | .ok value => pure value
  | .error () => throw (.unsupported "compiler layout unavailable for native FFI type")

def ffiType (q : Queries S C) (choice : C) : Nat → LocalLayout → RvalueM S Native.FfiType
  | 0,_ => throw (.resourceExhaustion "native FFI recursive compiler query budget exhausted")
  | fuel+1,layout => do
    match layout.layout.backendRepr with
    | .Scalar scalar =>
      if let .adt isEnum _ reprC _ ← q.typeShape choice layout then
        if !isEnum && reprC then throw (.invalidProgram "repr(C) non-enum has scalar backend ABI")
      match scalar.primitive with
      | .Int .I8 true => pure .i8 | .Int .I16 true => pure .i16
      | .Int .I32 true => pure .i32 | .Int .I64 true => pure .i64
      | .Int .I8 false => pure .u8 | .Int .I16 false => pure .u16
      | .Int .I32 false => pure .u32 | .Int .I64 false => pure .u64
      | .Float .F32 => pure .f32 | .Float .F64 => pure .f64
      | .Pointer space =>
        if space == AddressSpace.ZERO then pure .pointer
        else throw (.unsupported "native nonzero address-space pointer")
      | _ => throw (.unsupported "unsupported scalar type for native call")
    | _ =>
      match ← q.typeShape choice layout with
      | .emptyTuple => pure .void
      | .adt _ isStruct reprC fields =>
        unless isStruct && reprC do throw (.unsupported "native call requires repr(C) struct")
        let mut result := #[]
        for field in fields do result := result.push (← ffiType q choice fuel (← queryLayout q choice field))
        pure (.structureType result)
      | .other => throw (.unsupported "unsupported type for native call")

structure ClosureHost (S C Code : Type) where
  /-- Actual libffi Builder/closure/code pointer. Source intentionally leaks
  both data and closure until process exit, retaining its context interchange.
  For unsupported signatures the builder receives no descriptors and must
  install the source diagnostic-and-exit trampoline, not reject construction. -/
  build : C → Option (Array Native.FfiType × Native.FfiType) → Bool → RvalueM S Code

/-- Only source unsupported-signature errors choose the aborting descriptor.
Missing compiler evidence, resource limits and machine failures propagate. -/
def buildClosure (queries : Queries S C) (host : ClosureHost S C Code)
    (choice : C) (fuel : Nat) (inputs : Array TyId) (output : TyId) : RvalueM S Code := do
  let signature ← try
    let mut arguments := #[]
    for input in inputs do
      arguments := arguments.push (← ffiType queries choice fuel (← queryLayout queries choice input))
    let result ← ffiType queries choice fuel (← queryLayout queries choice output)
    pure (some (arguments,result))
    catch error => match error with
      | .unsupported _ => pure none
      | _ => throw error
  host.build choice signature signature.isNone
end Miri.Interpreter.NativeAbi
