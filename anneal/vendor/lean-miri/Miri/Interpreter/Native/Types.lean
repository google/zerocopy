import Miri.Interpreter.ScalarOps

/-! Pinned `shims/native_lib/mod.rs` boundary data. Host addresses are bounded
by the configured host usize, independently of the MIR target pointer width. -/
namespace Miri.Interpreter.Native
open Miri.ABI Miri.Memory Miri.MIR
inductive FfiType where
  | i8 | i16 | i32 | i64 | u8 | u16 | u32 | u64 | f32 | f64 | pointer | void
  | structureType (fields : Array FfiType)
  deriving Repr
structure OwnedArg where
  type : FfiType
  bytes : Array UInt8
  deriving Repr
structure AccessRange where
  addr : Nat
  size : Nat
  deriving DecidableEq, Repr
inductive AccessEvent where
  | read (range : AccessRange)
  | write (range : AccessRange) (certain : Bool)
  deriving DecidableEq, Repr
def AccessEvent.range : AccessEvent → AccessRange
  | .read r | .write r _ => r
structure StartFfiInfo where
  pagePtrs : Array Nat
  stackPtr : Nat
  deriving Repr
inductive TraceRequest where
  | startFfi (info : StartFfiInfo)
  | overrideRetcode (code : Int32)
  deriving Repr
inductive TypeShape where
  | adt (isEnum isStruct reprC : Bool) (fields : Array TyId)
  | emptyTuple
  | other
  deriving Repr
structure RawAllocation (P : Type) where
  address : Nat
  size : Nat
  mutable : Bool
  /-- Provenance range enumeration must retain source order. -/
  provenances : Array P
  deriving Repr
structure Library where
  path : String
  deriving Repr
structure SymbolInfo (Code : Type) where
  code : Code
  /-- `dladdr` success and UTF8 conversion are required backend checks. -/
  definingPath : String
  deriving Repr
end Miri.Interpreter.Native
