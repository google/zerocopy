import Miri.Input.CompilerInstance
import Miri.Interpreter.Constant

/-! Actual compiler ValueNS path resolution and const_eval_instance evidence
for helpers.rs::eval_path_scalar/eval_libc. Original full constant identity,
query environment, type, value and raw payload remain available. Allocation
values use the canonical Constant pipeline, preserving graph provenance.
-/
namespace Miri.Input.CompilerNamedConstants
open Lean Miri.ABI Miri.Memory Miri.Interpreter
structure Value where
  sourceInstance : CallInstance
  ty : MIR.TyId
  value : MIR.ConstValue
structure Entry where
  name : String
  result : Except String Value
  payload : Json
structure Prepared where
  program : LoweredProgram
  runtime : RuntimeMetadata
  entries : Array Entry
private def supported (j : Json) : Except String Unit := do
  unless (← (← j.getObjVal? "status").getStr?) == "supported" do
    throw s!"named compiler constant unavailable: {((j.getObjVal? "reason").bind Json.getStr?).toOption}"

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : Except String Prepared := do
  unless RuntimeMetadata.JsonReflexivity.matchesRightOr sourceEquality program.input.raw do
    throw "named constant metadata document mismatch"
  let records ← (← program.input.raw.getObjVal? "compiler_named_constants").getArr?
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut entries := #[]
  for record in records do
    let name ← (← record.getObjVal? "name").getStr?
    unless !(entries.any (·.name == name)) do throw "duplicate compiler named constant query"
    unless (← (← record.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do
      throw "named constant compiler environment mismatch"
    let query ← record.getObjVal? "query"
    let origin := do
      supported query
      CompilerInstance.decode ctx tables query
    let result ← match origin with
      | .error reason => pure (.error reason)
      | .ok (sourceInstance,next) =>
        tables := next
        pure (do
          let ty ← (← (← query.getObjVal? "type").getObjVal? "type_id").getNat?
          unless ctx.containsTypeId ty do throw "named constant references missing compiler type"
          let evaluated ← query.getObjVal? "evaluation"
          supported evaluated
          let value ← lowerCompilerConstValue ctx ty (← ctx.decodeCompilerValue (← evaluated.getObjVal? "value"))
          pure (⟨sourceInstance,ty,value⟩ : Value))
    entries := entries.push ⟨name,result,record⟩
  pure ⟨program.withCompilerTables tables,runtime,entries⟩

def value (prepared : Prepared) (name : String) : Except String Value := do
  let some entry := prepared.entries.find? (·.name == name)
    | throw s!"missing compiler named constant query {name}"
  entry.result

/-- Scalar-only fast path preserves the actual bits and byte width. Allocation
pointers/slices/indirect values require toOp and actual global memory hooks. -/
def scalar (prepared : Prepared) (name : String) : Except String (Scalar P) := do
  let entry ← value prepared name
  let layout ← prepared.runtime.lookup entry.ty |>.mapError toString
  let (bits,width) ← match entry.value with
    | .Scalar (.Int bits width) => pure (bits,width)
    | .Scalar (.Ptr (.Address bits width)) =>
      let pointer ← prepared.runtime.target.pointerSizeIn prepared.runtime.target.defaultAddressSpace |>.mapError toString
      unless width == pointer.bytes.toNat do throw "compiler pointer constant target-width mismatch"
      pure (bits,width)
    | _ => throw "named constant requires canonical allocation materialization via Constant.constValueToOp"
  unless width < 2^64 && layout.layout.size.bytes.toNat == width && bits < 2^128 do
    throw "compiler named scalar width/type/bits mismatch"
  Scalar.fromUInt (BitVec.ofNat 128 bits) (.ofBytes (UInt64.ofNat width)) |>.mapError (fun error => reprStr error)

def i32 (prepared : Prepared) (name : String) : Except String Int32 := do
  let entry ← value prepared name
  let .Scalar (.Int bits width) := entry.value | throw "libc i32 constant is not an integer scalar"
  unless width == 4 && bits < 2^128 do throw "libc i32 scalar representation mismatch"
  let integer ← ScalarInt.tryFromUInt (BitVec.ofNat 128 bits) (.ofBytes 4) |>.mapError (fun error => reprStr error)
  let some integer := integer | throw "libc i32 bits exceed compiler scalar width"
  integer.toInt32 |>.mapError (fun error => reprStr error)

def toOp [DecidableEq K] (prepared : Prepared) (queries : ConstantQueries P E K H) (name : String) :
    ConstantM P E K H (OpTy P) := do
  let entry ← match value prepared name with
    | .ok value => pure value
    | .error error => throw (.metadata error)
  constValueToOp prepared.runtime queries entry.value entry.ty
end Miri.Input.CompilerNamedConstants
