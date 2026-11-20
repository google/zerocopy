import Miri.Input.CompilerNative
import Miri.Interpreter.NativeAddressSource

/-! Exact native callback signature from alloc_addresses/mod.rs:167–174.
The catalog records the actual compiler query after full-instance substitution
and bound-region erasure, with no normalization or FnAbi reconstruction. -/
namespace Miri.Input.CompilerNativeSignatures
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private def typeRef (p : CompilerProviders.Prepared) (value : Json) : Except String TyId := do
  let id ← value.getObjValAs? Nat "type_id"
  let _ ← p.runtime.node id |>.mapError toString
  pure id

def query (p : CompilerProviders.Prepared) (callee : CallInstance) : Except String (Array TyId × TyId) := do
  let entries ← (← p.program.input.raw.getObjVal? "compiler_native_signature_queries").getArr?
  let ctx := LowerContext.ofDocument p.program.input
  let tables := p.program.compilerTables
  let mut found : Option (Array TyId × TyId) := none
  for entry in entries do
    let (actual,next) ← match CompilerInstance.decode ctx tables entry with
      | .ok value => pure value
      | .error _ => continue
    if actual == callee then
      unless next.definitions == tables.definitions && next.typeConstants == tables.typeConstants do
        throw "native signature query requires unprepared compiler identity"
      unless (← entry.getObjValAs? String "query") ==
          "instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))" &&
          (← entry.getObjValAs? String "normalization") == "none" &&
          (← entry.getObjValAs? String "bound_regions") == "erased" do
        throw "native signature query operation/region-erasure evidence mismatch"
      let value ← entry.getObjVal? "signature_query"
      unless (← value.getObjValAs? String "status") == "supported" do
        throw "native signature compiler query unavailable for demanded full instance"
      let signature ← value.getObjVal? "value"
      let inputs ← (← (← signature.getObjVal? "inputs").getArr?).mapM (typeRef p)
      let output ← typeRef p (← signature.getObjVal? "output")
      let result := (inputs,output)
      if let some old := found then
        unless old == result do throw "conflicting native signature queries for exact full instance"
      found := some result
  let some result := found | throw "missing exact compiler native signature query"
  pure result

private def lift (value : Except String A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"native function signature: {reason}")

/-- Imported compiler functions resolve through their actual image identity;
dynamic reservations resolve through the canonical full-instance registry. -/
private def makeUsing (p : CompilerProviders.Prepared)
    (lookup : CompilerVTableRuntime.GlobalLookup p.lifecycle.calls.symbols)
    (image : AllocationImage.Imported)
    (arrays : RuntimeArrayQueries.Access (MachineAddress.State K U))
    (registry : PointerMachine.User U → FunctionPointers.Registry Other) :
    NativeAddressSource.Compiler K U C where
  queries := CompilerNative.abiQueries p arrays
  functionSignature := fun _ id => do
    let machine ← get
    let callee ← if machine.memory.hasImportedRuntimeId id then do
      let some callee ← lift (CompilerVTableRuntime.globalFunctionUsing p.lifecycle.calls.symbols lookup image machine.memory id)
        | throw (.invalidProgram "native compiler function has non-function imported identity")
      pure callee
    else do
      let entries := (registry machine.user).functions.filter (·.allocation == id)
      unless entries.size == 1 do throw (.unsupported "native function lacks unique canonical full-instance reservation")
      let some entry := entries[0]? | throw (.invalidProgram "native function reservation vanished")
      pure entry.callee
    lift (query p callee)

def make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (arrays : RuntimeArrayQueries.Access (MachineAddress.State K U))
    (registry : PointerMachine.User U → FunctionPointers.Registry Other) :
    NativeAddressSource.Compiler K U C :=
  makeUsing p (CompilerVTableRuntime.GlobalLookup.prepare p.lifecycle.calls.symbols)
    image arrays registry
/-- Remaining native capabilities are actual allocator/libffi effects plus
source build configuration and a finite compiler traversal budget. -/
structure Host (K U C : Type) where
  backing : NativeAllocationLifecycle.Backing (MachineAddress.State K U)
  closure : NativeAbi.ClosureHost (MachineAddress.State K U) C Nat
  closuresEnabled : Bool
  queryBudget : Nat

/-- Optional native construction installs the direct compiler catalog adapter;
callers cannot supply a substitute whole function-signature query here. -/
def effects (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (arrays : RuntimeArrayQueries.Access (MachineAddress.State K U))
    (registry : PointerMachine.User U → FunctionPointers.Registry Other)
    (host : Host K U C) : NativeAddressSource.Effects K U C where
  backing := host.backing
  compiler := make p image arrays registry
  closure := host.closure
  closuresEnabled := host.closuresEnabled
  queryBudget := host.queryBudget

def optionalEffects (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (arrays : RuntimeArrayQueries.Access (MachineAddress.State K U))
    (registry : PointerMachine.User U → FunctionPointers.Registry Other)
    (host : Option (Host K U C)) : Option (NativeAddressSource.Effects K U C) :=
  host.map (effects p image arrays registry)
end Miri.Input.CompilerNativeSignatures
