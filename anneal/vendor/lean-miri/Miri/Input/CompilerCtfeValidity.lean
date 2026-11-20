import Miri.Input.CompilerProviders
import Miri.Input.CompilerGlobals
import Miri.Interpreter.TypedMemoryProviders

/-! Pinned validity.rs:725–811 CTFE recursion lookup. This performs the real
zero-size pointer identity query and reads canonical TCX globals independently
of local materialization. Nested-static predicates are exact compiler evidence,
never guessed from names, initializer bytes or whether a local copy exists. -/
namespace Miri.Input.CompilerCtfeValidity
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

private def lift (value : Except String A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"CTFE validity compiler lookup: {reason}")

private def staticKind (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (id : AllocId) (global : GlobalAllocation) : Except String Validity.GlobalAllocationKind := do
  let some (.static definition isStatic tls foreignItem) := global.payload
    | throw "CTFE static predicates are unavailable"
  unless isStatic && !tls do throw "CTFE static is not a non-thread-local static"
  let source ← image.sourceNode memory id
  let some (.static source) := source.data | throw "CTFE static lacks actual compiler image identity"
  let actual ← lookupDefinitionId p.program.compilerTables.definitions source.definitionId
  unless actual == definition do throw "CTFE static compiler definition identity mismatch"
  let info ← CompilerGlobals.staticInfo source
  unless info.size == global.size && info.align == global.align && info.mutability == global.mutability &&
      info.foreignItem == foreignItem do throw "CTFE static compiler metadata disagrees with canonical global"
  let some evidence := source.globalInfo | throw "CTFE nested-static compiler evidence missing"
  let nested ← evidence.payload.getObjValAs? Bool "nested"
  pure (.static nested foreignItem)

/-- Source ptr_try_get_alloc_id errors mean there is no allocation identity;
internal resolver invariants remain explicit StepErrors. Missing TCX globals
are distinguished from still-local allocations, as the delayed-bug branch is. -/
def lookup (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (_ : C) (place : MPlaceTy Provenance) (_mode : Validity.CtfeMode) :
    ValidityMachine.M K U Validity.PointerAllocLookup := do
  let resolved ← fun state =>
    match TypedMemoryProviders.resolvePointer pointers state.machine.memory place.mplace.ptr 0 state.machine with
    | .ok value machine => .ok value {state with machine}
    | .error error machine => .error error {state with machine}
  let .ok resolved := resolved | return .noAllocationId
  let memory := (← get).machine.memory
  let some global := memory.findGlobal? resolved.allocId
    | return .missingGlobal (memory.live.any (·.1 == resolved.allocId))
  let kind ← if global.kind == .static then do
      if let some (.static _ isStatic tls _) := global.payload then
        unless isStatic && !tls do throw (.invalidProgram "CTFE static declaration invariant failed")
      lift (staticKind p image memory resolved.allocId global)
    else pure .other
  pure (.global global.size global.mutability kind)
end Miri.Input.CompilerCtfeValidity
