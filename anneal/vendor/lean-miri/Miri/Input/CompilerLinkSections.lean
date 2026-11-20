import Miri.Input.CompilerMain
import Miri.Input.CompilerFunctionPointers
import Miri.Input.CompilerPrimitiveFacts
import Miri.Interpreter.IntrinsicVectorMachine

/-! helpers.rs::lookup_link_section, eval_context.rs::eval_global and
place.rs::raw_const_to_mplace. Source symbol order and used filtering are
exported; actual static pointers, initializer reads and projection execute here.
-/
namespace Miri.Input.CompilerLinkSections
open Lean Miri.ABI Miri.Memory Miri.Interpreter
structure Memory (K U Other : Type) where
  functions : FunctionPointers.Hooks K U Other
  externStatic : MIR.DefId → MachineHooks.M K U (Pointer Provenance)
  projection : MachineHooks.M K U (ProjectionCx Provenance)
  readImmediate : OpTy Provenance → MachineHooks.M K U (RvalueImmTy Provenance)
structure GlobalRef where
  definition : MIR.DefId
  ty : MIR.TyId
  allocation : AllocationId
  expectStatic : Bool
private def lift (query : Except String A) : MachineHooks.M K U A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported error)
private def project (query : Except ProjectionError A) : MachineHooks.M K U A :=
  match query with | .ok value => pure value | .error error => throw (IntrinsicVectorMachine.projectionError error)

def globalRef (runtime : RuntimeMetadata) (h : Memory K U Other) (entryData : GlobalRef) :
    MachineHooks.M K U (OpTy Provenance) := do
  let memory := (← get).machine.memory
  let id ← lift (AllocationImage.runtimeId memory entryData.allocation)
  let some info := memory.findGlobal? id | throw (.unsupported "link-entryData global allocation metadata absent")
  let pointer ← match info.payload with
    | some (.static definition isStatic threadLocal foreignItem) => do
      unless entryData.expectStatic && isStatic && definition == entryData.definition do
        throw (.invalidProgram "named global static identity/query mismatch")
      if threadLocal then throw (.invalidProgram "source global_root_pointer cannot form a constant TLS pointer")
      if foreignItem then h.externStatic definition else FunctionPointers.rootPointer h.functions id
    | _ => do
      unless !entryData.expectStatic do
        throw (.invalidProgram "named global static query did not import a static allocation")
      FunctionPointers.rootPointer h.functions id
  let layout ← lift (runtime.lookup entryData.ty |>.mapError toString)
  unless layout.layout.isSized do throw (.invalidProgram "source global place requires a sized layout")
  pure ⟨.indirect ⟨pointer.withOptionalProvenance,.none,none⟩,layout⟩

def global (p : CompilerMain.Prepared) (h : Memory K U Other) (entryData : CompilerMain.Section) :
    MachineHooks.M K U (OpTy Provenance) :=
  globalRef p.runtime h ⟨entryData.definition,entryData.ty,entryData.allocation,true⟩

/-- Reads occur in source order; earlier initialization/provenance/race effects
remain in the machine if a later static or element read fails. -/
def lookup (p : CompilerMain.Prepared) (h : Memory K U Other) (includeName : String → Bool) :
    MachineHooks.M K U (Array (TlsImmediate Provenance × MIR.SpanRef)) := do
  let mut values := #[]
  for entry in ← lift p.sections do
    if !includeName entry.name then continue
    let entryData ← lift entry.result
    let operand ← global p h entryData
    let node ← lift (p.runtime.node operand.layout.ty |>.mapError toString)
    unless node.shapeStatus == .supported do throw (.unsupported "link-entryData value type shape missing")
    if node.shapeKind == .functionPointer then
      let value ← h.readImmediate operand
      values := values.push (⟨value.imm,value.layout⟩,entryData.span)
    else if node.shapeKind == .array then
      let element ← lift (p.runtime.field operand.layout 0 |>.mapError toString)
      let elementNode ← lift (p.runtime.node element.ty |>.mapError toString)
      unless elementNode.shapeStatus == .supported && elementNode.shapeKind == .functionPointer do
        throw (.unsupported "only FnPtr and arrays of FnPtr are supported in well-known linker sections")
      let cx ← h.projection
      let unit ← lift (CompilerPrimitiveFacts.unitLayout p.runtime)
      let mut iterator ← project (projectArrayFields cx operand unit)
      repeat
        let cx ← h.projection
        match ProjectionArrayIterator.next cx iterator with
        | .error error _ => throw (IntrinsicVectorMachine.projectionError error)
        | .ok none _ => break
        | .ok (some (_,element)) after =>
          iterator := after
          let value ← h.readImmediate element
          values := values.push (⟨value.imm,value.layout⟩,entryData.span)
    else throw (.unsupported "only FnPtr and arrays of FnPtr are supported in well-known linker sections")
  pure values
/-- Main's linker-section compiler query executes actual imported global reads;
all MainMachine scheduler/callback/termination effects remain unchanged. -/
def hooks (p : CompilerMain.Prepared) (memory : Memory MiriMemoryKind (ThreadStacks.Storage U) O)
    (base : MainMachine.Hooks U C O ABI.ExternAbi F A Aff P) :
    MainMachine.Hooks U C O ABI.ExternAbi F A Aff P :=
  {CompilerMain.hooks p base with lookupLinkSection := lookup p memory}
end Miri.Input.CompilerLinkSections
