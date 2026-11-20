import Miri.Interpreter.ProgramExit

/-! Pinned shims/global_ctor.rs::GlobalCtorState::on_stack_empty (23-98).
Binary format is explicit target metadata. Link sections are matched exactly;
constructor lists retain source order and are popped from the end. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.Concurrency
inductive ConstructorBinaryFormat where
  | coff | machO | elf | wasm | other (name : String)
inductive GlobalCtorStage (P : Type) where
  | init
  | constructors (remaining : Array (TlsImmediate P × MIR.SpanRef))
  | done
structure GlobalCtorState (P E H : Type) where
  execution : TlsExecutionState P E H
  stage : GlobalCtorStage P
abbrev GlobalCtorM (P E H Error A : Type) := EStateM (TlsExecutionError Error) (GlobalCtorState P E H) A
structure GlobalCtorQueries (P E H Error : Type) where
  lookupLinkSection : (String → Bool) → GlobalCtorM P E H Error (Array (TlsImmediate P × MIR.SpanRef))
  getPointerFnInstance : Pointer (Option P) → GlobalCtorM P E H Error CallInstance
  /-- Actual call_thread_root_function with C ABI, unwind=false, no arguments,
  no return destination, Stop{cleanup:true}, source empty-stack/origin checks. -/
  callConstructor : CallInstance → MIR.SpanRef → GlobalCtorM P E H Error Unit

/-- Source splitn(3, ',') retains the entire suffix in the third component. -/
def constructorSectionMatches (format : ConstructorBinaryFormat) (sectionName : String) : Bool :=
  match format with
  | .coff => sectionName == ".CRT$XCU"
  | .elf | .wasm => sectionName == ".init_array"
  | .machO =>
    match sectionName.splitOn "," with
    | [segment,name] => segment == "__DATA" && name == "__mod_init_func"
    | [segment,name,kind] => segment == "__DATA" && name == "__mod_init_func" && kind == "mod_init_funcs"
    | _ => false
  | .other _ => false

def globalConstructorsOnStackEmpty [PointerProvenance P] (format : ConstructorBinaryFormat)
    (target : RuntimeTargetDataLayout) (queries : GlobalCtorQueries P E H Error) :
    GlobalCtorM P E H Error StackEmptyCallbackResult := do
  let state ← EStateM.get
  match state.stage with
  | .init =>
    match format with
    | .other _ => EStateM.set { state with stage := .done }
    | _ =>
      let constructors ← queries.lookupLinkSection (constructorSectionMatches format)
      let after ← EStateM.get
      EStateM.set { after with stage := .constructors constructors }
    pure .Pending
  | .constructors constructors =>
    match constructors.back? with
    | none => EStateM.set { state with stage := .done }; pure .Pending
    | some (constructor,span) =>
      -- Pop precedes scalar conversion/function resolution/call, including errors.
      EStateM.set { state with stage := .constructors constructors.pop }
      let scalar ← match constructor.value.toScalar with
        | .ok scalar => pure scalar
        | .error error => throw (.immediate error)
      let pointer ← match scalar.toPointer target.base with
        | .ok pointer => pure pointer
        | .error error => throw (.scalar error)
      let fnInstance ← queries.getPointerFnInstance pointer
      queries.callConstructor fnInstance span
      pure .Pending
  | .done => pure .Ready
end Miri.Interpreter
