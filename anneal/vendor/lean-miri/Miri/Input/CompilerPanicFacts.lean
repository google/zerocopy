import Miri.Input.LowerMIR
import Miri.Interpreter.Panic

/-! Exact language-item definitions and Instance::mono generic parameters.
Definition IDs are appended before shared provider preparation. Missing query
metadata stays a demanded compiler obligation, never a successful panic. -/
namespace Miri.Input.CompilerPanicFacts
open Lean Miri.ABI Miri.Interpreter

def name : Panic.LangItem → String
  | .Panic => "Panic"
  | .PanicNounwind => "PanicNounwind"
  | .PanicBoundsCheck => "PanicBoundsCheck"
  | .PanicMisalignedPointerDereference => "PanicMisalignedPointerDereference"
  | .PanicAddOverflow => "PanicAddOverflow"
  | .PanicSubOverflow => "PanicSubOverflow"
  | .PanicMulOverflow => "PanicMulOverflow"
  | .PanicDivOverflow => "PanicDivOverflow"
  | .PanicRemOverflow => "PanicRemOverflow"
  | .PanicNegOverflow => "PanicNegOverflow"
  | .PanicShrOverflow => "PanicShrOverflow"
  | .PanicShlOverflow => "PanicShlOverflow"
  | .PanicDivZero => "PanicDivZero"
  | .PanicRemZero => "PanicRemZero"
  | .PanicNullPointerDereference => "PanicNullPointerDereference"
  | .PanicNullReferenceConstructed => "PanicNullReferenceConstructed"
  | .PanicInvalidEnumConstruction => "PanicInvalidEnumConstruction"
  | .PanicCoroutineResumed => "PanicCoroutineResumed"
  | .PanicAsyncFnResumed => "PanicAsyncFnResumed"
  | .PanicAsyncGenFnResumed => "PanicAsyncGenFnResumed"
  | .PanicGenFnNone => "PanicGenFnNone"
  | .PanicCoroutineResumedPanic => "PanicCoroutineResumedPanic"
  | .PanicAsyncFnResumedPanic => "PanicAsyncFnResumedPanic"
  | .PanicAsyncGenFnResumedPanic => "PanicAsyncGenFnResumedPanic"
  | .PanicGenFnNonePanic => "PanicGenFnNonePanic"
  | .PanicCoroutineResumedDrop => "PanicCoroutineResumedDrop"
  | .PanicAsyncFnResumedDrop => "PanicAsyncFnResumedDrop"
  | .PanicAsyncGenFnResumedDrop => "PanicAsyncGenFnResumedDrop"
  | .PanicGenFnNoneDrop => "PanicGenFnNoneDrop"

private def parameterTag : MainGenericParameter → Nat
  | .lifetime => 0 | .typeParameter => 1 | .constParameter => 2

private def definition (source : Json) : Except String DefinitionId := do
  pure ⟨← source.getObjValAs? Nat "crate",← source.getObjValAs? Nat "index"⟩
private def rows (p : LoweredProgram) : Except String (Array Json) := do
  (← p.input.raw.getObjVal? "compiler_panic_queries").getArr?

/-- An absent catalog is not demanded by preparing an unrelated function.
Actual panic queries still fail. Present definitions join the final shared
append-only table; no returned compiler DefId is invented at the call event. -/
def prepareProgram (program : LoweredProgram) : Except String LoweredProgram := do
  let source ← match program.input.raw.getObjVal? "compiler_panic_queries" with
    | .error _ => return program | .ok value => pure value
  let mut definitions := program.compilerTables.definitions
  let mut tags : Array String := #[]
  for row in ← source.getArr? do
    let tag ← row.getObjValAs? String "lang_item"
    if tags.contains tag then throw "duplicate panic language-item query"
    tags := tags.push tag
    if (← row.getObjValAs? String "status") == "supported" then
      let item ← row.getObjVal? "definition"
      unless item == .null do
        let source ← definition item
        unless definitions.contains source do definitions := definitions.push source
  pure (program.withCompilerTables {program.compilerTables with definitions})

def langItemByName (program : LoweredProgram) (tag : String) : Except String (Option MIR.DefId) := do
  let selected := (← rows program).filter fun row =>
    (row.getObjValAs? String "lang_item").toOption == some tag
  unless selected.size == 1 do throw "exact panic language-item query is missing or duplicated"
  let some row := selected[0]? | throw "panic language-item query absent"
  unless (← row.getObjValAs? String "status") == "supported" do throw "panic language-item query unresolved"
  let value ← row.getObjVal? "definition"
  if value == .null then return none
  pure (some (← lookupDefinitionId program.compilerTables.definitions (← definition value)))

def langItem (program : LoweredProgram) (item : Panic.LangItem) : Except String (Option MIR.DefId) :=
  langItemByName program (name item)

def genericParameters (program : LoweredProgram) (requested : MIR.DefId) :
    Except String (Array MainGenericParameter) := do
  let mut found : Option (Array MainGenericParameter) := none
  for row in ← rows program do
    unless (← row.getObjValAs? String "status") == "supported" do continue
    let value ← row.getObjVal? "definition"
    if value == .null then continue
    let id ← lookupDefinitionId program.compilerTables.definitions (← definition value)
    unless id == requested do continue
    let params ← (← (← row.getObjVal? "generic_parameters").getArr?).mapM fun value => do
      match ← value.getStr? with
      | "lifetime" => pure MainGenericParameter.lifetime
      | "type_parameter" => pure .typeParameter
      | "const_parameter" => pure .constParameter
      | _ => throw "unknown compiler panic generic parameter kind"
    if let some earlier := found then
      unless earlier.map parameterTag == params.map parameterTag do throw "conflicting compiler generic parameters for panic definition"
    found := some params
  match found with
  | none => throw "compiler panic definition has no generic-parameter query"
  | some params => pure params
/-- machine.rs::unwind_terminate uses reason.lang_item followed by
Instance::mono, retaining erased lifetime arguments and rejecting type/const
parameters. Missing compiler records remain unsupported; absent required lang
items are source invariant errors. -/
def unwindTerminate (program : LoweredProgram) (reason : MIR.UnwindTerminateReason) :
    Except StepError CallInstance := do
  let tag := match reason with | .Abi => "PanicCannotUnwind" | .InCleanup => "PanicInCleanup"
  let some definition ← langItemByName program tag |>.mapError StepError.unsupported
    | throw (.invalidProgram "missing unwind termination language item")
  let mut args := #[]
  for parameter in ← genericParameters program definition |>.mapError StepError.unsupported do
    match parameter with
    | .lifetime => args := args.push (.Lifetime .Erased)
    | .typeParameter | .constParameter =>
      throw (.invalidProgram "Instance::mono called on type/const generic unwind termination item")
  pure ⟨.Item definition,args⟩
end Miri.Input.CompilerPanicFacts
