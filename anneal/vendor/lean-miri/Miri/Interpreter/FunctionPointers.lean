import Miri.Interpreter.VTable
import Miri.Interpreter.Unwind
import Miri.Interpreter.PointerMachine
import Miri.Interpreter.Backtrace
import Miri.Interpreter.Cast

/-! Source memory.rs fn_ptr/get_fn_alloc/get_ptr_fn and machine.rs salt/root
provenance. Function identities are full instances, never numeric addresses. -/
namespace Miri.Interpreter.FunctionPointers
open Miri.ABI Miri.Memory Miri.MIR Miri.Memory.AllocAddresses
open MachineHooks (M State)
structure FunctionEntry where
  callee : CallInstance
  salt : Fin 32
  allocation : AllocId
structure Registry (Other : Type) where
  functions : Array FunctionEntry
  extras : Array (AllocId × Other)

/-- Empty means no functions have yet been reserved. Imported global functions
must be seeded explicitly when attaching an already populated compiler image. -/
def Registry.empty : Registry Other := ⟨#[],#[]⟩

/-- Merge TCX-wide `GlobalAlloc::Function(instance,salt)` reservations into a
fresh EvalWorld registry. Imported image entries are seeded by startup and
must agree with any identity retained from an earlier Miri world. Per-world
`FnVal::Other` entries deliberately stay in the fresh registry: source Miri
allocates those with `reserve_alloc_id` rather than the TCX dedup cache. -/
def Registry.mergePersistent (fresh live : Registry Other) : Except String (Registry Other) := do
  let mut functions := fresh.functions
  for entry in live.functions do
    if let some old := functions.find? (fun old => old.callee == entry.callee && old.salt == entry.salt) then
      unless old.allocation == entry.allocation do
        throw "conflicting TCX function reservation for the same instance and salt"
    else
      if functions.any (·.allocation == entry.allocation) then
        throw "TCX function allocation ID is assigned to multiple instance/salt keys"
      if fresh.extras.any (·.1 == entry.allocation) then
        throw "TCX function allocation ID collides with a fresh extra function"
      functions := functions.push entry
  pure { fresh with functions }

structure Hooks (K User Other : Type) where
  registry : User → Registry Other
  putRegistry : User → Registry Other → User
  crossCrateInlineAlways : Bool
  inlineNever : CallInstance → M K User Bool
  chooseSalt : M K User (Fin 32)
  ptrGetAlloc : Pointer Provenance → M K User (Option (AllocId × Size))
  adjustRootPointer : AllocId → BorTag → M K User (Pointer Provenance)
  importedFunction : AllocId → M K User (Option CallInstance)

private def registry (h : Hooks K User Other) : M K User (Registry Other) := do
  return h.registry (← get).machine.user
private def setRegistry (h : Hooks K User Other) (value : Registry Other) : M K User Unit :=
  modify fun state => {state with machine := {state.machine with user := h.putRegistry state.machine.user value}}

/-- Both generic-argument inspection and inline-attribute query precede the
uniqueness decision. The threshold Always short-circuits the compiler query. -/
def globalSalt (h : Hooks K User Other) (callee : CallInstance) : M K User (Fin 32) := do
  let generic := callee.args.any fun arg => match arg with | .Lifetime _ => false | _ => true
  let canInline : Bool ← if h.crossCrateInlineAlways then pure true else do
    let never ← h.inlineNever callee
    pure (!never)
  if !generic && !canInline then return ⟨0,by decide⟩
  h.chooseSalt

private def reserve (h : Hooks K User Other) (value : FnVal Other) : M K User AllocId := do
  match value with
  | .Instance callee =>
    let salt ← globalSalt h callee
    let entries ← registry h
    if let some existing := entries.functions.find? (fun e => e.callee == callee && e.salt == salt) then
      return existing.allocation
    let state ← get
    if state.machine.memory.sourceAllocIdWorldActive then
      throw (.unsupported "source function AllocId key/salt is not captured by the prepared raw-world profile")
    let (memory,result) := state.machine.memory.reserveAllocId
    set {state with machine := {state.machine with memory}}
    let id ← match result with
      | .ok id => pure id
      | .error error => throw (.resourceExhaustion s!"function allocation ID: {reprStr error}")
    let state ← get
    let memory := MemoryState.pushGlobal state.machine.memory
      ⟨id,.function,.ZERO,.ONE,.Not,some .function⟩
    set {state with machine := {state.machine with memory}}
    let entries ← registry h
    setRegistry h {entries with functions := entries.functions.push ⟨callee,salt,id⟩}
    return id
  | .Other extra =>
    let state ← get
    let (memory,result) := state.machine.memory.reserveAllocId
    set {state with machine := {state.machine with memory}}
    let id ← match result with
      | .ok id => pure id
      | .error error => throw (.resourceExhaustion s!"extra function allocation ID: {reprStr error}")
    let entries ← registry h
    if entries.extras.any (·.1 == id) then throw (.invalidProgram "extra function ID already present")
    setRegistry h {entries with extras := entries.extras.push (id,extra)}
    modify fun state => {state with machine := {state.machine with memory := state.machine.memory.registerExtraFunction id}}
    return id

/-- Function globals cannot be TLS/extern statics. Borrow root tags are created
before address assignment, and retained if the latter fails. -/
def rootPointer (h : Hooks K User Other) (id : AllocId) : M K User (Pointer Provenance) := do
  let state ← get
  let tag ← match state.machine.borrowTracker with
    | none => pure BorTag.one
    | some tracker =>
      match tracker.global.rootPointerTag id with
      | .error error => throw (.resourceExhaustion s!"function root tag: {reprStr error}")
      | .ok (global,tag) =>
        set {state with machine := {state.machine with borrowTracker := some {tracker with global}}}
        pure tag
  h.adjustRootPointer id tag

def functionPointer (h : Hooks K User Other) (value : FnVal Other) : M K User (Pointer Provenance) := do
  rootPointer h (← reserve h value)

/-- Source ptr_get_alloc_id(ptr,0): missing provenance is dangling even when an
integer happens to equal a function address. Wildcards use actual exposed lookup. -/
def allocation (h : Hooks K User Other) (pointer : Pointer (Option Provenance)) :
    M K User (AllocId × Size) := do
  let .ok pointer := pointer.intoPointerOrAddr
    | throw (.undefinedBehavior "DanglingIntPointer")
  let some result ← h.ptrGetAlloc pointer | throw (.undefinedBehavior "DanglingIntPointer")
  return result

def globalFunction (h : Hooks K User Other) (id : AllocId) : M K User (Option CallInstance) := do
  let entries ← registry h
  if let some entry := entries.functions.find? (·.allocation == id) then return some entry.callee
  if entries.extras.any (·.1 == id) then return none
  if let .ok info := (← get).machine.memory.getAllocInfo id then
    if info.kind != .function then return none
  h.importedFunction id

def getFnAlloc (h : Hooks K User Other) (id : AllocId) : M K User (Option (FnVal Other)) := do
  if let some (_,extra) := (← registry h).extras.find? (·.1 == id) then return some (.Other extra)
  return (← globalFunction h id).map FnVal.Instance

def getPtrFn (h : Hooks K User Other) (pointer : Pointer (Option Provenance)) : M K User (FnVal Other) := do
  let (id,offset) ← allocation h pointer
  if offset != .ZERO then throw (.undefinedBehavior "InvalidFunctionPointer")
  let some value ← getFnAlloc h id | throw (.undefinedBehavior "InvalidFunctionPointer")
  return value

/-- Close actual absolute-address resolution and adjustment with PointerMachine.
Random address choices remain explicit source outcomes, not a fixed seed. -/
def pointerMachine (pointer : PointerMachine.Hooks K User)
    (choices : AllocId → AddressRandomChoices)
    (base : Hooks K (PointerMachine.User User) Other) : Hooks K (PointerMachine.User User) Other :=
  {base with
    ptrGetAlloc := fun p => PointerMachine.ptrGetAlloc pointer p 0
    adjustRootPointer := fun id tag =>
      PointerMachine.adjustAllocRootPointer pointer id tag .ZERO .other (choices id)}

/-- A lawful embedding of existing address state into a larger concrete machine
user record (for example ThreadStacks.Storage). No second frame stack is made. -/
structure AddressLens (User Payload : Type) where
  get : User → PointerMachine.User Payload
  put : User → PointerMachine.User Payload → User
  getPut : ∀ user value, get (put user value) = value
  putGet : ∀ user, put user (get user) = user
  putPut : ∀ user first second, put (put user first) second = put user second

private def addressAction (lens : AddressLens User Payload) (action : PointerMachine.M K Payload A) :
    M K User A := fun state =>
  let machine := state.machine
  let projected := {machine with user := lens.get machine.user}
  let initial : PointerMachine.State K Payload := ⟨state.stack,projected⟩
  match action initial with
  | .ok value result => .ok value ⟨result.stack,
      {result.machine with user := lens.put machine.user result.machine.user}⟩
  | .error error result => .error error ⟨result.stack,
      {result.machine with user := lens.put machine.user result.machine.user}⟩

/-- Same actual address engine under a lawful user-record embedding. All memory,
borrow/race/thread/stack mutations survive both result branches. -/
def pointerMachineVia (lens : AddressLens User Payload)
    (pointer : PointerMachine.Hooks K Payload) (choices : AllocId → AddressRandomChoices)
    (base : Hooks K User Other) : Hooks K User Other :=
  {base with
    ptrGetAlloc := fun p => addressAction lens (PointerMachine.ptrGetAlloc pointer p 0)
    adjustRootPointer := fun id tag => addressAction lens
      (PointerMachine.adjustAllocRootPointer pointer id tag .ZERO .other (choices id))}

def callHooks (h : Hooks K User Other)
    (base : CallHooks Provenance (State K User) C MachineHooks.FrameExtra Other Extern FnABI ArgABI) :
    CallHooks Provenance (State K User) C MachineHooks.FrameExtra Other Extern FnABI ArgABI :=
  {base with getPtrFn := fun _ => getPtrFn h}

/-- Reuse actual allocation resolution for vtable/type-validity consumers.
The existing FullInstance-only VTable dictionary cannot represent machine extra
functions: retain that representation gap explicitly rather than classify UB. -/
def vtableHooks (h : Hooks K User Other)
    (base : VTableHooks Provenance (State K User) C CallInstance FnABI) :
    VTableHooks Provenance (State K User) C CallInstance FnABI :=
  {base with
    resolvePointer := fun _ pointer => do
      match pointer.intoPointerOrAddr with
      | .error _ => return .error .danglingInteger
      | .ok pointer =>
        match ← h.ptrGetAlloc pointer with
        | none => return .error .danglingInteger
        | some value => return .ok value
    globalFunction := fun _ id => do
      if (← registry h).extras.any (·.1 == id) then
        throw (.unsupported "FullInstance-only vtable dictionary cannot represent machine extra function")
      globalFunction h id }

def unwindHooks (h : Hooks K User Other) (base : Unwind.Hooks K User C Other) :
    Unwind.Hooks K User C Other :=
  {base with getPtrFn := fun _ => getPtrFn h}

def backtraceHooks (h : Hooks K User Other)
    (base : Backtrace.Hooks Provenance (State K User) D MD B I E Loc) :
    Backtrace.Hooks Provenance (State K User) D MD B I E Loc :=
  {base with
    functionPointer := fun callee => return (← functionPointer h (.Instance callee)).withOptionalProvenance
    allocation := allocation h
    globalFunction := globalFunction h}

def castHooks (h : Hooks K User Other)
    (base : CastHooks Provenance (State K User) C D) : CastHooks Provenance (State K User) C D :=
  {base with functionPointer := fun _ callee =>
    return (← functionPointer h (.Instance callee)).withOptionalProvenance}
end Miri.Interpreter.FunctionPointers
