import Miri.Interpreter.ForeignItems
import Miri.Memory.Pointer

/-! Pinned shims/extern_static.rs and machine.rs::extern_static_pointer.
Every pointer is canonical strict Miri provenance; extra import indirection is
allocated and written rather than represented by a fabricated pointer. -/
namespace Miri.Interpreter.ExternStatic
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError
structure State where
  symbols : Array (String × StrictPointer) := #[]
  imports : Array (String × StrictPointer) := #[]
  missingWeak : Option StrictPointer := none
  deriving Repr
inductive InitialValue where | zeroByte | nullPointer deriving DecidableEq, Repr
structure InitHooks (S : Type) where
  get : M S State
  put : State → M S Unit
  unix : Bool
  os : String
  gnu : Bool

  environ : M S StrictPointer
  allocateValue : InitialValue → M S StrictPointer
  allocatePointerCell : StrictPointer → M S StrictPointer
  isDynSym : String → M S Bool
  functionPointer : String → M S StrictPointer
private def insert (entries : Array (String × StrictPointer)) (name : String)
    (pointer : StrictPointer) : Except StepError (Array (String × StrictPointer)) := do
  if entries.any (·.1 == name) then throw (.invalidProgram s!"duplicate extern static `{name}`")
  if pointer.provenance.getAllocId.isNone then throw (.invalidProgram "extern static has wildcard provenance")
  return entries.push (name,pointer)
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error

def add (h : InitHooks S) (name : String) (pointer : StrictPointer) : M S Unit := do
  let state ← h.get
  h.put { state with symbols := ← lift (insert state.symbols name pointer) }

def addWeak (h : InitHooks S) (name : String) (pointer : StrictPointer) : M S Unit := do
  let cell ← h.allocatePointerCell pointer
  let state ← h.get
  h.put { state with imports := ← lift (insert state.imports name cell) }

def weakFunctions (h : InitHooks S) (names : Array String) : M S Unit := do
  for name in names do
    if !(← h.isDynSym name) then throw (.invalidProgram s!"{name} is not a dynamic symbol")
    addWeak h name (← h.functionPointer name)

def initExternStatics (h : InitHooks S) : M S Unit := do
  if h.unix then
    let environ ← h.environ
    add h "environ" environ
    addWeak h "environ" environ
  if h.os == "linux" then
    weakFunctions h #["getrandom","gettid","statx","strlen"]
    if h.gnu then
      weakFunctions h #["__cxa_thread_atexit_impl"]
      let pointer ← h.allocateValue .zeroByte
      add h "__dso_handle" pointer
      addWeak h "__dso_handle" pointer
  else if h.os == "android" then
    weakFunctions h #["signal","getrandom","gettid","futimens","preadv","pwritev"]
  else if h.os == "windows" then
    add h "_tls_used" (← h.allocateValue .zeroByte)
  else if h.os == "illumos" || h.os == "solaris" then
    weakFunctions h #["pthread_setname_np"]
  let pointer ← h.allocateValue .nullPointer
  let state ← h.get
  h.put { state with missingWeak := some pointer }

inductive ImportLinkage where | none | externalWeak | other deriving DecidableEq, Repr
structure Declaration where
  symbol : String
  size : Size
  align : Align
  linkage : ImportLinkage
structure AllocationInfo where
  size : Size
  align : Align
structure ResolveHooks (S I : Type) where
  get : M S State
  declaration : DefId → M S Declaration
  pointerSize : Size
  checkSymbolClash : String → M S Unit
  allocationInfo : AllocId → M S AllocationInfo
  lookupStatic : String → M S (Option I)
  evalGlobal : I → M S StrictPointer
  declarationMutable : DefId → M S Bool
  allocationMutable : AllocId → M S Bool
private def concrete (pointer : StrictPointer) : M S AllocId :=
  match pointer.provenance.getAllocId with
  | some id => pure id
  | none => throw (.invalidProgram "extern static cannot contain wildcard provenance")
private def checkLayout (h : ResolveHooks S I) (decl : Declaration)
    (pointer : StrictPointer) : M S AllocId := do
  let id ← concrete pointer
  let info ← h.allocationInfo id
  if decl.size.bytes > info.size.bytes || decl.align.pow2 > info.align.pow2 then
    throw (.undefinedBehavior s!"extern static `{decl.symbol}` declaration exceeds backing size or alignment")
  return id

def resolve (h : ResolveHooks S I) (definition : DefId) : M S StrictPointer := do
  let decl ← h.declaration definition
  let state ← h.get
  let entries := if decl.linkage == .none then state.symbols else state.imports
  if let some (_,pointer) := entries.find? (·.1 == decl.symbol) then
    h.checkSymbolClash decl.symbol
    let _ ← checkLayout h decl pointer
    return pointer
  if decl.linkage == .externalWeak then
    if decl.size != h.pointerSize then throw (.invalidProgram "non-pointer-sized weak static")
    let some pointer := state.missingWeak | throw (.invalidProgram "missing weak symbol cell uninitialized")
    return pointer
  let some fnInstance ← h.lookupStatic decl.symbol
    | throw (.unsupported s!"extern static `{decl.symbol}` is not supported by Miri")
  let pointer ← h.evalGlobal fnInstance
  let id ← checkLayout h decl pointer
  let declaredMutable ← h.declarationMutable definition
  let backingMutable ← h.allocationMutable id
  if declaredMutable != backingMutable then
    throw (.undefinedBehavior "extern static declaration and backing mutability disagree")
  return pointer
def provenanceRoots (state : State) : Array StrictPointer :=
  state.symbols.map (·.2) ++ state.imports.map (·.2) ++
    (match state.missingWeak with | some pointer => #[pointer] | none => #[])
end Miri.Interpreter.ExternStatic
