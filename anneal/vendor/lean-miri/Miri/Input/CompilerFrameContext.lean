import Miri.Input.CompilerProviders
import Miri.Input.NormalizationBody
import Miri.Interpreter.AllocationDriver

/-! Canonical stack.rs frame/local/instruction queries. The body index is the
identity key; body contents only check consistency. Local layouts consume exact
full-instance body-normalization evidence, never template type substitution. -/
namespace Miri.Input.CompilerFrameContext
open Lean Miri.ABI Miri.Memory Miri.Interpreter
abbrev ActualFrame := Frame Provenance LocalLayout MachineHooks.FrameExtra
private def lift (query : Except String A) : MachineHooks.M K User A :=
  match query with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler frame query: {error}")

/-- Resolve by canonical identity and validate the complete instance/body pair.
Structural equality is an assertion, not a body-selection algorithm. -/
def bodyOfFrame (p : CompilerProviders.Prepared) (frame : ActualFrame) :
    Except String LoweredBody := do
  let some body := p.program.bundle.bodies[frame.bodyIdentity.index]?
    | throw "canonical body identity is absent"
  unless body.body == frame.body do throw "canonical body/content mismatch"
  let loaded ← CallResolution.loadedBodyOfInstance p.lifecycle.calls.calls frame.functionInstance
  unless loaded.identity == frame.bodyIdentity do throw "full-instance/canonical body identity mismatch"
  pure body

def currentBody (p : CompilerProviders.Prepared) : MachineHooks.M K User LoweredBody := do
  lift (bodyOfFrame p (← MachineHooks.currentFrame))

def normalizedBody (p : CompilerProviders.Prepared) (frame : ActualFrame) :
    Except String Json := do
  let body ← bodyOfFrame p frame
  let some lifecycle := p.lifecycle.lifecycle.entries[frame.bodyIdentity.index]?
    | throw "canonical body compiler context is absent"
  unless (← lifecycle.callee) == frame.functionInstance do
    throw "body normalization belongs to another full instance"
  let context ← body.input.payload.getObjVal? "constant_query_context"
  let normalized ← context.getObjVal? "normalization"
  NormalizationBody.resolve normalized body.input.payload

/-- The recorded normalization ran rustc's instantiate-MIR-and-normalize query
with this exact full instance and body's typing environment. -/
def normalizedLocalType (p : CompilerProviders.Prepared) (frame : ActualFrame)
    (id : MIR.LocalId) : Except String MIR.TyId := do
  let body ← bodyOfFrame p frame
  let some source := body.input.locals[id]? | throw "source local is absent"
  unless source.id == id do throw "source local index mismatch"
  let locals ← (← (← normalizedBody p frame).getObjVal? "locals").getArr?
  unless locals.size == body.input.locals.size do throw "body normalization changed local count"
  let some decl := locals[id]? | throw "normalized local is absent"
  unless (← decl.getObjValAs? Nat "local") == id do throw "normalized local index mismatch"
  (← decl.getObjVal? "type").getObjValAs? Nat "type_id"

/-- Source step.rs Cast target normalization at the exact current statement.
The requested original type must be the actual Cast target. No type-ID-only
substitution table is shared across distinct full instantiations. -/
def normalizeCastTarget (p : CompilerProviders.Prepared) (requested : MIR.TyId) :
    MachineHooks.M K User MIR.TyId := do
  let frame ← MachineHooks.currentFrame
  let .mir location := frame.location | throw .expectedMirLocation
  let body ← lift (bodyOfFrame p frame)
  let some block := body.body.basicBlocks[location.block]?
    | throw (.stack (.invalidLocation location))
  let some statement := block.statements[location.statementIndex]?
    | throw (.invalidProgram "cast normalization outside a source statement")
  let .Assign _ (.Cast _ _ original) := statement.kind
    | throw (.invalidProgram "cast normalization outside the source Cast rvalue")
  unless requested == original do throw (.invalidProgram "cast normalization requested another source type")
  lift do
    let normalized ← normalizedBody p frame
    let blocks ← (← normalized.getObjVal? "basic_blocks").getArr?
    let some normalizedBlock := blocks[location.block]? | throw "normalized source block absent"
    unless (← normalizedBlock.getObjValAs? Nat "block") == location.block do
      throw "normalized source block index mismatch"
    let statements ← (← normalizedBlock.getObjVal? "statements").getArr?
    let some statement := statements[location.statementIndex]? | throw "normalized source statement absent"
    let kind ← statement.getObjVal? "kind"
    unless (← kind.getObjValAs? String "variant") == "Assign" do throw "normalization changed statement kind"
    let rvalue ← kind.getObjVal? "rvalue"
    unless (← rvalue.getObjValAs? String "kind") == "Cast" do throw "normalization changed Cast rvalue"
    (← rvalue.getObjVal? "target_type").getObjValAs? Nat "type_id"

/-- The uncached compiler leaf used by the canonical local-layout cache. -/
def computeLocalLayout (p : CompilerProviders.Prepared) (id : MIR.LocalId) :
    MachineHooks.M K User LocalLayout := do
  let frame ← MachineHooks.currentFrame
  let ty ← lift (normalizedLocalType p frame id)
  lift ((p.runtime.lookup ty).mapError toString)

/-- Complete source layout_of_local for the actual current frame: a cached
layout bypasses normalization; debug compatibility runs before cache mutation. -/
def layoutOfLocal (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (compatible : LocalLayout → LocalLayout → Except StepError Bool)
    (id : MIR.LocalId) (known : Option LocalLayout) : MachineHooks.M K User LocalLayout := do
  let frame ← MachineHooks.currentFrame
  let slot ← match frame.getLocal id with
    | .ok slot => pure slot
    | .error error => throw (.stack error)
  if let some cached := slot.layout then return cached
  let layout ← match known with
    | none => computeLocalLayout p id
    | some known => do
      if debugAssertions then
        let computed ← computeLocalLayout p id
        let same ← match compatible computed known with
          | .ok same => pure same
          | .error error => throw error
        unless same do throw (.invalidProgram "known local layout differs from compiler layout")
      pure known
  let frame ← MachineHooks.currentFrame
  let (frame,layout) ← match frame.getOrCacheLocalLayout id layout with
    | .ok result => pure result
    | .error error => throw (.stack error)
  MachineHooks.setCurrentFrame frame
  pure layout

/-- The passed body is checked against the current identity, never searched. -/
def localSpan (p : CompilerProviders.Prepared) (supplied : MIR.Body) (id : MIR.LocalId) :
    MachineHooks.M K User MIR.SpanRef := do
  let frame ← MachineHooks.currentFrame
  unless supplied == frame.body do throw (.invalidProgram "local span body differs from active frame")
  let body ← lift (bodyOfFrame p frame)
  let some decl := body.input.locals[id]? | throw (.invalidProgram "local source span index is absent")
  match p.program.bundle.spans.toList.idxOf? decl.sourceInfo.span with
  | some index => pure ⟨index⟩
  | none => throw (.unsupported "exact local source span is absent from canonical span table")

/-- Return the actual existing MIR node; no second executable instruction IR. -/
def instruction (p : CompilerProviders.Prepared) :
    MachineHooks.M K User (Option (Sum MIR.Statement MIR.Terminator)) := do
  let frame ← MachineHooks.currentFrame
  let _ ← lift (bodyOfFrame p frame)
  match frame.location with
  | .unwinding _ => pure none
  | .mir location =>
    let some block := frame.body.basicBlocks[location.block]?
      | throw (.stack (.invalidLocation location))
    if let some statement := block.statements[location.statementIndex]? then return some (.inl statement)
    if location.statementIndex == block.statements.size then return some (.inr block.terminator)
    throw (.stack (.invalidLocation location))

def sourceInfo (p : CompilerProviders.Prepared) : MachineHooks.M K User (Option MIR.SourceInfo) := do
  match ← instruction p with
  | none => pure none
  | some (.inl statement) => pure (some statement.sourceInfo)
  | some (.inr terminator) => pure (some terminator.sourceInfo)

def currentSpan (p : CompilerProviders.Prepared) : MachineHooks.M K User MIR.SpanRef := do
  let frame ← MachineHooks.currentFrame
  let _ ← lift (bodyOfFrame p frame)
  match AllocationDriver.frameSpan frame with
  | .ok span => pure span
  | .error error => throw error

/-- Source InterpCx::cur_span retains the actual enclosing compiler span for
an empty stack. The caller supplies that source context; no dummy is invented. -/
def curSpan (p : CompilerProviders.Prepared) (contextSpan : MIR.SpanRef) :
    MachineHooks.M K User MIR.SpanRef := do
  if (← get).stack.frames.isEmpty then return contextSpan
  currentSpan p

/-- Remaining capabilities after source-owned local layout/span queries are
removed. These concern typed operations, validation and compiler predicates. -/
structure CompilerLeaves (K User C : Type) where
  debugAssertions : Bool
  validationInProgress : MachineHooks.M K User Bool
  projection : C → MachineHooks.M K User (ProjectionCx Provenance)
  deref : C → RuntimePlace Provenance → Bool → MachineHooks.M K User (RuntimePlace Provenance)
  checkPlaceType : C → MIR.Place → RuntimePlace Provenance → MachineHooks.M K User Unit
  memoryOffset : C → MemPlace Provenance → Size → OffsetMode → MemPlaceMeta Provenance → MachineHooks.M K User (MemPlace Provenance)
  debugAbiCheck : Immediate Provenance → LocalLayout → MachineHooks.M K User Unit
  enforceValidity : C → LocalLayout → MachineHooks.M K User Bool
  validate : C → RuntimePlace Provenance → MachineHooks.M K User Unit
  willValidateMemory : MemoryOperandLayout → Bool

def compilerFromLeaves (p : CompilerProviders.Prepared) (h : CompilerLeaves K User C) :
    PlaceMachine.CompilerHooks K User C :=
  {debugAssertions := h.debugAssertions
   layout := fun _ id => computeLocalLayout p id
   localSpan := localSpan p
   validationInProgress := h.validationInProgress
   projection := h.projection
   deref := h.deref
   checkPlaceType := h.checkPlaceType
   memoryOffset := h.memoryOffset
   debugAbiCheck := h.debugAbiCheck
   enforceValidity := h.enforceValidity
   validate := h.validate
   willValidateMemory := h.willValidateMemory}

def compilerHooks (p : CompilerProviders.Prepared) (base : PlaceMachine.CompilerHooks K User C) :
    PlaceMachine.CompilerHooks K User C :=
  {base with layout := fun _ id => computeLocalLayout p id, localSpan := localSpan p}

/-- Only TLS resolution remains a capability of the rvalue leaf record. -/
def rvalueLeaves (p : CompilerProviders.Prepared)
    (threadLocalPointer : C → MIR.DefId → MachineHooks.M K User (Pointer (Option Provenance))) :
    ExecutionLeaves.Rvalue (MachineHooks.State K User) C :=
  ⟨threadLocalPointer,fun _ ty => normalizeCastTarget p ty⟩

/-- Close canonical frame access and local compiler leaves in the same config.
The existing operational dictionaries retain physical/validation capabilities. -/
def executionHooks (p : CompilerProviders.Prepared)
    (base : ExecutionMachine.Config K User C Other Extern Host) :
    ExecutionMachine.Config K User C Other Extern Host :=
  {base with
    compiler := compilerHooks p base.compiler
    rvalues := {base.rvalues with normalize := fun _ ty => normalizeCastTarget p ty}}
end Miri.Input.CompilerFrameContext

namespace Miri.Input.CompilerFrameContext
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
variable {K U : Type}
 theorem localSpan_known (p : CompilerProviders.Prepared) (body : LoadedBody) (actual : LoweredBody)
    (fnInstance : CallInstance) (decl : LocalDecl) (span : SpanRef)
    (row : p.program.bundle.bodies[body.identity.index]? = some actual)
    (contents : actual.body = body.body)
    (loader : CallResolution.loadedBodyOfInstance p.lifecycle.calls.calls fnInstance = .ok body)
    (declaration : actual.input.locals[0]? = some decl)
    (indexed : p.program.bundle.spans.toList.idxOf? decl.sourceInfo.span = some span.id)
    (frames : Array ActualFrame) (frame : ActualFrame) (machine : MachineHooks.MachineState K U)
    (identity : frame.bodyIdentity = body.identity) (function : frame.functionInstance = fnInstance)
    (frameBody : frame.body = body.body) :
    localSpan p body.body 0 (⟨⟨frames.push frame⟩,machine⟩ : MachineHooks.State K U) =
      .ok span ⟨⟨frames.push frame⟩,machine⟩ := by
  simp [localSpan,MachineHooks.currentFrame,Stack.currentFrame?,bodyOfFrame,lift,
    row,contents,loader,declaration,indexed,identity,function,frameBody,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,Except.bind,Except.pure]
end Miri.Input.CompilerFrameContext
