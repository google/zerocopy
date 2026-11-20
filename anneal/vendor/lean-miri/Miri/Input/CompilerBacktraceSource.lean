import Miri.Input.CompilerInstance
import Miri.Interpreter.Backtrace
import Miri.Interpreter.BacktraceMachine

/-! Compiler hygiene/source-map/rendering evidence, with exact body/span keys.
An unseen forged BytePos remains unresolved; no nearby-position approximation. -/
namespace Miri.Input.CompilerBacktraceSource
open Lean Miri.Interpreter
structure Position where
  bytePosition : UInt32
  line : Nat
  column : Nat
  filename : String
  deriving DecidableEq
structure SpanEntry where
  span : MIR.SpanRef
  position : Position
structure Prepared where
  program : LoweredProgram
  bodySpans : Array (Except String (Array SpanEntry))
  positions : Array Position
  names : Array (CallInstance × String)

private def natural (j : Json) (key : String) : Except String Nat := do
  (← j.getObjVal? key).getNat?
private def position (j : Json) : Except String Position := do
  let offset ← natural j "byte_position"
  unless offset < 2^32 do throw "compiler BytePos exceeds u32"
  return ⟨UInt32.ofNat offset,← natural j "line",← natural j "zero_based_char_column",
    ← (← j.getObjVal? "filename").getStr?⟩
private def spans (ctx : LowerContext) (interner : CompilerSpanInterner) (payload : Json) :
    Except String (Array SpanEntry × CompilerSpanInterner) := do
  let records ← (← payload.getObjVal? "backtrace_spans").getArr?
  let mut interner := interner
  let mut entries := #[]
  for record in records do
    let (span,next) ← lowerCompilerSpanWithInterner interner
      (← ctx.decodeCompilerValue (← record.getObjVal? "span"))
    interner := next
    let location ← position (← record.getObjVal? "source_position")
    unless (← natural record "collapsed_lo") == location.bytePosition.toNat do
      throw "collapsed hygiene BytePos/source-map position mismatch"
    if let some old := entries.find? (fun entry : SpanEntry => entry.span == span) then
      unless old.position == location do throw "conflicting body/span hygiene query"
    else entries := entries.push ⟨span,location⟩
  return (entries,interner)

def prepare (program : LoweredProgram) : Except String Prepared := do
  let ctx := LowerContext.ofDocument program.input
  let mut interner := CompilerSpanInterner.ofTables program.compilerTables
  let mut bodySpans := #[]
  let mut positions := #[]
  let mut positionIndex : Std.HashMap UInt32 Position := {}
  for body in program.bundle.bodies do
    match spans ctx interner body.input.payload with
    | .error error => bodySpans := bodySpans.push (.error error)
    | .ok (entries,next) =>
      interner := next
      bodySpans := bodySpans.push (.ok entries)
      for entry in entries do
        if let some old := positionIndex.get? entry.position.bytePosition then
          unless old == entry.position do throw "conflicting exact source-map query"
        else
          positionIndex := positionIndex.insert entry.position.bytePosition entry.position
          positions := positions.push entry.position
  let ctx := LowerContext.ofDocument program.input
  let records ← (← (← program.input.raw.getObjVal? "compiler_runtime_queries").getObjVal? "instances").getArr?
  let mut names := #[]
  let mut namesByDefinition : Std.HashMap Nat (Array Nat) := {}
  let mut tables := interner.getTables
  for record in records do
    let (callee,next) ← CompilerInstance.decode ctx tables record
    tables := next
    let name ← (← record.getObjVal? "display").getStr?
    let candidates := namesByDefinition.getD callee.defId #[]
    if let some index := candidates.find? fun index =>
        match names[index]? with
        | some (oldCallee,_) => oldCallee == callee
        | none => false then
      let some (_,old) := names[index]? | throw "compiler full-instance bucket index invariant"
      unless old == name do throw "conflicting compiler full-instance rendering"
    else
      let index := names.size
      names := names.push (callee,name)
      namesByDefinition := namesByDefinition.insert callee.defId (candidates.push index)
  return ⟨program.withCompilerTables tables,bodySpans,positions,names⟩

private def lift (result : Except String A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler backtrace source: {error}")

/-- Compiler-source construction with only runtime global/pointer queries.
Every hygiene/source-map/name result is selected by its exact exported key. -/
def source (p : Prepared) (hostUsizeMax : Nat)
    (unitPointerLayout : EStateM StepError S LocalLayout)
    (misaligned : Memory.Pointer (Option Memory.Provenance) → ABI.Align → EStateM StepError S (Option Memory.Misalignment))
    (functionPointer : CallInstance → EStateM StepError S (Memory.Pointer (Option Memory.Provenance)))
    (allocation : Memory.Pointer (Option Memory.Provenance) → EStateM StepError S (Memory.AllocId × ABI.Size))
    (globalFunction : Memory.AllocId → EStateM StepError S (Option CallInstance)) :
    BacktraceMachine.Sources S Position := {
  hostUsizeMax,unitPointerLayout,misaligned,functionPointer,allocation,globalFunction
  collapsedSpanLo := fun identity span => lift do
    let some records := p.bodySpans[identity.index]? | throw "canonical backtrace body identity absent"
    let entries ← records
    let some entry := entries.find? (·.span == span) | throw "exact body/span hygiene query absent"
    return entry.position.bytePosition
  lookupCharPos := fun offset => lift do
    let some location := p.positions.find? (·.bytePosition == offset)
      | throw "unseen BytePos needs actual compiler source-map query"
    return location
  line := Position.line
  column := Position.column
  renderInstance := fun callee => lift do
    let some (_,name) := p.names.find? (·.1 == callee) | throw "exact full-instance rendering absent"
    return name
  remappedFilename := fun location => pure location.filename }

def hooks (p : Prepared) (base : Backtrace.Hooks P S D MD B I E Position) :
    Backtrace.Hooks P S D MD B I E Position :=
  {base with
    collapsedSpanLo := fun identity span => lift do
      let some records := p.bodySpans[identity.index]? | throw "canonical backtrace body identity absent"
      let entries ← records
      let some entry := entries.find? (·.span == span) | throw "exact body/span hygiene query absent"
      return entry.position.bytePosition
    lookupCharPos := fun offset => lift do
      let some location := p.positions.find? (·.bytePosition == offset)
        | throw "unseen BytePos needs actual compiler source-map query"
      return location
    line := Position.line
    column := Position.column
    renderInstance := fun callee => lift do
      let some (_,name) := p.names.find? (·.1 == callee) | throw "exact full-instance rendering absent"
      return name
    remappedFilename := fun location => pure location.filename }
end Miri.Input.CompilerBacktraceSource
