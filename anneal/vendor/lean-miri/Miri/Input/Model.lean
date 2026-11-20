import Miri.Input.DecoderValues

namespace Miri.Input

structure ImportDocumentCore where
  compilerPredicates : Array CompilerPredicateEvidence := #[]
  /-- Version tag for source physical ArgAbi layouts in FnAbi evidence. -/
  compilerAbiLayoutSchema : Option String := none
  producer : Producer
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  completenessStatus : PayloadStatus
  types : Array TypeNode
  allocations : Array AllocationNode
  compilerAllocIdWorld : Option CompilerAllocIdWorld := none
  instances : Array InstanceNode
  selectedScope : Option SelectedScope
  functionAbis : Array FunctionAbi
  bodies : Array Body
  obligations : Array Obligation
  raw : Lean.Json
  /-- Resolved source nodes from the mandatory shared-payload graph. Each node
  is retained once so downstream consumers can reuse the document's DAG. -/
  sharedNodes : Array Lean.Json := #[]
  /-- Checked import-time ABI queries; failures remain deferred until demand. -/
  compilerFunctionAbiTable : Option (CompilerFunctionAbiTable sharedNodes) := none
  compilerValueMemo : Option CompilerValueMemo := none

/-- Full diagnostic import retained for callers that inspect the typed JSON
projection. Runtime decoding uses `ImportDocumentCore` and does not retain this
duplicate tree. -/
structure ImportDocument where
  compilerPredicates : Array CompilerPredicateEvidence := #[]
  /-- Version tag for source physical ArgAbi layouts in FnAbi evidence. -/
  compilerAbiLayoutSchema : Option String := none
  producer : Producer
  runtimeTargetDataLayout : Option TargetDataLayoutEvidence := none
  completenessStatus : PayloadStatus
  types : Array TypeNode
  allocations : Array AllocationNode
  compilerAllocIdWorld : Option CompilerAllocIdWorld := none
  instances : Array InstanceNode
  selectedScope : Option SelectedScope
  functionAbis : Array FunctionAbi
  bodies : Array Body
  typedTree : TypedValue
  obligations : Array Obligation
  raw : Lean.Json
  /-- Resolved source nodes from the mandatory shared-payload graph. -/
  sharedNodes : Array Lean.Json := #[]

/-- Diagnostic/reflected imports contain schema data only. Their runtime view
uses the uncached compatibility path; the native runtime importer retains the
checked compiler projections directly in ImportDocumentCore. -/
def ImportDocument.toCore (document : ImportDocument) : ImportDocumentCore := {
  compilerPredicates := document.compilerPredicates
  compilerAbiLayoutSchema := document.compilerAbiLayoutSchema
  producer := document.producer
  runtimeTargetDataLayout := document.runtimeTargetDataLayout
  completenessStatus := document.completenessStatus
  types := document.types
  allocations := document.allocations
  compilerAllocIdWorld := document.compilerAllocIdWorld
  instances := document.instances
  selectedScope := document.selectedScope
  functionAbis := document.functionAbis
  bodies := document.bodies
  obligations := document.obligations
  raw := document.raw
  sharedNodes := document.sharedNodes
}

/-- Diagnostic clients may pass their full document to core-only consumers
without retaining the generic tree in the resulting runtime metadata. -/
instance : Coe ImportDocument ImportDocumentCore := ⟨ImportDocument.toCore⟩

def ImportDocumentCore.withTypedTree (core : ImportDocumentCore) (typedTree : TypedValue) : ImportDocument := {
  compilerPredicates := core.compilerPredicates
  compilerAbiLayoutSchema := core.compilerAbiLayoutSchema
  producer := core.producer
  runtimeTargetDataLayout := core.runtimeTargetDataLayout
  completenessStatus := core.completenessStatus
  types := core.types
  allocations := core.allocations
  compilerAllocIdWorld := core.compilerAllocIdWorld
  instances := core.instances
  selectedScope := core.selectedScope
  functionAbis := core.functionAbis
  bodies := core.bodies
  typedTree := typedTree
  obligations := core.obligations
  raw := core.raw
  sharedNodes := core.sharedNodes
}

/-- A structurally complete input accepted by the decoder.  This is still not
a semantic model or a proof of Miri equivalence. -/
structure ExecutionInput where
  document : ImportDocument

structure RuntimeExecutionInput where
  document : ImportDocumentCore

structure DecodeResult where
  document : ImportDocument
  executionInput : Option ExecutionInput
  /-- Exact obligations that make `executionInput` unavailable under the
  decoder's existing readiness predicate. This is diagnostic evidence only;
  it does not relax or otherwise define execution readiness. -/
  blockingObligations : Array Obligation := #[]

structure RuntimeDecodeResult where
  document : ImportDocumentCore
  executionInput : Option RuntimeExecutionInput
  blockingObligations : Array Obligation := #[]

end Miri.Input
