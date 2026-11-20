import Miri.Input.AllocationImage
import Miri.Input.Decoder

/-! Actual compiler GlobalAlloc queries and shared definition identities.
Missing evidence is an error; initializer bytes do not establish declaration
mutability, foreignness or layout. -/
namespace Miri.Input.CompilerGlobals
open Miri.ABI Miri.Memory

def staticInfo (source : StaticAllocation) : Except String AllocationImage.StaticInfo := do
  let some info := source.globalInfo | throw "static global_info compiler queries are missing"
  unless info.status == .supported do throw "static global_info compiler query is unresolved"
  unless info.threadLocal == source.threadLocal do throw "static TLS predicates disagree"
  unless info.isStatic do throw "GlobalAlloc::Static lacks compiler is_static evidence"
  let size ← (RuntimeMetadata.size info.sizeBytes).mapError toString
  let align ← (RuntimeMetadata.alignment info.alignBytes).mapError toString
  let mutable ← match info.mutability with
    | .mutable => pure Mutability.Mut
    | .immutable => pure Mutability.Not
    | .unknown tag => throw s!"unknown compiler static mutability {tag}"
  pure ⟨size, align, mutable, info.isStatic, info.foreignItem⟩

def queries : AllocationImage.Queries := ⟨staticInfo⟩

/-- Append graph identities without changing any existing dense ID. Every body
uses the final shared table, including statics with no selected MIR root. -/
def prepareProgram (program : LoweredProgram) : LoweredProgram := Id.run do
  let mut definitions := program.bundle.definitions
  for node in program.input.allocations do
    let id := match node.data with
      | some (.static source) => some source.definitionId
      | some (.function source) => some source.definitionId
      | _ => none
    if let some id := id then
      unless definitions.contains id do definitions := definitions.push id
  let bodies := program.bundle.bodies.map fun body => { body with definitions := definitions }
  return { program with bundle := { program.bundle with bodies := bodies, definitions := definitions } }

def importGraph [DecidableEq K] (target : RuntimeTargetDataLayout)
    (program : LoweredProgram) (initial : MemoryState P E K) : AllocationImage.ImportResult P E K :=
  let program := prepareProgram program
  AllocationImage.importGraph target program.bundle.definitions queries program.input.allocations initial

end Miri.Input.CompilerGlobals
