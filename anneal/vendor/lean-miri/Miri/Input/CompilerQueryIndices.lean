import Miri.Input.RuntimeMetadata
import Miri.Input.CompilerExternAbi
import Miri.Input.CallResolution
import Miri.Input.Decoder
import Miri.Interpreter.FunctionCalls

/-! Preparation-time lookup indices for exact covariance and generated-call ABI
queries. The indices retain source row order and the first malformed global
row; consumers still decide query-specific matches and error precedence. -/
namespace Miri.Input.CompilerQueryIndices
open Lean Miri.ABI Miri.Interpreter

private def covarianceKey (source target : Nat) : String := s!"{source}:{target}"

structure CovarianceData where
  headerError : Option String := none
  firstRowError : Option (Nat × String) := none
  rows : Std.HashMap String (Array (Nat × Json)) := {}

private def buildCovariance (raw : Json) : CovarianceData := Id.run do
  let entries ← match do
      let table ← raw.getObjVal? "compiler_covariance_queries"
      table.getArr? with
    | .ok entries => pure entries
    | .error error => return { headerError := some error }
  let mut rows : Std.HashMap String (Array (Nat × Json)) := {}
  let mut firstRowError : Option (Nat × String) := none
  let mut index := 0
  while index < entries.size && firstRowError.isNone do
    let some entry := entries[index]? | return { headerError := some "covariance row index invariant" }
    let key ← match do
        let source ← (← entry.getObjVal? "source_type").getObjValAs? Nat "type_id"
        let target ← (← entry.getObjVal? "target_type").getObjValAs? Nat "type_id"
        pure (covarianceKey source target) with
      | .ok key => pure key
      | .error error =>
        firstRowError := some (index,error)
        index := index + 1
        continue
    rows := rows.insert key ((rows.getD key #[]).push (index,entry))
    index := index + 1
  return { firstRowError, rows }

structure Covariance (raw : Json) where
  private mk ::
  data : CovarianceData
  exact : data = buildCovariance raw

def covariance (raw : Json) : Covariance raw := ⟨buildCovariance raw, rfl⟩

private def functionType (runtime : RuntimeMetadata) (knownTypes : Std.HashSet Nat)
    (source : Json) : Except String Nat := do
  let id ← source.getObjValAs? Nat "type_id"
  unless knownTypes.contains id do
    let _ ← runtime.node id |>.mapError toString
  pure id

private def safetyKey : MIR.Safety → String
  | .Safe => "safe"
  | .Unsafe => "unsafe"

private def signatureKey (inputs : Array Nat) (output : Nat) (abi : ABI.ExternAbi)
    (safety : MIR.Safety) (cVariadic splatted : Bool) : String :=
  let encodedInputs := String.intercalate "," (inputs.toList.map toString)
  s!"{encodedInputs}|{output}|{reprStr abi}|{safetyKey safety}|{cVariadic}|{splatted}"

private def parseSignatureKey (runtime : RuntimeMetadata) (knownTypes : Std.HashSet Nat)
    (record : Json) : Except String String := do
  let typingEnv ← record.getObjValAs? String "typing_env"
  unless typingEnv == "fully_monomorphized" do
    throw "helper signature compiler typing environment mismatch"
  let signature ← record.getObjVal? "signature"
  let inputs ← (← (← signature.getObjVal? "inputs").getArr?).mapM (functionType runtime knownTypes)
  let output ← functionType runtime knownTypes (← signature.getObjVal? "output")
  let abi ← CompilerExternAbi.decode (← signature.getObjVal? "abi")
  let safety ← signature.getObjVal? "safety"
  unless (← safety.getObjValAs? String "status") == "supported" do
    throw "helper safety metadata unsupported"
  let safety ← match ← safety.getObjValAs? String "kind" with
    | "safe" => pure MIR.Safety.Safe
    | "unsafe" => pure MIR.Safety.Unsafe
    | _ => throw "unknown helper signature safety"
  let variadic ← signature.getObjValAs? Bool "c_variadic"
  let splatted ← record.getObjValAs? Bool "splatted"
  pure (signatureKey inputs output abi safety variadic splatted)

/-- A helper-signature row's raw query value and its demand-time ABI result.
The `Except`s retain malformed/unsupported row outcomes without making an
unused query fail during index construction. -/
structure SignatureAbiRow where
  index : Nat
  record : Json
  abiQuery : Except String Json
  parsedAbi : Except String (FnAbi MIR.TyId)

structure SignatureAbiData where
  headerError : Option String := none
  firstRowError : Option (Nat × String) := none
  rows : Std.HashMap String (Array SignatureAbiRow) := {}

private def parseSignatureAbiResult (runtime : RuntimeMetadata)
    (abiCache : Option (CallResolution.FunctionAbiCache runtime)) (result : Json) :
    Except String (FnAbi MIR.TyId) := do
  unless (← result.getObjValAs? String "status") == "supported" do
    throw s!"compiler dummy-signature ABI query failed: {result.compress}"
  CallResolution.functionAbiJson runtime (← result.getObjVal? "value") abiCache

private def buildSignatureAbi (runtime : RuntimeMetadata)
    (abiCache : Option (CallResolution.FunctionAbiCache runtime)) (raw : Json) : SignatureAbiData := Id.run do
  let records ← match do
      let facts ← raw.getObjVal? "compiler_function_facts"
      let signatures ← facts.getObjVal? "helper_signatures"
      signatures.getArr? with
    | .ok records => pure records
    | .error error => return { headerError := some error }
  let knownTypes := runtime.source.types.foldl (fun found node => found.insert node.id)
    ({} : Std.HashSet Nat)
  let mut rows : Std.HashMap String (Array SignatureAbiRow) := {}
  let mut firstRowError : Option (Nat × String) := none
  let mut index := 0
  while index < records.size && firstRowError.isNone do
    let some record := records[index]? | return { headerError := some "helper signature row index invariant" }
    match parseSignatureKey runtime knownTypes record with
    | .ok key =>
      let abiQuery := record.getObjVal? "abi_query"
      let parsedAbi := abiQuery.bind (parseSignatureAbiResult runtime abiCache)
      let row : SignatureAbiRow := ⟨index,record,abiQuery,parsedAbi⟩
      rows := rows.insert key ((rows.getD key #[]).push row)
    | .error error => firstRowError := some (index,error)
    index := index + 1
  return { firstRowError, rows }

structure SignatureAbi (runtime : RuntimeMetadata) (raw : Json) where
  private mk ::
  abiCache : Option (CallResolution.FunctionAbiCache runtime)
  data : SignatureAbiData
  exact : data = buildSignatureAbi runtime abiCache raw

def signatureAbi (runtime : RuntimeMetadata) (raw : Json)
    (abiCache : Option (CallResolution.FunctionAbiCache runtime) := none) : SignatureAbi runtime raw :=
  ⟨abiCache,buildSignatureAbi runtime abiCache raw,rfl⟩

def covarianceRows {raw : Json} (index : Covariance raw) (source target : Nat) : Array (Nat × Json) :=
  index.data.rows.getD (covarianceKey source target) #[]

def signatureRows {runtime : RuntimeMetadata} {raw : Json}
    (index : SignatureAbi runtime raw) (key : String) : Array (Nat × Json) :=
  (index.data.rows.getD key #[]).map fun row => (row.index,row.record)

/-- Internal query path selecting predecoded ABI outcomes while retaining each
source row's index and raw record for exact duplicate checks. -/
def signatureAbiRows {runtime : RuntimeMetadata} {raw : Json}
    (index : SignatureAbi runtime raw) (key : String) : Array SignatureAbiRow :=
  index.data.rows.getD key #[]

def signatureRequestKey (inputs : Array MIR.TyId) (output : MIR.TyId)
    (abi : ABI.ExternAbi) (safety : MIR.Safety) (cVariadic splatted : Bool) : String :=
  signatureKey inputs output abi safety cVariadic splatted

end Miri.Input.CompilerQueryIndices
