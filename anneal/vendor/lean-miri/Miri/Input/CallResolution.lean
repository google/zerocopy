import Miri.Input.CompilerInstance
import Miri.Input.CallCompatibility
import Miri.ABI.FnAbi
import Miri.Interpreter.Call

/-! Internal reuse of actual rustc instance-resolution and FnAbi query results.
Complete instance arguments and shared definition/type-constant tables are kept.
Missing/ambiguous/conflicting queries remain errors. This is not a compiler
instance solver or Miri's foreign-function/shim dispatcher. -/
namespace Miri.Input.CallResolution
open Lean Miri.ABI Miri.Interpreter
abbrev Result := Except String
private def require (value : Option A) (message : String) : Result A :=
  match value with | some value => pure value | none => throw message
private def field (j : Json) (name : String) : Result Json := j.getObjVal? name
private def text (j : Json) (name : String) : Result String := do (← field j name).getStr?
private def natural (j : Json) (name : String) : Result Nat := do (← field j name).getNat?

def convention (source : CanonicalAbi) : Result CanonAbi := do
  if source.status != .supported then throw "calling-convention query is unsupported"
  match source.kind with
  | .c => pure .C | .rust => pure .Rust | .rustCold => pure .RustCold
  | .rustPreserveNone => pure .RustPreserveNone | .rustTail => pure .RustTail
  | .custom => pure .Custom | .swift => pure .Swift | .gpuKernel => pure .GpuKernel
  | .arm =>
    let call ← require source.armCall "missing Arm calling convention"
    return .Arm (← match call with
      | .aapcs => pure ArmCall.Aapcs | .cmseNonSecureCall => pure .CCmseNonSecureCall
      | .cmseNonSecureEntry => pure .CCmseNonSecureEntry | .unknown _ => throw "unknown Arm convention")
  | .interrupt =>
    let kind ← require source.interruptKind "missing interrupt calling convention"
    return .Interrupt (← match kind with
      | .avr => pure InterruptKind.Avr | .avrNonBlocking => pure .AvrNonBlocking
      | .msp430 => pure .Msp430 | .riscvMachine => pure .RiscvMachine
      | .riscvSupervisor => pure .RiscvSupervisor | .x86 => pure .X86
      | .unknown _ => throw "unknown interrupt convention")
  | .x86 =>
    let call ← require source.x86Call "missing x86 calling convention"
    return .X86 (← match call with
      | .fastcall => pure X86Call.Fastcall | .stdcall => pure .Stdcall | .sysv64 => pure .SysV64
      | .thiscall => pure .Thiscall | .vectorcall => pure .Vectorcall | .win64 => pure .Win64
      | .unknown _ => throw "unknown x86 convention")
  | .unknown _ => throw "unknown canonical ABI"

def functionAbi (runtime : RuntimeMetadata) (source : FunctionAbi) : Result (FnAbi TypeId) := do
  let args ← source.arguments.mapM fun argument => (CallCompatibility.argument runtime argument).mapError toString
  let ret ← (CallCompatibility.argument runtime source.returnValue).mapError toString
  if source.fixedCount >= 2^32 then throw "FnAbi.fixed_count exceeds u32"
  if source.fixedCount > args.size then throw "FnAbi.fixed_count exceeds actual arguments"
  -- rustc's physical `FnAbi.args` can include the compiler-injected caller
  -- location while `fixed_count` counts only explicit source arguments.
  -- Preserve both exact facts here; demanded call initialization validates
  -- their relationship against the exact `requires_caller_location` query.
  return ⟨args,ret,source.cVariadic,UInt32.ofNat source.fixedCount,← convention source.callingConvention,source.canUnwind⟩

/-- Decode and convert a raw compiler FnAbi through the runtime's shared
preparation cache. Before cache preparation (and for manually constructed
metadata), retain the direct decoder/converter path. -/
private def decodeFunctionAbiJson (raw : Json) : Result FunctionAbi :=
  decodeCompilerFunctionAbi raw

private def decodeFunctionAbiJsonWithMemo (raw : Json)
    (memo : CompilerFunctionAbiMemo) : Result FunctionAbi :=
  decodeCompilerFunctionAbiWithMemo raw memo

private def isFunctionAbiCandidate (raw : Json) : Bool :=
  ["arguments", "return", "calling_convention", "can_unwind", "c_variadic", "fixed_count"]
    |>.all fun key => (raw.getObjVal? key).isOk

/-- Prepare one immutable runtime cache from the decoded shared-payload graph.
Only nodes with the complete FnAbi envelope are candidates; malformed candidates
retain their failed decode/conversion outcome and cannot fail unused metadata. -/
private def buildFunctionAbiCache (runtime : RuntimeMetadata) :
    Std.HashMap Json (Except String (FnAbi TypeId)) := Id.run do
  let mut entries : Std.HashMap Json (Except String (FnAbi TypeId)) := {}
  match runtime.source.compilerFunctionAbiTable with
  | some typed =>
    for (raw, decoded) in typed.entries do
      if !(entries.contains raw) then
        entries := entries.insert raw (decoded >>= functionAbi runtime)
  | none =>
    let abiMemo := prepareCompilerFunctionAbiMemo runtime.source.sharedNodes
    for raw in runtime.source.sharedNodes do
      if isFunctionAbiCandidate raw && !(entries.contains raw) then
        let result := do
          functionAbi runtime (← decodeFunctionAbiJsonWithMemo raw abiMemo)
        entries := entries.insert raw result
  return entries

/-- Immutable conversion memo tied to the exact runtime value and its exact
shared-graph inputs. Its sole constructor proves the entries equal a fresh
build, so callers cannot install fabricated ABI results. -/
structure FunctionAbiCache (runtime : RuntimeMetadata) where
  private mk ::
  private entries : Std.HashMap Json (Except String (FnAbi TypeId))
  private exact : entries = buildFunctionAbiCache runtime

/-- Prepare the memo for all shared-graph FnAbi candidates in this runtime. -/
def prepareFunctionAbiCacheProfiled (profile : Lean.Options) (runtime : RuntimeMetadata) :
    FunctionAbiCache runtime :=
  ⟨profileit "prepare.function_abi_cache" profile fun _ => buildFunctionAbiCache runtime, rfl⟩

/-- Prepare the memo for all shared-graph FnAbi candidates in this runtime. -/
def prepareFunctionAbiCache (runtime : RuntimeMetadata) : FunctionAbiCache runtime :=
  prepareFunctionAbiCacheProfiled {} runtime

/-- Decode and convert a raw compiler FnAbi through the checked shared cache.
Without a cache, retain the direct decoder/converter path for manually
constructed runtime contexts. -/
def functionAbiJson (runtime : RuntimeMetadata) (raw : Json)
    (cache : Option (FunctionAbiCache runtime) := none) : Result (FnAbi TypeId) := do
  match cache with
  | some cache =>
    match cache.entries[raw]? with
    | some result => result
    | none => functionAbi runtime (← decodeFunctionAbiJson raw)
  | none => functionAbi runtime (← decodeFunctionAbiJson raw)

structure Site where
  bodyIndex : Nat
  block : MIR.BasicBlockId
  deriving DecidableEq, Repr
structure Resolution where
  callee : CallInstance
  sourceInstanceId : InstanceId
  function : MIR.Operand
  abi : Except String (FnAbi TypeId)
  source : Json
structure Entry where
  site : Site
  outcome : Except String Resolution
structure InstanceBody where
  fnInstance : CallInstance
  sourceInstanceId : InstanceId
  bodyIndex : Nat
structure Indirect where
  site : Site
  function : MIR.Operand
  functionType : MIR.TyId
  abi : FnAbi TypeId
  source : Json
structure Prepared where
  program : LoweredProgram
  runtime : RuntimeMetadata
  functionAbiCache : FunctionAbiCache runtime
  /-- Strict source unit-layout scan cached as a deferred outcome for ABI
  compatibility calls. Manual records retain the linear compatibility path. -/
  unitLayoutCache : Option (CallCompatibility.UnitLayoutCache runtime) := none
  sourceEquality : RuntimeMetadata.JsonReflexivity runtime.source.raw
  entries : Array Entry
  bodies : Array InstanceBody
  obligations : Array Obligation
  indirect : Array Indirect := #[]

/-- Preserve first-match lookup, including the linear fallback for malformed
manual JSON whose equality/hash behavior is not canonical. Build this once,
instead of scanning every typed ABI for every call site. -/
private def typedFunctionAbiIndex (values : Array FunctionAbi) : Option (Std.HashMap Json FunctionAbi) := Id.run do
  let mut entries := {}
  for value in values do
    if !DecoderValues.hasCanonicalJsonObjectKeys value.payload then return none
    if !entries.contains value.payload then entries := entries.insert value.payload value
  return some entries

private def findTypedFunctionAbi (values : Array FunctionAbi)
    (index : Option (Std.HashMap Json FunctionAbi)) (raw : Json) : Option FunctionAbi :=
  match index with
  | some entries =>
    if DecoderValues.hasCanonicalJsonObjectKeys raw then entries[raw]?
    else values.find? (·.payload == raw)
  | none => values.find? (·.payload == raw)

private def decodeResolution (runtime : RuntimeMetadata) (ctx : LowerContext)
    (abiCache : FunctionAbiCache runtime) (typedAbis : Option (Std.HashMap Json FunctionAbi))
    (tables : CompilerTables)
    (function : MIR.Operand) (source : Json) :
    Result (Resolution × CompilerTables) := do
  let status ← text source "status"
  let kind ← text source "kind"
  let virtual := kind == "virtual_dispatch"
  unless kind == "resolved_instance" || virtual do throw "callee is not a compiler instance dispatch"
  unless status == "supported" || (virtual && status == "unknown") do
    throw "compiler callee resolution is unavailable"
  let (callee,tables) ← CompilerInstance.decode ctx tables source
  match callee.kind with
  | .Virtual _ slot =>
    unless virtual do throw "virtual instance lacks virtual-dispatch query tag"
    unless (← natural source "dispatch_slot") == slot do throw "virtual dispatch slot/instance mismatch"
  | _ => unless !virtual do throw "virtual dispatch query did not return a Virtual instance"
  let sourceInstanceId ← natural source "instance_id"
  let sourceAbi ← field source "fn_abi"
  let sourceAbi ← require (findTypedFunctionAbi runtime.source.functionAbis typedAbis sourceAbi) "missing typed compiler FnAbi record"
  return (⟨callee,sourceInstanceId,function,
    functionAbiJson runtime sourceAbi.payload (some abiCache),source⟩,tables)

/-- Appended identities are rebound through all bodies; existing IDs never move.
Query failures are retained per call site, without deleting the imported MIR. -/
private def prepareUsingRuntime (profile : Lean.Options) (program : LoweredProgram) (runtime : RuntimeMetadata)
    (sourceEquality : RuntimeMetadata.JsonReflexivity runtime.source.raw) :
    Result Prepared := do
  let functionAbiCache := prepareFunctionAbiCacheProfiled profile runtime
  let typedAbis := profileit "prepare.typed_abi_index" profile fun _ => typedFunctionAbiIndex runtime.source.functionAbis
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut bodies := #[]
  let mut obligations := #[]
  for (sourceId,index) in program.instances do
    let source ← require (program.input.instances.find? (·.id == sourceId)) "missing source instance record"
    match CompilerInstance.decode ctx tables source.payload with
    | .error message => obligations := obligations.push ⟨s!"instance[{sourceId}]",message⟩
    | .ok (fnInstance,next) =>
      tables := next
      bodies := bodies.push ⟨fnInstance,sourceId,index⟩
  let mut entries := #[]
  let mut indirect := #[]
  for (body,index) in program.bundle.bodies.toList.zipIdx do
    let blocks ← (← field body.input.payload "basic_blocks").getArr?
    for (block,blockIndex) in body.body.basicBlocks.toList.zipIdx do
      let function ← match block.terminator.kind with
        | .Call function .. | .TailCall function .. => pure (some function)
        | _ => pure none
      if let some function := function then
        let sourceBlock ← require blocks[blockIndex]? "missing source block"
        let sourceResolution ← field sourceBlock "terminator" >>= fun term => field term "kind" >>= fun kind => field kind "resolution"
        if (text sourceResolution "kind").toOption == some "indirect_function_pointer" then
          let result := do
            unless (← text sourceResolution "status") == "supported" do throw "indirect compiler signature/ABI query is unavailable"
            let sourceType ← field sourceResolution "function_type"
            let typeId ← natural sourceType "type_id"
            let sourceType ← require (program.input.types.find? (fun (node : TypeNode) => node.id == typeId)) "indirect function type is missing"
            unless sourceType.shapeKind == TypeShapeKind.functionPointer do throw "indirect dispatch metadata is not a function-pointer type"
            pure (typeId,← functionAbiJson runtime (← field sourceResolution "fn_abi")
              (some functionAbiCache))
          match result with
          | .error message =>
            obligations := obligations.push ⟨s!"body[{index}].block[{blockIndex}].indirect",message⟩
            entries := entries.push ⟨⟨index,blockIndex⟩,.error message⟩
          | .ok (ty,abi) =>
            indirect := indirect.push ⟨⟨index,blockIndex⟩,function,ty,abi,sourceResolution⟩
          continue
        let result := do
          let block ← require blocks[blockIndex]? "missing source block"
          let source ← field block "terminator" >>= fun term => field term "kind" >>= fun kind => field kind "resolution"
          decodeResolution runtime ctx functionAbiCache typedAbis tables function source
        let outcome ← match result with
          | .error message =>
            obligations := obligations.push ⟨s!"body[{index}].block[{blockIndex}].resolution",message⟩
            pure (.error message)
          | .ok (resolution,next) =>
            tables := next
            if let .error message := resolution.abi then
              obligations := obligations.push ⟨s!"body[{index}].block[{blockIndex}].fn_abi",message⟩
            pure (.ok resolution)
        entries := entries.push ⟨⟨index,blockIndex⟩,outcome⟩
  return {
    program := program.withCompilerTables tables
    runtime
    functionAbiCache
    unitLayoutCache := some (CallCompatibility.bindUnitLayout runtime)
    sourceEquality
    entries
    bodies
    obligations
    indirect }

/-- Prepare call-resolution tables using the already validated immutable
runtime metadata for this program's unchanged ImportDocument. Compiler tables
may grow during preparation, but `CompilerGlobals.prepareProgram` changes only
the lowered bundle and leaves that document untouched. -/
def prepareWithRuntimeProfiled (profile : Lean.Options) (runtime : RuntimeMetadata) (program : LoweredProgram)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : Result Prepared := do
  let program := profileit "prepare.compiler_globals" profile fun _ => CompilerGlobals.prepareProgram program
  let sourceEquality := match sourceEquality with
    | some certificate => certificate
    | none => RuntimeMetadata.JsonReflexivity.prepare (left := runtime.source.raw)
  unless sourceEquality.matchesRight program.input.raw do
    throw "compiler call pipeline/runtime metadata are from different documents"
  prepareUsingRuntime profile program runtime sourceEquality

/-- Prepare call-resolution tables using validated runtime metadata. -/
def prepareWithRuntime (runtime : RuntimeMetadata) (program : LoweredProgram)
    (sourceEquality : Option (RuntimeMetadata.JsonReflexivity runtime.source.raw) := none) : Result Prepared :=
  prepareWithRuntimeProfiled {} runtime program sourceEquality

/-- Standalone compatibility path: validate RuntimeMetadata before resolving
instances or call-site queries, preserving the historical error order. -/
def prepare (program : LoweredProgram) : Result Prepared := do
  let program := CompilerGlobals.prepareProgram program
  let runtime ← (RuntimeMetadata.ofDocument program.input).mapError toString
  let sourceEquality := RuntimeMetadata.JsonReflexivity.prepare (left := runtime.source.raw)
  prepareUsingRuntime {} program runtime sourceEquality

def atSite (prepared : Prepared) (site : Site) : Result Resolution := do
  let matching := prepared.entries.filter (·.site == site)
  if matching.size != 1 then throw "missing or ambiguous compiler call site"
  (← require matching[0]? "missing compiler call site").outcome

/-- Function operand identity is checked in addition to body and block.
Source sites are compiler-table indices, never diagnostic span matches. -/
def resolveAt (prepared : Prepared) (site : Site) (function : MIR.Operand) : Result CallInstance := do
  let found ← atSite prepared site
  if found.function != function then throw "call-site function operand mismatch"
  return found.callee

def abiOfInstance (prepared : Prepared) (fnInstance : CallInstance) (extraArgs : Array TypeId) : Result (FnAbi TypeId) := do
  -- The exporter records fn_abi_of_instance(..., List::empty()). Extra-vararg
  -- queries require additional compiler evidence, even if an ABI looks similar.
  if !extraArgs.isEmpty then throw "missing compiler FnAbi query for extra arguments"
  let mut found := none
  for entry in prepared.entries do
    if let .ok resolution := entry.outcome then
      if resolution.callee == fnInstance then
        let abi ← resolution.abi
        if let some old := found then
          if old != abi then throw "conflicting compiler FnAbi queries for one complete instance"
        found := some abi
  require found "missing compiler FnAbi instance query"

/-- A loaded body carries the exact source table key. Equal MIR syntax does
not make distinct root/template/promoted/instance body identities interchangeable. -/
def loadedBodyOfInstance (prepared : Prepared) (fnInstance : CallInstance) : Result LoadedBody := do
  let matching := prepared.bodies.filter (·.fnInstance == fnInstance)
  unless matching.size == 1 do
    throw s!"missing or ambiguous canonical instance body identity: requested={reprStr fnInstance}, matches={matching.size}"
  let some candidate := matching[0]? | throw "compiler instance body is unavailable"
  let source ← require (prepared.program.input.instances.find? (·.id == candidate.sourceInstanceId))
    "canonical source instance record is missing"
  unless source.kind == .instanceMir do throw "compiler body is not a substituted executable instance"
  let instantiated ← require source.bodyInstantiation "instance body lacks substitution evidence"
  unless instantiated.status == .supported && instantiated.tag == "substituted_and_normalized" do
    throw "instance body substitution/normalization is unresolved"
  unless source.instanceArgsAreMonomorphic == some true do throw "instance arguments are not known monomorphic"
  let body ← require prepared.program.bundle.bodies[candidate.bodyIndex]? "instance body index is absent"
  unless body.obligations.isEmpty do throw "lowered instance body has unresolved obligations"
  return ⟨.ofCanonicalIndex candidate.bodyIndex, body.body⟩

/-- Compatibility syntax-only view of the exact loaded body. It retains the
same unique-key and instantiation checks; equal bodies are not merged. -/
def bodyOfInstance (prepared : Prepared) (fnInstance : CallInstance) : Result MIR.Body := do
  return (← loadedBodyOfInstance prepared fnInstance).body

private def lift (result : Result A) : CallM S A :=
  match result with | .ok value => pure value | .error message => throw (.unsupported message)

/-- Replace only ABI leaves with complete compiler records and source layout
compatibility. Machine dispatch, target features, caller locations, pointer
resolution and actual body interception remain required in the supplied hooks. -/
def bindAbi (prepared : Prepared) (compatibility : CallCompatibility.Evidence S)
    (budget : Nat)
    (base : CallHooks P S C E Other Extern (FnAbi TypeId) (ArgAbi TypeId)) :
    CallHooks P S C E Other Extern (FnAbi TypeId) (ArgAbi TypeId) := {
  base with
  fnAbiOfInstance := fun _ fnInstance extra => lift (abiOfInstance prepared fnInstance extra)
  abiCanUnwind := FnAbi.canUnwind
  abiVariadic := FnAbi.cVariadic
  abiFixedCount := fun abi => abi.fixedCount.toNat
  abiArgs := FnAbi.args
  abiReturn := FnAbi.ret
  sameConvention := fun left right => left.conv == right.conv
  argLayout := ArgAbi.layout
  argIsIgnore := ArgAbi.isIgnore
  isOneZst := fun layout => layout.layout.is1zst
  checkArgumentCompat := fun _ caller callee =>
    LayoutCompat.checkArgumentCompat (CallCompatibility.queries prepared.runtime compatibility prepared.unitLayoutCache)
      budget caller callee }

end Miri.Input.CallResolution
