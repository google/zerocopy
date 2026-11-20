import Miri.Input.Model.Types
import Miri.Input.SharedPayloads
import Miri.Input.JsonTraversalCache

namespace Miri.Input.DecoderValues

open Lean

def expectedMiriCommit : String := "7fa591d7d4dd9af8154becbc8332f8096f8323b1"
def expectedRustcCommit : String := "8144389c895da997dbdecaa635e41d6a50be6ffd"
def expectedSchema : String := "lean-miri-rustc-mir"
def expectedSchemaVersion : Nat := 3
def expectedCompilerAbiLayoutSchema : String := "physical_ty_and_layout_v1"

def escapePathKey (key : String) : String :=
  key.toList.foldl (fun out char => out ++ match char with
    | '%' => "%25"
    | '\\' => "%5C"
    | '.' => "%2E"
    | '[' => "%5B"
    | ']' => "%5D"
    | _ => String.ofList [char]) ""

def joinPath (path key : String) : String :=
  let key := escapePathKey key
  if path.isEmpty then key else path ++ "." ++ key

def field (j : Json) (key path : String) : Except String Json := do
  j.getObjVal? key |>.mapError fun e => s!"{path}: missing/invalid field `{key}` ({e})"

def fieldNat (j : Json) (key path : String) : Except String Nat := do
  let v ← field j key path
  v.getNat? |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer ({e})"

def fieldString (j : Json) (key path : String) : Except String String := do
  let v ← field j key path
  v.getStr? |>.mapError fun e => s!"{joinPath path key}: expected string ({e})"

def fieldBool (j : Json) (key path : String) : Except String Bool := do
  let v ← field j key path
  v.getBool? |>.mapError fun e => s!"{joinPath path key}: expected boolean ({e})"

def arrayField (j : Json) (key path : String) : Except String (Array Json) := do
  let v ← field j key path
  v.getArr? |>.mapError fun e => s!"{joinPath path key}: expected array ({e})"

def optionalNatField (j : Json) (key path : String) : Except String (Option Nat) := do
  let v ← field j key path
  if v == .null then pure none else
    (v.getNat?).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

def optionalField (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

def optionalString (j : Json) (key path : String) : Except String (Option String) := do
  match optionalField j key with
  | none | some .null => pure none
  | some value => (value.getStr?).map some |>.mapError fun e => s!"{joinPath path key}: expected string ({e})"

def objectFields (j : Json) : Except String (Array (String × Json)) := do
  match j with
  | .obj fields => pure fields.toList.toArray
  | _ => throw "expected object"

def statusOf? (j : Json) : Option String :=
  match optionalField j "status" with
  | none => none
  | some value => match value.getStr? with | .ok text => some text | .error _ => none

def parseStatus (value : String) : PayloadStatus :=
  match value with
  | "supported" | "complete" => .supported
  | "unsupported" => .unsupported
  | "unknown" => .unknown
  | "incomplete" => .incomplete
  | "debug_payload" => .debugPayload
  | other => .unrecognized other

def sourceDebugString (j : Json) (key path : String) : Except String String := do
  let value ← field j key path
  match value with
  | .str text => pure text
  | .obj _ =>
    if statusOf? value != some "debug_payload" then
      throw s!"{joinPath path key}: expected string or diagnostic debug payload"
    fieldString value "rustc_debug" (joinPath path key)
  | _ => throw s!"{joinPath path key}: expected string or diagnostic debug payload"

/-- Parsed successful shared payloads are memoized per input document. Keys use
the canonical JSON encoding so inline copies and DAG references share entries;
failed parses are never cached, preserving diagnostics at each occurrence. -/
structure DecodeMemo where
  private mk ::
  private sourceSpans : Std.HashMap Json SourceSpanData := {}
  private layouts : Std.HashMap Json Layout := {}
  private functionAbis : Std.HashMap Json FunctionAbi := {}

def emptyDecodeMemo : DecodeMemo := {}

def parseSourcePosition (j : Json) (path : String) : Except String SourcePosition := do
  return {
    line := ← fieldNat j "line" path
    column := ← fieldNat j "column" path
  }

def parseSourceSpanUncached (j : Json) (path : String) : Except String SourceSpanData := do
  if (j.getObjVal? "$lean_miri_shared_ref").isOk then
    throw s!"{path}: shared span reference requires a shared_payloads catalog"
  let start ← parseSourcePosition (← field j "start" path) (joinPath path "start")
  let endPos ← parseSourcePosition (← field j "end" path) (joinPath path "end")
  return {
    originalPayload := j.compress
    lo := ← fieldNat j "lo" path
    hi := ← fieldNat j "hi" path
    start := start
    «end» := endPos
    context := ← sourceDebugString j "ctxt" path
    file := ← sourceDebugString j "file" path
  }

def parseSourceSpan (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String SourceSpanData := do
  match memo.sourceSpans[j]? with
  | some value => pure value
  | none => parseSourceSpanUncached j path

def parseSourceInfo (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String SourceInfo := do
  return {
    span := ← parseSourceSpan (← field j "span" path) (joinPath path "span") memo
    scope := ← fieldNat j "scope" path
  }

def hasField (j : Json) (key : String) : Bool := (j.getObjVal? key).isOk

def isSourceSpanJson (j : Json) : Bool :=
  hasField j "lo" && hasField j "hi" && hasField j "start" && hasField j "end" &&
    hasField j "ctxt" && hasField j "file"

def statementVariant (tag : String) : StatementVariant :=
  match tag with
  | "Assign" => .assign
  | "FakeRead" => .fakeRead
  | "SetDiscriminant" => .setDiscriminant
  | "StorageLive" => .storageLive
  | "StorageDead" => .storageDead
  | "PlaceMention" => .placeMention
  | "AscribeUserType" => .ascribeUserType
  | "Coverage" => .coverage
  | "Intrinsic" => .intrinsic
  | "ConstEvalCounter" => .constEvalCounter
  | "Nop" => .nop
  | "BackwardIncompatibleDropHint" => .backwardIncompatibleDropHint
  | other => .unknown other

def terminatorVariant (tag : String) : TerminatorVariant :=
  match tag with
  | "Goto" => .goto
  | "SwitchInt" => .switchInt
  | "UnwindResume" => .unwindResume
  | "UnwindTerminate" => .unwindTerminate
  | "Return" => .return
  | "Unreachable" => .unreachable
  | "Drop" => .drop
  | "Call" => .call
  | "TailCall" => .tailCall
  | "Assert" => .assert
  | "Yield" => .yield
  | "CoroutineDrop" => .coroutineDrop
  | "FalseEdge" => .falseEdge
  | "FalseUnwind" => .falseUnwind
  | "InlineAsm" => .inlineAsm
  | other => .unknown other

def rvalueVariant (tag : String) : RvalueVariant :=
  match tag with
  | "Use" => .use
  | "Repeat" => .repeat
  | "Ref" => .ref
  | "ThreadLocalRef" => .threadLocalRef
  | "RawPtr" => .rawPtr
  | "Cast" => .cast
  | "BinaryOp" => .binaryOp
  | "UnaryOp" => .unaryOp
  | "Discriminant" => .discriminant
  | "Aggregate" => .aggregate
  | "CopyForDeref" => .copyForDeref
  | "WrapUnsafeBinder" => .wrapUnsafeBinder
  | "Reborrow" => .reborrow
  | other => .unknown other

def operandVariant (tag : String) : OperandVariant :=
  match tag with
  | "Copy" => .copy
  | "Move" => .move
  | "Constant" => .constant
  | "RuntimeChecks" => .runtimeChecks
  | other => .unknown other

def projectionVariant (tag : String) : ProjectionVariant :=
  match tag with
  | "Deref" => .deref
  | "Field" => .field
  | "Index" => .index
  | "ConstantIndex" => .constantIndex
  | "Subslice" => .subslice
  | "Downcast" => .downcast
  | "OpaqueCast" => .opaqueCast
  | "UnwrapUnsafeBinder" => .unwrapUnsafeBinder
  | "PhantomDeref" => .phantomDeref
  | other => .unknown other

def typeShapeKind (tag : String) : TypeShapeKind :=
  match tag with
  | "bool" => .bool
  | "char" => .char
  | "int" => .int
  | "uint" => .uint
  | "float" => .float
  | "adt" => .adt
  | "foreign" => .foreign
  | "str" => .str
  | "array" => .array
  | "pattern_type" => .patternType
  | "slice" => .slice
  | "raw_pointer" => .rawPointer
  | "reference" => .reference
  | "function_definition" => .functionDefinition
  | "function_pointer" => .functionPointer
  | "unsafe_binder" => .unsafeBinder
  | "dynamic_trait_object" => .dynamicTraitObject
  | "closure" => .closure
  | "coroutine_closure" => .coroutineClosure
  | "coroutine" => .coroutine
  | "coroutine_witness" => .coroutineWitness
  | "never" => .never
  | "tuple" => .tuple
  | "alias" => .alias
  | "parameter" => .parameter
  | "bound_type" => .boundType
  | "placeholder_type" => .placeholderType
  | "inference_type" => .inferenceType
  | "error_type" => .errorType
  | other => .unknown other

inductive Domain where
  | any | statement | terminator | rvalue | operand | projection
  | statementWrapper | terminatorWrapper
  deriving BEq, Hashable

structure DecodeValueKey where
  json : Json
  domain : Domain
  tagCategory : Option TypedEnumTag
  isRegionPath : Bool
  isHirIdPath : Bool
  isCoveragePath : Bool
  isCastCoercionPath : Bool
  deriving BEq, Hashable

def decodeValueKey (j : Json) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) : DecodeValueKey := {
  json := j
  domain := domain
  tagCategory := tagCategory
  isRegionPath := path.endsWith ".region"
  isHirIdPath := path.endsWith ".hir_id"
  isCoveragePath := path.endsWith ".coverage"
  isCastCoercionPath := path.endsWith ".cast_kind.coercion"
}

def asTag? (j : Json) (key : String) : Option String :=
  match optionalField j key with
  | none => none
  | some value => match value.getStr? with | .ok text => some text | .error _ => none

def singletonRef (j : Json) (key : String) : Option Nat :=
  match objectFields j with
  | .error _ => none
  | .ok fields =>
    match fields.toList with
    | [(name, value)] =>
      if name != key then none else
        match value.getNat? with | .ok id => some id | .error _ => none
    | _ => none

def isTypeRef (j : Json) : Option Nat := singletonRef j "type_id"

def isAllocationRef (j : Json) : Option Nat := do
  singletonRef j "allocation_id"

def childDomain (parent : Domain) (key : String) : Domain :=
  match parent, key with
  | .statementWrapper, "kind" => .statement
  | .terminatorWrapper, "kind" => .terminator
  | _, "rvalue" => .rvalue
  | _, "operand" | _, "function" | _, "condition" | _, "discriminant" => .operand
  | _, "projection" => .projection
  | _, "statements" => .statementWrapper
  | _, "terminator" => .terminatorWrapper
  | _, _ => .any

def isKnownStatement (tag : String) : Bool :=
  match statementVariant tag with | .unknown _ => false | _ => true
def isKnownTerminator (tag : String) : Bool :=
  match terminatorVariant tag with | .unknown _ => false | _ => true
def isKnownRvalue (tag : String) : Bool :=
  match rvalueVariant tag with | .unknown _ => false | _ => true
def isKnownOperand (tag : String) : Bool :=
  match operandVariant tag with | .unknown _ => false | _ => true
def isKnownProjection (tag : String) : Bool :=
  match projectionVariant tag with | .unknown _ => false | _ => true

def recognizedAutoDomain (j : Json) : Option Domain :=
  if (optionalField j "status").isSome then
  if let some v := asTag? j "variant" then
    if isKnownStatement v then some .statement
    else if isKnownTerminator v then some .terminator
    else none
  else
    match asTag? j "kind" with
    | none => none
    | some tag =>
      if isKnownRvalue tag then some .rvalue
      else if isKnownOperand tag then some .operand
      else if isKnownProjection tag then some .projection
      else none
  else none

def domainTag (j : Json) (domain : Domain) : Option String :=
  match domain with
  | .statement | .terminator | .statementWrapper | .terminatorWrapper => asTag? j "variant"
  | .rvalue | .operand | .projection => asTag? j "kind"
  | .any => none

def isStringJson (j : Json) : Bool :=
  match j with | .str _ => true | _ => false

def integerTypeTag (text : String) : IntegerTypeTag :=
  match text with
  | "i8" => .known .i8 | "i16" => .known .i16 | "i32" => .known .i32
  | "i64" => .known .i64 | "i128" => .known .i128 | "isize" => .known .isize
  | "u8" => .known .u8 | "u16" => .known .u16 | "u32" => .known .u32
  | "u64" => .known .u64 | "u128" => .known .u128 | "usize" => .known .usize
  | other => .unknown other

def floatTypeTag (text : String) : FloatTypeTag :=
  match text with
  | "f16" => .f16 | "f16b" => .f16b | "f32" => .f32 | "f64" => .f64
  | "f128" => .f128 | "ppcf128" => .ppcf128
  | other => .unknown other

def adtKindTag (text : String) : AdtKind :=
  match text with
  | "struct" => .structKind
  | "union" => .unionKind
  | "enum" => .enumKind
  | other => .unknown other

def binOpFromExportTag (tag : String) : Option Miri.MIR.BinOp :=
  match tag with
  | "add" => some .Add | "add_unchecked" => some .AddUnchecked
  | "add_with_overflow" => some .AddWithOverflow
  | "sub" => some .Sub | "sub_unchecked" => some .SubUnchecked
  | "sub_with_overflow" => some .SubWithOverflow
  | "mul" => some .Mul | "mul_unchecked" => some .MulUnchecked
  | "mul_with_overflow" => some .MulWithOverflow
  | "div" => some .Div | "rem" => some .Rem
  | "bit_xor" => some .BitXor | "bit_and" => some .BitAnd | "bit_or" => some .BitOr
  | "shift_left" => some .Shl | "shift_left_unchecked" => some .ShlUnchecked
  | "shift_right" => some .Shr | "shift_right_unchecked" => some .ShrUnchecked
  | "equal" => some .Eq | "less_than" => some .Lt | "less_equal" => some .Le
  | "not_equal" => some .Ne | "greater_equal" => some .Ge | "greater_than" => some .Gt
  | "compare" => some .Cmp | "pointer_offset" => some .Offset
  | _ => Miri.MIR.BinOp.ofString tag

def unOpFromExportTag (tag : String) : Option Miri.MIR.UnOp :=
  match tag with
  | "not" => some .Not
  | "negate" => some .Neg
  | "pointer_metadata" => some .PtrMetadata
  | _ => Miri.MIR.UnOp.ofString tag

def statusField (j : Json) (path : String) (optional : Bool := false)
    : Except String PayloadStatus := do
  match optionalField j "status" with
  | none =>
    if optional then pure .supported
    else throw s!"{joinPath path "status"}: missing required status tag"
  | some value =>
    let text ← value.getStr? |>.mapError fun e => s!"{joinPath path "status"}: expected string ({e})"
    pure (parseStatus text)

def parseOperatorTag (j : Json) (path : String) : Except String (String × PayloadStatus) := do
  match j with
  | .str tag => pure (tag, .supported)
  | .obj _ =>
    let tag ← fieldString j "kind" path
    let status ← statusField j path
    pure (tag, status)
  | _ => throw s!"{path}: expected tagged operator object"

def typedEnumCategory? (key path : String) (parentTag : Option String) (j : Json) : Option TypedEnumTag := Id.run do
  let hasKind := (optionalField j "kind").isSome
  let hasStatus := (optionalField j "status").isSome
  match key with
  | "safety" => if hasKind || isStringJson j then some .safety else none
  | "borrow_kind" => if hasKind then some .borrowKind else none
  | "fake_kind" => if isStringJson j then some .fakeBorrowKind else none
  | "mutability_kind" => if isStringJson j then some .mutBorrowKind else none
  | "mutability" => if hasKind then some .mutability else none
  | "cast_kind" => if hasKind then some .castKind else none
  | "coercion" => if hasKind then some .pointerCoercion else none
  | "source" =>
    if path.endsWith ".cast_kind.coercion" && hasKind then some .coercionSource else none
  | "aggregate_kind" => if hasKind then some .aggregateKind else none
  | "unwind" => if hasKind then some .unwindAction else none
  | "phase" | "injection_phase" =>
    if hasKind && hasStatus then some .mirPhase
    else if isStringJson j then some .mirPhaseStage
    else none
  | "retag" => if hasKind && hasStatus then some .withRetag else none
  | "check" => if parentTag == some "RuntimeChecks" && hasKind && hasStatus then some .runtimeCheck else none
  | "cause" => if hasKind && hasStatus then some .fakeReadCause else none
  | "call_source" => if hasKind && hasStatus then some .callSource else none
  | "reason" =>
    if parentTag == some "BackwardIncompatibleDropHint" && hasKind && hasStatus then
      some .backwardDropReason
    else if hasKind && hasStatus then some .unwindReason
    else none
  | "region" => if hasKind && hasStatus then some .regionKind else none
  | "bound_kind" => if hasKind && hasStatus then some .boundRegionKind else none
  | "index_kind" => if hasKind then some .boundVarIndexKind else none
  | "parameter" => if path.endsWith ".region" && hasKind then some .lateParamRegionKind else none
  | "signed_kind" | "unsigned_kind" | "integer_kind" => if isStringJson j then some .integerType else none
  | "float_kind" => if isStringJson j then some .floatType else none
  | "adt_kind" => if isStringJson j then some .adtKind else none
  | "variance" => if hasKind && hasStatus then some .variance else none
  | "coverage" => if parentTag == some "Coverage" && hasKind && hasStatus then some .coverageKind else none
  | "point_kind" => if path.endsWith ".coverage" && isStringJson j then some .coveragePointKind else none
  | "retag_mode" => if isStringJson j then some .fakeBorrowRetagMode else none
  | _ => none

def parseInlineTag (j : Json) (path : String) : Except String TaggedNode := do
  match j with
  | .str tag => return ⟨.supported, tag, j⟩
  | .obj _ =>
    let tag ← fieldString j "kind" path
    let status ← match optionalField j "status" with
      | none => pure .supported
      | some value => parseStatus <$> (value.getStr? |>.mapError fun e => s!"{joinPath path "status"}: expected string ({e})")
    return ⟨status, tag, j⟩
  | _ => throw s!"{path}: expected enum tag object or string"

def userTypeProjectionKind (j : Json) (path : String) : Except String UserTypeProjectionKind := do
  let tag ← fieldString j "kind" path
  match tag with
  | "Deref" => pure .deref
  | "Field" => pure (.field (← fieldNat j "index" path))
  | "Index" => pure .index
  | "ConstantIndex" =>
    pure (.constantIndex (← fieldNat j "offset" path) (← fieldNat j "min_length" path)
      (← fieldBool j "from_end" path))
  | "Subslice" =>
    pure (.subslice (← fieldNat j "from" path) (← fieldNat j "to" path)
      (← fieldBool j "from_end" path))
  | "Downcast" =>
    let nameValue ← field j "name" path
    let name ← match nameValue with
      | .null => pure none
      | _ => (nameValue.getStr?).map some |>.mapError fun e => s!"{joinPath path "name"}: expected string or null ({e})"
    pure (.downcast name (← fieldNat j "variant_index" path))
  | "OpaqueCast" => pure .opaqueCast
  | "UnwrapUnsafeBinder" => pure .unwrapUnsafeBinder
  | "PhantomDeref" => pure .phantomDeref
  | other => pure (.unknown other)

def parseUserTypeProjection (j : Json) (path : String) : Except String UserTypeProjection := do
  let status ← statusField j path
  let baseIndex ← match optionalField j "base_index" with
    | none | some .null => pure none
    | some value => (value.getNat?).map some |>.mapError fun e => s!"{joinPath path "base_index"}: expected unsigned integer ({e})"
  let projections ← match optionalField j "projections" with
    | none | some .null => pure none
    | some _ =>
      let json ← arrayField j "projections" path
      let mut parsed := #[]
      for (item, index) in json.toList.zipIdx do
        parsed := parsed.push (← userTypeProjectionKind item s!"{joinPath path "projections"}[{index}]")
      pure (some parsed)
  if status == .supported && (baseIndex.isNone || projections.isNone) then
    throw s!"{path}: supported user-type projection is missing base index or projection sequence"
  return ⟨status, baseIndex, projections, j⟩

abbrev DecodeValueM := StateT (Std.HashMap DecodeValueKey TypedValue) (Except String)

mutual
partial def decodeValueM (j : Json) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) (memo : DecodeMemo) : DecodeValueM TypedValue := do
  let key := decodeValueKey j path domain tagCategory
  if let some value := (← get).get? key then return value
  let value ← decodeValueBody j path domain tagCategory memo
  modify fun cache => cache.insert key value
  return value

partial def decodeValueBody (j : Json) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) (memo : DecodeMemo) : DecodeValueM TypedValue := do
  if let some id := isTypeRef j then return .typeRef id
  if let some id := isAllocationRef j then return .allocationRef id
  if statusOf? j == some "debug_payload" then return .diagnostic j
  match j with
  | .arr values =>
    let mut decoded := #[]
    let mut index := 0
    for value in values do
      decoded := decoded.push (← decodeValueM value s!"{path}[{index}]" domain tagCategory memo)
      index := index + 1
    return .array decoded
  | .obj _ =>
    if isSourceSpanJson j then return .sourceSpan (← parseSourceSpan j path memo)
    if hasField j "span" && hasField j "scope" then
      return .sourceInfo (← parseSourceInfo j path memo)
    let effectiveDomain := if domain == .any then
      match recognizedAutoDomain j with | some detected => detected | none => .any
      else domain
    let fields ← objectFields j
    let mut decodedFields := #[]
    let parentTag := match effectiveDomain with
      | .rvalue | .operand | .statement | .terminator => domainTag j effectiveDomain
      | _ => none
    for (key, value) in fields do
      let nextDomain := childDomain effectiveDomain key
      let decoded ← if key == "user_type_projection" && parentTag == some "AscribeUserType" then
          .userTypeProjection <$> parseUserTypeProjection value (joinPath path key)
        else if key == "operator" && (parentTag == some "BinaryOp" || optionalField j "kind" == some (.str "Overflow")) then
          let (tag, status) ← parseOperatorTag value (joinPath path key)
          match binOpFromExportTag tag with
          | some op => pure (.binOperator op status)
          | none => pure (.unknownBinOperator tag status)
        else if key == "operator" && parentTag == some "UnaryOp" then
          let (tag, status) ← parseOperatorTag value (joinPath path key)
          match unOpFromExportTag tag with
          | some op => pure (.unOperator op status)
          | none => pure (.unknownUnOperator tag status)
        else decodeValueM value (joinPath path key) nextDomain (typedEnumCategory? key path parentTag value) memo
      let isTagField := match effectiveDomain with
        | .statement | .terminator | .rvalue | .operand | .projection => key == "status" || key == "variant" || key == "kind"
        | _ => false
      let decoded := match key, value with
        | "instance_id", .num _ =>
          match value.getNat? with | .ok id => .instanceRef id | .error _ => decoded
        | "local", .num _ =>
          match value.getNat? with | .ok id => .localRef id | .error _ => decoded
        | "block", .num _ | "target", .num _ | "otherwise", .num _
        | "real_target", .num _ | "imaginary_target", .num _ | "resume", .num _ =>
          match value.getNat? with | .ok id => .blockRef id | .error _ => decoded
        | _, _ => decoded
      if !isTagField then decodedFields := decodedFields.push (key, decoded)
    match effectiveDomain with
    | .statement =>
      let tag ← fieldString j "variant" path
      let status := parseStatus (← fieldString j "status" path)
      return .statement (statementVariant tag) status decodedFields
    | .terminator =>
      let tag ← fieldString j "variant" path
      let status := parseStatus (← fieldString j "status" path)
      return .terminator (terminatorVariant tag) status decodedFields
    | .rvalue =>
      let tag ← fieldString j "kind" path
      let status := parseStatus (← fieldString j "status" path)
      if tag == "BinaryOp" || tag == "UnaryOp" then
        let operator ← field j "operator" path
        let _ ← parseOperatorTag operator (joinPath path "operator")
      return .rvalue (rvalueVariant tag) status decodedFields
    | .operand =>
      let tag ← fieldString j "kind" path
      let status := parseStatus (← fieldString j "status" path)
      return .operand (operandVariant tag) status decodedFields
    | .projection =>
      let tag ← fieldString j "kind" path
      return .projection (projectionVariant tag) decodedFields
    | .any | .statementWrapper | .terminatorWrapper =>
      match tagCategory with
      | some category => return .enumTag category (← parseInlineTag j path) decodedFields
      | none => return .object decodedFields
  | .str _ =>
    match tagCategory with
    | some category => return .enumTag category (← parseInlineTag j path) #[]
    | none => return .scalar j
  | _ => return .scalar j
end

def decodeValue (j : Json) (path : String) (domain : Domain := .any)
    (tagCategory : Option TypedEnumTag := none) (memo : DecodeMemo := {}) : Except String TypedValue := do
  (decodeValueM j path domain tagCategory memo).run' {}

def statusObligation? (status : PayloadStatus) (path : String) : Option Obligation :=
  match status with
  | .supported | .debugPayload => none
  | .unsupported => some ⟨path, "exporter marked this payload unsupported; it is an unresolved semantic obligation"⟩
  | .unknown => some ⟨path, "exporter could not resolve this payload; it is an unresolved obligation"⟩
  | .incomplete => some ⟨path, "exporter marked this payload incomplete; it is an unresolved obligation"⟩
  | .unrecognized value => some ⟨path, s!"unrecognized status `{value}`"⟩

def unknownTagObligation (tag : String) (path : String) : Obligation :=
  ⟨path, s!"unrecognized pinned MIR enum tag `{tag}`; update decoder and review its semantics"⟩

def enumTagKnown (category : TypedEnumTag) (tag : String) : Bool :=
  match category with
  | .safety => tag == "safe" || tag == "unsafe"
  | .borrowKind => tag == "shared" || tag == "mutable" || tag == "fake"
  | .fakeBorrowKind => tag == "shallow" || tag == "deep"
  | .mutBorrowKind => tag == "default" || tag == "two_phase" || tag == "closure_capture"
  | .mutability => tag == "mutable" || tag == "immutable"
  | .castKind => tag == "PointerExposeProvenance" || tag == "PointerWithExposedProvenance" ||
      tag == "PointerCoercion" || tag == "IntToInt" || tag == "FloatToInt" ||
      tag == "FloatToFloat" || tag == "IntToFloat" || tag == "PtrToPtr" ||
      tag == "FnPtrToPtr" || tag == "Transmute" || tag == "BoxDerefTransmute" || tag == "Subtype"
  | .pointerCoercion => tag == "ReifyFnPointer" || tag == "UnsafeFnPointer" ||
      tag == "ClosureFnPointer" || tag == "MutToConstPointer" || tag == "ArrayToPointer" || tag == "Unsize"
  | .coercionSource => tag == "as_cast" || tag == "implicit"
  | .unwindReason => tag == "abi" || tag == "in_cleanup"
  | .aggregateKind => tag == "Array" || tag == "Tuple" || tag == "Adt" ||
      tag == "Closure" || tag == "Coroutine" || tag == "CoroutineClosure" || tag == "RawPtr"
  | .unwindAction => tag == "Continue" || tag == "Unreachable" || tag == "Terminate" || tag == "Cleanup"
  | .mirPhase => tag == "built" || tag == "analysis" || tag == "runtime"
  | .mirPhaseStage => tag == "initial" || tag == "post_cleanup" || tag == "optimized"
  | .withRetag => tag == "yes" || tag == "no"
  | .runtimeCheck => tag == "ub_checks" || tag == "contract_checks" || tag == "overflow_checks"
  | .fakeReadCause => tag == "match_guard" || tag == "matched_place" ||
      tag == "guard_binding" || tag == "let_binding" || tag == "index"
  | .callSource => tag == "overloaded_operator" || tag == "match_comparison" ||
      tag == "miscellaneous_desugaring" || tag == "clone_or_use" || tag == "normal_call"
  | .backwardDropReason => tag == "edition_2024"
  | .regionKind => tag == "early_parameter" || tag == "bound" || tag == "late_parameter" ||
      tag == "static" || tag == "inference_variable" || tag == "placeholder" ||
      tag == "erased" || tag == "error"
  | .boundRegionKind => tag == "anonymous" || tag == "named_for_printing" ||
      tag == "named" || tag == "closure_environment"
  | .boundVarIndexKind => tag == "bound" || tag == "canonical"
  | .lateParamRegionKind => tag == "anonymous" || tag == "named_anonymous" ||
      tag == "named" || tag == "closure_environment"
  | .integerType => ["i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize"].contains tag
  | .floatType => ["f16", "f16b", "f32", "f64", "f128", "ppcf128"].contains tag
  | .adtKind => tag == "struct" || tag == "union" || tag == "enum"
  | .variance => tag == "covariant" || tag == "contravariant" || tag == "invariant" || tag == "bivariant"
  | .coverageKind => tag == "point" || tag == "block_marker" || tag == "virtual_counter"
  | .coveragePointKind => tag == "expr" || tag == "implicit_else" || tag == "function_end"
  | .fakeBorrowRetagMode => tag == "default"
  | .other _ => false

def valueLocalObligationsInto (value : TypedValue) (path : String)
    (initial : Array Obligation) : Array Obligation := Id.run do
  match value with
  | .scalar _ | .diagnostic _ | .typeRef _ | .allocationRef _ | .instanceRef _
  | .localRef _ | .blockRef _ | .sourceSpan _ | .sourceInfo _ => return initial
  | .binOperator _ status | .unOperator _ status =>
      return match statusObligation? status path with
        | some issue => initial.push issue
        | none => initial
  | .unknownBinOperator tag status | .unknownUnOperator tag status =>
      let withTag := initial.push (unknownTagObligation tag path)
      return match statusObligation? status path with
        | some issue => withTag.push issue
        | none => withTag
  | .enumTag category tag children => do
      let mut out := initial
      if let some issue := statusObligation? tag.status path then out := out.push issue
      if !enumTagKnown category tag.tag then
        out := out.push (unknownTagObligation tag.tag (joinPath path "kind"))
      if category == .mirPhase then
        let phaseValue := children.find? fun (key, _) => key == "phase"
        match tag.tag with
        | "built" =>
          if phaseValue.isSome then out := out.push ⟨path, "built MIR phase must not include a subphase"⟩
        | "analysis" | "runtime" =>
          match phaseValue with
          | none => out := out.push ⟨joinPath path "phase", "analysis/runtime MIR phase is missing its subphase"⟩
          | some (_, .enumTag .mirPhaseStage phaseTag _) =>
            let valid := if tag.tag == "analysis" then
              phaseTag.tag == "initial" || phaseTag.tag == "post_cleanup"
              else phaseTag.tag == "initial" || phaseTag.tag == "post_cleanup" || phaseTag.tag == "optimized"
            if !valid then out := out.push ⟨joinPath path "phase", s!"subphase `{phaseTag.tag}` does not belong to `{tag.tag}` MIR"⟩
          | some (_, _) => out := out.push ⟨joinPath path "phase", "MIR subphase is not a typed tag"⟩
        | _ => pure ()
      if category == .withRetag then
        let performs := children.find? fun (key, _) => key == "performs_retag"
        match performs with
        | some (_, .scalar (.bool value)) =>
          if value != (tag.tag == "yes") then out := out.push ⟨joinPath path "performs_retag", "boolean disagrees with the WithRetag tag"⟩
        | _ => out := out.push ⟨joinPath path "performs_retag", "WithRetag tag is missing its boolean witness"⟩
      if category == .runtimeCheck then
        match children.find? fun (key, _) => key == "enabled" with
        | some (_, .scalar (.bool _)) => pure ()
        | _ => out := out.push ⟨joinPath path "enabled", "runtime-check tag is missing its configured boolean"⟩
      if category == .coverageKind then
        let hasNatField := fun key =>
          match children.find? fun (fieldKey, _) => fieldKey == key with
          | some (_, .scalar (.num value)) => ((Json.num value).getNat?).isOk
          | _ => false
        match tag.tag with
        | "point" =>
          match children.find? fun (key, _) => key == "point_kind" with
          | some (_, .enumTag .coveragePointKind _ _) => pure ()
          | _ => out := out.push ⟨joinPath path "point_kind", "coverage point is missing its typed point kind"⟩
          match children.find? fun (key, _) => key == "hir_id" with
          | some (_, .object fields) =>
            let hasOwner := fields.any fun (key, value) =>
              key == "owner_def_id" && match value with | .scalar (.str _) => true | _ => false
            let hasLocalId := fields.any fun (key, value) =>
              key == "local_id" && match value with
                | .scalar (.num number) => ((Json.num number).getNat?).isOk
                | _ => false
            if !hasOwner || !hasLocalId then
              out := out.push ⟨joinPath path "hir_id", "coverage point has malformed owner DefId or local HIR index"⟩
          | _ => out := out.push ⟨joinPath path "hir_id", "coverage point is missing its HIR identifier"⟩
        | "block_marker" =>
          if !hasNatField "id" then out := out.push ⟨joinPath path "id", "block-marker coverage is missing its identifier"⟩
        | "virtual_counter" =>
          if !hasNatField "bcb" then out := out.push ⟨joinPath path "bcb", "virtual-counter coverage is missing its basic-block counter"⟩
        | _ => pure ()
      if category == .regionKind then
        let hasField := fun key => (children.find? fun (fieldKey, _) => fieldKey == key).isSome
        match tag.tag with
        | "early_parameter" =>
          if !hasField "index" || !hasField "name" then
            out := out.push ⟨path, "early region parameter is missing its index or name"⟩
        | "bound" =>
          if !hasField "index_kind" || !hasField "variable_index" || !hasField "bound_kind" then
            out := out.push ⟨path, "bound region is missing index, variable, or bound-kind metadata"⟩
        | "late_parameter" =>
          if !hasField "scope_def_id" || !hasField "scope_def_path" || !hasField "parameter" then
            out := out.push ⟨path, "late region parameter is missing its scope or parameter metadata"⟩
        | "inference_variable" | "placeholder" =>
          if !hasField "index" && !hasField "universe" then
            out := out.push ⟨path, "region variable is missing its identifying metadata"⟩
        | _ => pure ()
      return out
  | .userTypeProjection projection => do
      let mut out := initial
      if let some issue := statusObligation? projection.status path then out := out.push issue
      if projection.status == .supported then
        if projection.baseIndex.isNone then
          out := out.push ⟨joinPath path "base_index", "supported user-type projection is missing its base annotation index"⟩
        if projection.projections.isNone then
          out := out.push ⟨joinPath path "projections", "supported user-type projection is missing its projection sequence"⟩
      match projection.projections with
      | some entries =>
        for (entry, index) in entries.toList.zipIdx do
          match entry with
          | .unknown tag => out := out.push (unknownTagObligation tag s!"{joinPath path "projections"}[{index}].kind")
          | _ => pure ()
      | none => pure ()
      return out
  | .array _ => return initial
  | .object fields => do
      let mut out := initial
      return out
  | .statement variant status fields => do
      let mut out := initial
      if let some issue := statusObligation? status path then out := out.push issue
      match variant with
      | .unknown tag => out := out.push (unknownTagObligation tag (joinPath path "variant"))
      | .ascribeUserType =>
        if status == .supported then
          if !(fields.any fun (key, value) => key == "user_type_projection" && match value with | .userTypeProjection _ => true | _ => false) then
            out := out.push ⟨joinPath path "user_type_projection", "supported AscribeUserType is missing typed projection data"⟩
          if !(fields.any fun (key, value) => key == "variance" && match value with | .enumTag .variance _ _ => true | _ => false) then
            out := out.push ⟨joinPath path "variance", "supported AscribeUserType is missing typed variance data"⟩
      | .coverage =>
        if status == .supported && !(fields.any fun (key, value) => key == "coverage" && match value with | .enumTag .coverageKind _ _ => true | _ => false) then
          out := out.push ⟨joinPath path "coverage", "supported Coverage statement is missing its typed coverage kind"⟩
      | _ => pure ()
      return out
  | .terminator variant status fields => do
      let mut out := initial
      if let some issue := statusObligation? status path then out := out.push issue
      match variant with
      | .unknown tag => out := out.push (unknownTagObligation tag (joinPath path "variant"))
      | _ => pure ()
      return out
  | .rvalue variant status fields => do
      let mut out := initial
      if let some issue := statusObligation? status path then out := out.push issue
      match variant with
      | .unknown tag => out := out.push (unknownTagObligation tag (joinPath path "kind"))
      | _ => pure ()
      return out
  | .operand variant status fields => do
      let mut out := initial
      if let some issue := statusObligation? status path then out := out.push issue
      match variant with
      | .unknown tag => out := out.push (unknownTagObligation tag (joinPath path "kind"))
      | _ => pure ()
      return out
  | .projection variant fields => do
      let mut out := initial
      match variant with
      | .unknown tag => out := out.push (unknownTagObligation tag (joinPath path "kind"))
      | _ => pure ()
      return out

partial def valueObligationsInto (value : TypedValue) (path : String)
    (initial : Array Obligation) : Array Obligation := Id.run do
  let mut out := valueLocalObligationsInto value path initial
  match value with
  | .array values =>
    let mut index := 0
    for child in values do
      out := valueObligationsInto child s!"{path}[{index}]" out
      index := index + 1
  | .object fields | .enumTag _ _ fields | .statement _ _ fields | .terminator _ _ fields
  | .rvalue _ _ fields | .operand _ _ fields | .projection _ fields =>
    for (key, child) in fields do
      match value, key, child with
      | .enumTag _ _ _, "status", .scalar (.str text) =>
        if let some issue := statusObligation? (parseStatus text) (joinPath path key) then out := out.push issue
      | .enumTag _ _ _, "status", _ => out := out.push ⟨joinPath path key, "enum status must be a string"⟩
      | .object _, "status", .scalar (.str text) =>
        if let some issue := statusObligation? (parseStatus text) (joinPath path key) then out := out.push issue
      | .object _, "status", _ => out := out.push ⟨joinPath path key, "status field must be a string"⟩
      | _, _, _ => pure ()
      out := valueObligationsInto child (joinPath path key) out
  | _ => pure ()
  return out

def valueObligations (value : TypedValue) (path : String) : Array Obligation :=
  valueObligationsInto value path #[]

inductive RuntimeObligationSequence where
  | leaf (items : Array Obligation)
  | append (left right : RuntimeObligationSequence)
  | rebase (oldPath newPath : String) (inner : RuntimeObligationSequence)
  deriving Inhabited

def appendRuntimeObligations (left right : Option RuntimeObligationSequence) :
    Option RuntimeObligationSequence :=
  match left, right with
  | none, right => right
  | left, none => left
  | some left, some right => some (.append left right)

def rebaseRuntimeObligation (issue : Obligation) (oldPath newPath : String) : Obligation :=
  let path := if issue.path == oldPath then newPath else
    if issue.path.startsWith (oldPath ++ ".") || issue.path.startsWith (oldPath ++ "[") then
      newPath ++ String.ofList (issue.path.toList.drop oldPath.toList.length)
    else issue.path
  { issue with path := path }

def flattenRuntimeObligations (sequence : Option RuntimeObligationSequence) : Array Obligation := Id.run do
  let mut pending : Array (RuntimeObligationSequence × Array (String × String)) := match sequence with
    | some sequence => #[(sequence, #[])]
    | none => #[]
  let mut result := #[]
  while h : pending.size > 0 do
    let (sequence, rebases) := pending[pending.size - 1]'(by omega)
    pending := pending.pop
    match sequence with
    | .leaf items =>
      for item in items do
        result := result.push (rebases.reverse.foldl (fun issue (oldPath, newPath) =>
          rebaseRuntimeObligation issue oldPath newPath) item)
    | .append left right =>
      pending := pending.push (right, rebases)
      pending := pending.push (left, rebases)
    | .rebase oldPath newPath inner =>
      pending := pending.push (inner, rebases.push (oldPath, newPath))
  return result

structure RuntimeValueDecode where
  /-- Only the direct fields consumed by the parent's local invariants. -/
  summary : TypedValue
  obligations : Option RuntimeObligationSequence

/-- Document-local node identity plus every decoding context flag. Only successful
results are memoized; diagnostics are rebased separately for each occurrence. -/
structure RuntimeValueKey where
  json : JsonTraversalCache.IdentityKey
  domain : Domain
  tagCategory : Option TypedEnumTag
  isRegionPath : Bool
  isHirIdPath : Bool
  isCoveragePath : Bool
  isCastCoercionPath : Bool
  deriving BEq, Hashable

def runtimeValueKey (node : JsonTraversalCache.Node) (path : String)
    (domain : Domain) (tagCategory : Option TypedEnumTag) : RuntimeValueKey := {
  json := node.identity
  domain := domain
  tagCategory := tagCategory
  isRegionPath := path.endsWith ".region"
  isHirIdPath := path.endsWith ".hir_id"
  isCoveragePath := path.endsWith ".coverage"
  isCastCoercionPath := path.endsWith ".cast_kind.coercion"
}

/-- The raw fallback retains the original key comparison and hash exactly,
including manually constructed JSON whose BEq need not be lawful. -/
theorem runtimeValueKey_uncached_beq_eq (a b : Json)
    (pathA pathB : String) (domainA domainB : Domain)
    (tagA tagB : Option TypedEnumTag) :
    (runtimeValueKey (.uncached a) pathA domainA tagA ==
      runtimeValueKey (.uncached b) pathB domainB tagB) =
    (decodeValueKey a pathA domainA tagA == decodeValueKey b pathB domainB tagB) := rfl

theorem runtimeValueKey_uncached_hash_eq (value : Json) (path : String)
    (domain : Domain) (tag : Option TypedEnumTag) :
    hash (runtimeValueKey (.uncached value) path domain tag) =
      hash (decodeValueKey value path domain tag) := rfl

abbrev RuntimeDecodeCache := Std.HashMap RuntimeValueKey (String × RuntimeValueDecode)

def runtimeLocalObligations (value : TypedValue) (path : String)
    (children : Option RuntimeObligationSequence := none) : Option RuntimeObligationSequence :=
  let localIssues := valueLocalObligationsInto value path #[]
  if localIssues.isEmpty then children
  else appendRuntimeObligations (some (.leaf localIssues)) children

initialize runtimeSummaryKeys : Std.HashSet String ← pure (Std.HashSet.ofList [
  "status", "phase", "performs_retag", "enabled", "point_kind", "hir_id",
  "id", "bcb", "index", "name", "index_kind", "variable_index",
  "bound_kind", "scope_def_id", "scope_def_path", "parameter", "universe",
  "base_index", "projections", "user_type_projection", "variance", "coverage"])

def runtimeSummaryChild (key : String) (value : TypedValue) : TypedValue :=
  if key == "hir_id" then
    match value with
    | .object fields => .object (fields.filter fun (field, _) => field == "owner_def_id" || field == "local_id")
    | other => other
  else
    match value with
    | .enumTag category tag _ => .enumTag category tag #[]
    | .statement variant status _ => .statement variant status #[]
    | .terminator variant status _ => .terminator variant status #[]
    | .rvalue variant status _ => .rvalue variant status #[]
    | .operand variant status _ => .operand variant status #[]
    | .projection variant _ => .projection variant #[]
    | .object _ => .object #[]
    | .array _ => .array #[]
    | other => other

abbrev RuntimeDecodeM := StateT RuntimeDecodeCache (Except String)

mutual
partial def decodeRuntimeValueM (node : JsonTraversalCache.Node) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) (memo : DecodeMemo) : RuntimeDecodeM RuntimeValueDecode := do
  if !node.shouldMemo then return ← decodeRuntimeValueBody node path domain tagCategory memo
  -- Scalars are cheap and mostly inline. Giving every occurrence its own cache
  -- entry would retain millions of unique leaf IDs without sharing any work.
  match node.value with
  | .arr _ | .obj _ => pure ()
  | _ => return ← decodeRuntimeValueBody node path domain tagCategory memo
  let key := runtimeValueKey node path domain tagCategory
  if let some (oldPath, decoded) := (← get).get? key then
    if oldPath == path then return decoded
    return { decoded with obligations := decoded.obligations.map fun issues => .rebase oldPath path issues }
  let decoded ← decodeRuntimeValueBody node path domain tagCategory memo
  modify fun cache => cache.insert key (path, decoded)
  return decoded

partial def decodeRuntimeValueBody (node : JsonTraversalCache.Node) (path : String) (domain : Domain)
    (tagCategory : Option TypedEnumTag) (memo : DecodeMemo) : RuntimeDecodeM RuntimeValueDecode := do
  let j := node.value
  if let some id := isTypeRef j then
    let value := TypedValue.typeRef id
    return ⟨value, runtimeLocalObligations value path⟩
  if let some id := isAllocationRef j then
    let value := TypedValue.allocationRef id
    return ⟨value, runtimeLocalObligations value path⟩
  if statusOf? j == some "debug_payload" then
    let value := TypedValue.diagnostic j
    return ⟨value, runtimeLocalObligations value path⟩
  match j with
  | .arr values =>
    let mut obligations : Option RuntimeObligationSequence := none
    let mut index := 0
    for value in values do
      let child ← decodeRuntimeValueM (node.child index value) s!"{path}[{index}]" domain tagCategory memo
      obligations := appendRuntimeObligations obligations child.obligations
      index := index + 1
    let summary := TypedValue.array #[]
    return ⟨summary, runtimeLocalObligations summary path obligations⟩
  | .obj _ =>
    if isSourceSpanJson j then
      let value := TypedValue.sourceSpan (← parseSourceSpan j path memo)
      return ⟨value, runtimeLocalObligations value path⟩
    if hasField j "span" && hasField j "scope" then
      let value := TypedValue.sourceInfo (← parseSourceInfo j path memo)
      return ⟨value, runtimeLocalObligations value path⟩
    let effectiveDomain := if domain == .any then
      match recognizedAutoDomain j with | some detected => detected | none => .any
      else domain
    let fields ← objectFields j
    let parentTag := match effectiveDomain with
      | .rvalue | .operand | .statement | .terminator => domainTag j effectiveDomain
      | _ => none
    let mut summaries := #[]
    let mut obligations : Option RuntimeObligationSequence := none
    for ((key, value), index) in fields.toList.zipIdx do
      let childPath := joinPath path key
      let nextDomain := childDomain effectiveDomain key
      let child ← if key == "user_type_projection" && parentTag == some "AscribeUserType" then do
          let projection ← parseUserTypeProjection value childPath
          pure ⟨.userTypeProjection projection,
            runtimeLocalObligations (.userTypeProjection projection) childPath⟩
        else if key == "operator" && (parentTag == some "BinaryOp" || optionalField j "kind" == some (.str "Overflow")) then do
          let (tag, status) ← parseOperatorTag value childPath
          let decoded := match binOpFromExportTag tag with
            | some op => TypedValue.binOperator op status
            | none => TypedValue.unknownBinOperator tag status
          pure ⟨decoded, runtimeLocalObligations decoded childPath⟩
        else if key == "operator" && parentTag == some "UnaryOp" then do
          let (tag, status) ← parseOperatorTag value childPath
          let decoded := match unOpFromExportTag tag with
            | some op => TypedValue.unOperator op status
            | none => TypedValue.unknownUnOperator tag status
          pure ⟨decoded, runtimeLocalObligations decoded childPath⟩
        else decodeRuntimeValueM (node.child index value) childPath nextDomain (typedEnumCategory? key path parentTag value) memo
      let isTagField := match effectiveDomain with
        | .statement | .terminator | .rvalue | .operand | .projection => key == "status" || key == "variant" || key == "kind"
        | _ => false
      let parentIsTagged := match effectiveDomain with
        | .any | .statementWrapper | .terminatorWrapper => tagCategory.isSome
        | _ => false
      let parentIsObject := match effectiveDomain with
        | .any | .statementWrapper | .terminatorWrapper => !tagCategory.isSome
        | _ => false
      let statusIssues := if key == "status" && (parentIsTagged || parentIsObject) then
        match child.summary with
        | .scalar (.str text) => (statusObligation? (parseStatus text) childPath).toList
        | _ => [⟨childPath, if parentIsTagged then "enum status must be a string" else "status field must be a string"⟩]
        else []
      let statusSequence := if statusIssues.isEmpty then none else some (.leaf statusIssues.toArray)
      let childSequence := appendRuntimeObligations statusSequence child.obligations
      if !isTagField then obligations := appendRuntimeObligations obligations childSequence
      if !isTagField && (runtimeSummaryKeys.contains key ||
          path.endsWith ".hir_id" && (key == "owner_def_id" || key == "local_id")) then
        let childSummary := match key, value with
          | "instance_id", .num _ => match value.getNat? with
            | .ok id => TypedValue.instanceRef id
            | .error _ => runtimeSummaryChild key child.summary
          | "local", .num _ => match value.getNat? with
            | .ok id => TypedValue.localRef id
            | .error _ => runtimeSummaryChild key child.summary
          | "block", .num _ | "target", .num _ | "otherwise", .num _
          | "real_target", .num _ | "imaginary_target", .num _ | "resume", .num _ =>
            match value.getNat? with
            | .ok id => TypedValue.blockRef id
            | .error _ => runtimeSummaryChild key child.summary
          | _, _ => runtimeSummaryChild key child.summary
        summaries := summaries.push (key, childSummary)
    let summary ← match effectiveDomain with
      | .statement => do
        let tag ← fieldString j "variant" path
        let status := parseStatus (← fieldString j "status" path)
        pure (TypedValue.statement (statementVariant tag) status summaries)
      | .terminator => do
        let tag ← fieldString j "variant" path
        let status := parseStatus (← fieldString j "status" path)
        pure (TypedValue.terminator (terminatorVariant tag) status summaries)
      | .rvalue => do
        let tag ← fieldString j "kind" path
        let status := parseStatus (← fieldString j "status" path)
        if tag == "BinaryOp" || tag == "UnaryOp" then
          let operator ← field j "operator" path
          let _ ← parseOperatorTag operator (joinPath path "operator")
        pure (TypedValue.rvalue (rvalueVariant tag) status summaries)
      | .operand => do
        let tag ← fieldString j "kind" path
        let status := parseStatus (← fieldString j "status" path)
        pure (TypedValue.operand (operandVariant tag) status summaries)
      | .projection => do
        let tag ← fieldString j "kind" path
        pure (TypedValue.projection (projectionVariant tag) summaries)
      | .any | .statementWrapper | .terminatorWrapper => do
        match tagCategory with
        | some category => pure (TypedValue.enumTag category (← parseInlineTag j path) summaries)
        | none => pure (TypedValue.object summaries)
    return ⟨summary, runtimeLocalObligations summary path obligations⟩
  | .str _ =>
    match tagCategory with
    | some category =>
      let value := TypedValue.enumTag category (← parseInlineTag j path) #[]
      return ⟨value, runtimeLocalObligations value path⟩
    | none =>
      let value := TypedValue.scalar j
      return ⟨value, runtimeLocalObligations value path⟩
  | _ =>
    let value := TypedValue.scalar j
    return ⟨value, runtimeLocalObligations value path⟩
end

def decodeRuntimeValue (node : JsonTraversalCache.Node) (path : String) (domain : Domain := .any)
    (tagCategory : Option TypedEnumTag := none) (memo : DecodeMemo := {}) : Except String RuntimeValueDecode := do
  (decodeRuntimeValueM node path domain tagCategory memo).run' {}

def jsonArray (j : Json) (path : String) : Except String (Array Json) :=
  j.getArr? |>.mapError fun e => s!"{path}: expected array ({e})"

def natArray (j : Json) (path : String) : Except String (Array Nat) := do
  let values ← jsonArray j path
  let mut out := #[]
  let mut index := 0
  for value in values do
    out := out.push (← value.getNat? |>.mapError fun e => s!"{path}[{index}]: expected unsigned integer ({e})")
    index := index + 1
  return out

def optionalNat (j : Json) (key path : String) : Except String (Option Nat) := do
  match optionalField j key with
  | none | some .null => pure none
  | some value => (value.getNat?).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

def optionalJson (j : Json) (key : String) : Option Json :=
  optionalField j key |>.filter (· != .null)

def parseTagged (j : Json) (path : String) : Except String TaggedNode := do
  let tag ← fieldString j "kind" path
  let status ← match optionalField j "status" with
    | none => pure .supported
    | some value => parseStatus <$> (value.getStr? |>.mapError fun e => s!"{joinPath path "status"}: expected string ({e})")
  return ⟨status, tag, j⟩

def parseAbiTag (j : Json) (path : String) : Except String TaggedNode := do
  match j with
  | .str tag => return ⟨.supported, tag, j⟩
  | .obj _ =>
    let tag ← match optionalField j "kind" with
      | some value => value.getStr? |>.mapError fun e => s!"{joinPath path "kind"}: expected string enum tag ({e})"
      | none => match optionalField j "variant" with
        | some value => value.getStr? |>.mapError fun e => s!"{joinPath path "variant"}: expected string enum tag ({e})"
        | none => throw s!"{path}: enum object is missing its kind tag"
    let status ← match optionalField j "status" with
      | none => pure .supported
      | some value => parseStatus <$> (value.getStr? |>.mapError fun e => s!"{joinPath path "status"}: expected string ({e})")
    return ⟨status, tag, j⟩
  | _ => throw s!"{path}: expected enum tag string or tagged object"

def layoutVariantsKind (tag : String) : LayoutVariantsKind :=
  match tag with
  | "single" => .single
  | "multiple" => .multiple
  | "empty" => .empty
  | other => .unknown other

def backendReprKind (tag : String) : BackendReprKind :=
  match tag with
  | "scalar" => .scalar
  | "scalar_pair" => .scalarPair
  | "memory" => .memory
  | "simd_vector" => .simdVector
  | "scalable_simd_vector" => .scalableSimdVector
  | other => .unknown other

def optionalNatBefore (j : Json) (key path : String) : Except String (Option Nat) := do
  match optionalField j key with
  | none | some .null => pure none
  | some value => (value.getNat?).map some |>.mapError fun e => s!"{joinPath path key}: expected unsigned integer or null ({e})"

def parsePrimitiveLayout (j : Json) (path : String) : Except String PrimitiveLayout := do
  let tag ← fieldString j "kind" path
  let kind := match tag with
    | "integer" => .integer
    | "float" => .float
    | "pointer" => .pointer
    | other => .unknown other
  let integerKindText ← optionalString j "integer_kind" path
  let integerKind := integerKindText.map integerTypeTag
  let signed ← match optionalField j "signed" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "signed"}: expected boolean ({e})"
  let floatKindText ← optionalString j "float_kind" path
  let floatKind := floatKindText.map floatTypeTag
  let addressSpace ← optionalNatBefore j "address_space" path
  return {
    kind := kind
    sizeBytes := ← fieldNat j "size_bytes" path
    integerKind := integerKind
    signed := signed
    floatKind := floatKind
    addressSpace := addressSpace
    payload := j
  }

/-- Exact compiler u128 encoding; preserve legacy JSON naturals while allowing
full-width decimal strings that serde_json cannot represent as numbers. -/
def parseU128Natural (j : Json) (path : String) : Except String Nat := do
  let value ← match j with
    | .str text => do
      unless !text.isEmpty && text.toList.all Char.isDigit do throw s!"{path}: expected exact unsigned decimal string"
      let some value := text.toNat? | throw s!"{path}: invalid unsigned decimal"
      pure value
    | _ => j.getNat? |>.mapError fun error => s!"{path}: expected unsigned integer ({error})"
  unless value < 2^128 do throw s!"{path}: u128 overflow"
  pure value

def parseScalarLayout (j : Json) (path : String) : Except String ScalarLayout := do
  let tag ← fieldString j "kind" path
  let kind := match tag with
    | "initialized" => .initialized
    | "union" => .union
    | other => .unknown other
  let range ← match optionalJson j "valid_range" with
    | none => pure none
    | some value => pure (some (← parseU128Natural (← field value "start" (joinPath path "valid_range")) (joinPath path "valid_range.start"), ← parseU128Natural (← field value "end" (joinPath path "valid_range")) (joinPath path "valid_range.end")))
  return {
    kind := kind
    primitive := ← parsePrimitiveLayout (← field j "primitive" path) (joinPath path "primitive")
    validRange := range
    payload := j
  }

def parseBackendRepr (j : Json) (path : String) : Except String BackendRepr := do
  let tag ← fieldString j "kind" path
  let kind := backendReprKind tag
  let scalar ← match optionalJson j "scalar" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "scalar")))
  let first ← match optionalJson j "first" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "first")))
  let second ← match optionalJson j "second" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "second")))
  let element ← match optionalJson j "element" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "element")))
  let sized ← match optionalField j "sized" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "sized"}: expected boolean ({e})"
  let secondOffsetBytes ← optionalNatBefore j "second_offset_bytes" path
  let laneCount ← optionalNatBefore j "lane_count" path
  let vectorCount ← optionalNatBefore j "vector_count" path
  match kind with
  | .scalar => if scalar.isNone then throw s!"{path}: scalar backend representation is missing scalar data"
  | .scalarPair =>
    if first.isNone || second.isNone || secondOffsetBytes.isNone then
      throw s!"{path}: scalar-pair backend representation is incomplete"
  | .memory => if sized.isNone then throw s!"{path}: memory backend representation is missing `sized`"
  | .simdVector | .scalableSimdVector =>
    if element.isNone || laneCount.isNone then throw s!"{path}: SIMD backend representation is incomplete"
  | .unknown _ => pure ()
  return {
    kind := kind
    sized := sized
    scalar := scalar
    first := first
    second := second
    secondOffsetBytes := secondOffsetBytes
    element := element
    laneCount := laneCount
    vectorCount := vectorCount
    payload := j
  }

def parseFieldShape (j : Json) (path : String) : Except String FieldShape := do
  let tag ← fieldString j "kind" path
  let kind := match tag with
    | "primitive" => .primitive
    | "union" => .union
    | "array" => .array
    | "arbitrary" => .arbitrary
    | other => .unknown other
  let fieldCount ← optionalNatBefore j "field_count" path
  let offsetBytes ← optionalNatBefore j "offset_bytes" path
  let strideBytes ← optionalNatBefore j "stride_bytes" path
  let offsetsBytes ← match optionalJson j "offsets_bytes" with
    | none => pure #[]
    | some value => natArray value (joinPath path "offsets_bytes")
  let memoryOrder ← match optionalJson j "memory_order" with
    | none => pure #[]
    | some value => natArray value (joinPath path "memory_order")
  let fieldCountValue := match fieldCount with | some count => count | none => 0
  match kind with
  | .primitive => pure ()
  | .union => if fieldCount.isNone || offsetBytes.isNone then throw s!"{path}: union field shape is incomplete"
  | .array => if fieldCount.isNone || strideBytes.isNone then throw s!"{path}: array field shape is incomplete"
  | .arbitrary =>
    if fieldCount.isNone || offsetsBytes.size != fieldCountValue || memoryOrder.size != fieldCountValue then
      throw s!"{path}: arbitrary field shape count/offset/order mismatch"
  | .unknown _ => pure ()
  return {
    kind := kind
    fieldCount := fieldCountValue
    offsetBytes := offsetBytes
    strideBytes := strideBytes
    offsetsBytes := offsetsBytes
    memoryOrder := memoryOrder
    payload := j
  }

def parseLayoutVariant (j : Json) (path : String) : Except String LayoutVariant := do
  return {
    variantIndex := ← fieldNat j "variant_index" path
    sizeBytes := ← fieldNat j "size_bytes" path
    backendRepr := ← parseBackendRepr (← field j "backend_repr" path) (joinPath path "backend_repr")
    fieldOffsetsBytes := ← natArray (← field j "field_offsets_bytes" path) (joinPath path "field_offsets_bytes")
    uninhabited := ← fieldBool j "uninhabited" path
    payload := j
  }

def decimalNat (text path : String) : Except String Nat := do
  if text.isEmpty then throw s!"{path}: expected a nonempty unsigned decimal integer"
  let mut value := 0
  for digit in text.toList do
    if digit < '0' || digit > '9' then throw s!"{path}: expected an unsigned decimal integer"
    value := value * 10 + digit.toNat - '0'.toNat
  return value

def parseTagEncoding (j : Json) (path : String) : Except String TagEncoding := do
  match j with
  | .str legacy =>
    return ⟨.incomplete, .unknown s!"legacy_debug:{legacy}", none, none, none, j⟩
  | .obj _ =>
    let tag ← fieldString j "kind" path
    let status := parseStatus (← fieldString j "status" path)
    let kind := match tag with
      | "direct" => TagEncodingKind.direct
      | "niche" => TagEncodingKind.niche
      | other => TagEncodingKind.unknown other
    let untaggedVariant ← optionalNat j "untagged_variant" path
    let nicheVariants ← match optionalJson j "niche_variants" with
      | none => pure none
      | some range => pure (some (← fieldNat range "start" (joinPath path "niche_variants"), ← fieldNat range "end" (joinPath path "niche_variants")))
    let nicheStart ← match optionalField j "niche_start" with
      | none | some .null => pure none
      | some value =>
        let text ← value.getStr? |>.mapError fun e => s!"{joinPath path "niche_start"}: expected exact decimal string ({e})"
        pure (some (← decimalNat text (joinPath path "niche_start")))
    match kind with
    | .direct => pure ()
    | .niche =>
      if status == .supported && (untaggedVariant.isNone || nicheVariants.isNone || nicheStart.isNone) then
        throw s!"{path}: supported niche tag encoding is missing its range or start value"
    | .unknown _ => pure ()
    return ⟨status, kind, untaggedVariant, nicheVariants, nicheStart, j⟩
  | _ => throw s!"{path}: expected structured tag encoding"

def parseVariantsLayout (j : Json) (path : String) : Except String VariantsLayout := do
  let tag ← fieldString j "kind" path
  let kind := layoutVariantsKind tag
  let variantIndex ← optionalNatBefore j "variant_index" path
  let scalarTag ← match optionalJson j "tag" with
    | none => pure none
    | some value => pure (some (← parseScalarLayout value (joinPath path "tag")))
  let tagEncoding ← match optionalJson j "tag_encoding" with
    | none => pure none
    | some value => pure (some (← parseTagEncoding value (joinPath path "tag_encoding")))
  let tagFieldIndex ← optionalNatBefore j "tag_field_index" path
  let variantsJson ← match optionalJson j "variants" with
    | none => pure #[]
    | some value => jsonArray value (joinPath path "variants")
  let mut variants := #[]
  for (value, index) in variantsJson.toList.zipIdx do
    variants := variants.push (← parseLayoutVariant value s!"{joinPath path "variants"}[{index}]")
  match kind with
  | .single => if variantIndex.isNone then throw s!"{path}: single-variant layout is missing variant_index"
  | .multiple =>
    if scalarTag.isNone || tagEncoding.isNone || tagFieldIndex.isNone || variants.isEmpty then
      throw s!"{path}: multi-variant layout is missing tag or variant data"
  | .empty => pure ()
  | .unknown _ => pure ()
  return {
    kind := kind
    variantIndex := variantIndex
    tag := scalarTag
    tagEncoding := tagEncoding
    tagFieldIndex := tagFieldIndex
    variants := variants
    payload := j
  }

def parseLayoutUncached (j : Json) (path : String) : Except String Layout := do
  if (j.getObjVal? "$lean_miri_shared_ref").isOk then
    throw s!"{path}: shared layout reference requires a shared_payloads catalog"
  let statusText ← fieldString j "status" path
  let status := parseStatus statusText
  let kind := match asTag? j "kind" with
    | some "layout_query_error" => .layoutQueryError
    | some "layout" | none => .layout
    | some value => .unknown value
  let offsets ← if status == .supported then
    natArray (← field j "field_offsets_bytes" path) (joinPath path "field_offsets_bytes")
    else match optionalJson j "field_offsets_bytes" with
      | none => pure #[]
      | some value => natArray value (joinPath path "field_offsets_bytes")
  let variants ← match optionalJson j "variants" with
    | none => pure none
    | some value => pure (some (← parseTagged value (joinPath path "variants")))
  let backend ← match optionalJson j "backend_repr" with
    | none => pure none
    | some value => pure (some (← parseTagged value (joinPath path "backend_repr")))
  let fields ← match optionalJson j "fields" with
    | none => pure none
    | some value => pure (some (← parseFieldShape value (joinPath path "fields")))
  let variantsLayout ← match optionalJson j "variants" with
    | none => pure none
    | some value => pure (some (← parseVariantsLayout value (joinPath path "variants")))
  let backendRepresentation ← match optionalJson j "backend_repr" with
    | none => pure none
    | some value => pure (some (← parseBackendRepr value (joinPath path "backend_repr")))
  let sizeBytes ← optionalNat j "size_bytes" path
  let abiAlignBytes ← optionalNat j "abi_align_bytes" path
  let unadjustedAbiAlignBytes ← optionalNat j "unadjusted_abi_align_bytes" path
  let variantsKind := variants.map fun value => layoutVariantsKind value.tag
  let backendReprKind := backend.map fun value => backendReprKind value.tag
  if status == .supported && (sizeBytes.isNone || abiAlignBytes.isNone || unadjustedAbiAlignBytes.isNone) then
    throw s!"{path}: supported layout is missing size/alignment fields"
  if status == .supported && (fields.isNone || variantsLayout.isNone || backendRepresentation.isNone) then
    throw s!"{path}: supported layout is missing field/variant/backend representation data"
  match fields with
  | some fieldShape =>
    if fieldShape.fieldCount != offsets.size then
      throw s!"{path}: field shape count does not match field_offsets_bytes"
  | none => pure ()
  return {
    status := status
    kind := kind
    sizeBytes := sizeBytes
    abiAlignBytes := abiAlignBytes
    unadjustedAbiAlignBytes := unadjustedAbiAlignBytes
    fieldOffsetsBytes := offsets
    fields := fields
    variantsLayout := variantsLayout
    backendRepresentation := backendRepresentation
    variantsKind := variantsKind
    backendReprKind := backendReprKind
    variants := variants
    backendRepr := backend
    payload := j
  }

def parseLayout (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String Layout := do
  match memo.layouts[j]? with
  | some value => pure value
  | none => parseLayoutUncached j path

def isLayoutPayload (j : Json) : Bool :=
  hasField j "status" && hasField j "field_offsets_bytes"

/-- JSON equality and hashing are only used as memo keys for canonical object
trees. In particular, never cache a Raw object whose inorder keys are not
strictly increasing, since malformed raw object trees can violate BEq symmetry. -/
partial def hasCanonicalJsonObjectKeys : Json → Bool
  | .obj fields => Id.run do
    let mut previous? : Option String := none
    for (key, value) in fields.toList do
      if let some previous := previous? then
        unless previous < key do return false
      if !hasCanonicalJsonObjectKeys value then return false
      previous? := some key
    return true
  | .arr values => values.all hasCanonicalJsonObjectKeys
  | _ => true

def collectSharedDecodeMemo (j : Json) (path : String) (memo : DecodeMemo)
    : DecodeMemo := Id.run do
  let key := j
  let mut memo := memo
  if isSourceSpanJson j && hasCanonicalJsonObjectKeys j && memo.sourceSpans[key]?.isNone then
    if let .ok value := parseSourceSpanUncached j path then
      memo := { memo with sourceSpans := memo.sourceSpans.insert key value }
  else if isLayoutPayload j && hasCanonicalJsonObjectKeys j && memo.layouts[key]?.isNone then
    if let .ok value := parseLayoutUncached j path then
      memo := { memo with layouts := memo.layouts.insert key value }
  return memo

def sharedDecodeMemo (nodes : Array Json) : DecodeMemo := Id.run do
  let mut memo : DecodeMemo := {}
  for (node, index) in nodes.toList.zipIdx do
    memo := collectSharedDecodeMemo node s!"$.shared_payloads.nodes[{index}]" memo
  return memo

def compilerFunctionAbiDecodeMemo (nodes : Array Json) : DecodeMemo := Id.run do
  let mut memo : DecodeMemo := {}
  for (node, index) in nodes.toList.zipIdx do
    if !isSourceSpanJson node && isLayoutPayload node && hasCanonicalJsonObjectKeys node then
      if let .ok layout := parseLayoutUncached node s!"$.shared_payloads.nodes[{index}]" then
        memo := { memo with layouts := memo.layouts.insert node layout }
  return memo

/-- Opaque success-only layout memo for repeated decoding of compiler FnAbi
payloads from one shared-payload node table. The constructor ensures
callers can prepare only the decoder's checked memo representation. -/
structure CompilerFunctionAbiMemo where
  private mk ::
  private memo : DecodeMemo

/-- Prepare a reusable FnAbi decoder memo from a runtime's shared payloads.
Malformed layouts are deliberately not cached, preserving occurrence paths. -/
def prepareCompilerFunctionAbiMemo (nodes : Array Json) : CompilerFunctionAbiMemo :=
  ⟨compilerFunctionAbiDecodeMemo nodes⟩

def parseFunctionSignature (j : Json) (path : String) : Except String FunctionSignature := do
  let inputsJson ← arrayField j "inputs" path
  let mut inputs := #[]
  let mut index := 0
  for input in inputsJson do
    let id ← match isTypeRef input with
      | some id => pure id
      | none => throw s!"{joinPath path "inputs"}[{index}]: expected type reference"
    inputs := inputs.push id
    index := index + 1
  let outputJson ← field j "output" path
  let output ← match isTypeRef outputJson with
    | some id => pure id
    | none => throw s!"{joinPath path "output"}: expected type reference"
  let abiJson ← field j "abi" path
  let unwind ← match optionalField abiJson "unwind" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath (joinPath path "abi") "unwind"}: expected boolean or null ({e})"
  let externAbi : ExternAbi := {
    kind := ← parseAbiTag abiJson (joinPath path "abi")
    unwind := unwind
    sourceSpelling := ← optionalString abiJson "source_spelling" (joinPath path "abi")
    payload := abiJson
  }
  return {
    inputs := inputs
    output := output
    safety := ← parseAbiTag (← field j "safety" path) (joinPath path "safety")
    abi := externAbi
    cVariadic := ← fieldBool j "c_variadic" path
  }

def decodeCompilerPredicateEvidence (j : Json) : Except String CompilerPredicateEvidence := do
  let normalization ← field j "normalization" "$predicate"
  let normalized ← match ← field normalization "value" "$predicate.normalization" with
    | .null => pure none
    | value => value.getNat?.map some
  pure {
    id := ← fieldNat j "predicate_id" "$predicate"
    typingEnvironment := ← fieldString j "typing_env" "$predicate"
    stableKey := ← fieldNat j "stable_key" "$predicate"
    autoTrait := ← fieldBool j "auto_trait" "$predicate"
    normalizationStatus := parseStatus (← fieldString normalization "status" "$predicate.normalization")
    normalizedId := normalized
    original := ← field j "original" "$predicate"
    payload := j }

/-- Decode all source PatternKind branches; unknown kinds fail explicitly. -/
partial def decodeCompilerPattern (j : Json) : Except String CompilerPattern := do
  unless (← fieldString j "status" "$pattern") == "supported" do throw "unsupported compiler pattern"
  match ← fieldString j "kind" "$pattern" with
  | "range" => return .range (← field j "start" "$pattern") (← field j "end" "$pattern")
  | "or" => return .or (← (← arrayField j "patterns" "$pattern").mapM decodeCompilerPattern)
  | "not_null" => pure .notNull
  | _ => throw "unknown compiler PatternKind"

/-- Preserve the compiler query's exact type and typing-environment key. -/
def decodeTypeCompilerFacts (j : Json) (path : String := "$compiler_facts") : Except String TypeCompilerFacts := do
  let some inputType := isTypeRef (← field j "input_type" path) | throw "compiler fact input_type is not a type reference"
  let mut booleans := #[]
  for (name,value) in ← objectFields (← field j "boolean_queries" path) do
    let result ← match ← field value "value" path with
      | .null => pure none
      | value => value.getBool?.map some
    booleans := booleans.push (name, {
      status := parseStatus (← fieldString value "status" path), value := result,
      reason := ← optionalString value "reason" path, payload := value })
  let mut types := #[]
  for (name,value) in ← objectFields (← field j "type_queries" path) do
    let result ← match ← field value "value" path with
      | .null => pure none
      | value => match isTypeRef value with
        | some id => pure (some id)
        | none => throw "compiler type query value is not a type reference or null"
    types := types.push (name, {
      status := parseStatus (← fieldString value "status" path), value := result,
      reason := ← optionalString value "reason" path, payload := value })
  let (captureNames,captureStatus) ← match optionalField j "capture_names" with
    | none => pure (none,none)
    | some query => do
      let status := parseStatus (← fieldString query "status" path)
      let names ← match ← field query "value" path with
        | .null => pure none
        | .arr names => (names.mapM fun (name : Json) => match name with
            | .null => pure none
            | name => name.getStr?.map some).map some
        | _ => throw "capture_names must be null or array"
      pure (names,some status)
  pure {
    captureNames := captureNames, captureNamesStatus := captureStatus,
    typingEnvironment := ← fieldString j "typing_env" path, inputTypeId := inputType,
    booleanQueries := booleans, typeQueries := types,
    adtPayload := match ← field j "adt" path with | .null => none | value => some value,
    payload := j }

def parseTypeNode (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String TypeNode := do
  let shape ← field j "shape" path
  let shapeStatus := parseStatus (← fieldString shape "status" (joinPath path "shape"))
  let shapeKindText ← fieldString shape "kind" (joinPath path "shape")
  let signedKindText ← optionalString shape "signed_kind" (joinPath path "shape")
  let unsignedKindText ← optionalString shape "unsigned_kind" (joinPath path "shape")
  let floatKindText ← optionalString shape "float_kind" (joinPath path "shape")
  let adtKindText ← optionalString shape "adt_kind" (joinPath path "shape")
  let shapeMetadata : TypeShapeMetadata := {
    signedKind := signedKindText.map integerTypeTag
    unsignedKind := unsignedKindText.map integerTypeTag
    floatKind := floatKindText.map floatTypeTag
    adtKind := adtKindText.map adtKindTag
  }
  let signature ← match optionalJson shape "signature" with
    | none => pure none
    | some signature => pure (some (← parseFunctionSignature signature (joinPath path "shape.signature")))
  return {
    pattern := ← match optionalField shape "pattern" with
      | none => pure none
      | some value => (decodeCompilerPattern value).map some
    compilerFacts := ← match optionalField j "compiler_facts" with
      | none => pure none
      | some value => (decodeTypeCompilerFacts value (joinPath path "compiler_facts")).map some
    id := ← fieldNat j "type_id" path
    display := ← fieldString j "display" path
    shapeStatus := shapeStatus
    shapeKind := typeShapeKind shapeKindText
    shapeMetadata := shapeMetadata
    signature := signature
    layout := ← parseLayout (← field j "layout" path) (joinPath path "layout") memo
    payload := j
  }

def hexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def validHex (value : String) : Bool := value.toList.all hexDigit && value.length % 2 == 0

def parseInitRange (j : Json) (path : String) : Except String InitRange := do
  let state ← fieldString j "state" path
  let initialized ← match state with
    | "initialized" => pure true
    | "uninitialized" => pure false
    | _ => throw s!"{joinPath path "state"}: unrecognized initialization state `{state}`"
  let first ← fieldNat j "start_bytes" path
  let last ← fieldNat j "end_bytes_exclusive" path
  if last < first then throw s!"{path}: initialization range has end before start"
  return ⟨initialized, first, last⟩

def parseRelocation (j : Json) (path : String) : Except String Relocation := do
  let targetRef ← field j "target" path
  let target ← match isAllocationRef targetRef with
    | some id => pure id
    | none => throw s!"{joinPath path "target"}: expected allocation reference object"
  -- Export IDs are zero-based and compilation-local.  The public CTFE
  -- provenance record requires a nonzero AllocId, so use the reversible +1
  -- embedding here and retain the original export ID separately in `target`.
  let leanAllocId ← match Miri.Memory.AllocId.ofUInt64 (UInt64.ofNat (target + 1)) with
    | some id => pure id
    | none => throw s!"{joinPath path "target"}: export allocation ID cannot be represented as a nonzero CTFE identity"
  let immutable ← fieldBool j "immutable" path
  let sharedRef ← fieldBool j "shared_ref" path
  let ctfeProvenance ← match Miri.Memory.CtfeProvenance.fromParts (leanAllocId, immutable, sharedRef) with
    | .ok provenance => pure provenance
    | .error _ => throw s!"{path}: invalid CTFE provenance flags or allocation-ID width"
  let encoded ← fieldString j "target_offset_encoded_bytes" path
  if !validHex encoded then throw s!"{joinPath path "target_offset_encoded_bytes"}: malformed hexadecimal bytes"
  return {
    storageOffsetBytes := ← fieldNat j "storage_offset_bytes" path
    target := target
    targetOffsetEncodedBytes := encoded
    immutable := immutable
    sharedRef := sharedRef
    ctfeProvenance := ctfeProvenance
  }

def parseAllocationMemory (j : Json) (path : String) : Except String AllocationMemory := do
  let bytes ← fieldString j "bytes_hex" path
  if !validHex bytes then throw s!"{joinPath path "bytes_hex"}: malformed hexadecimal bytes"
  let rangesJson ← arrayField j "initialization_ranges" path
  let mut ranges := #[]
  let mut index := 0
  for value in rangesJson do
    ranges := ranges.push (← parseInitRange value s!"{joinPath path "initialization_ranges"}[{index}]")
    index := index + 1
  let relocJson ← arrayField j "relocations" path
  let mut relocations := #[]
  index := 0
  for value in relocJson do
    relocations := relocations.push (← parseRelocation value s!"{joinPath path "relocations"}[{index}]")
    index := index + 1
  let size := ← fieldNat j "size_bytes" path
  if bytes.length / 2 != size then throw s!"{joinPath path "bytes_hex"}: byte buffer length does not equal size_bytes"
  let mut cursor := 0
  for chunk in ranges do
    if chunk.startBytes != cursor then throw s!"{joinPath path "initialization_ranges"}: ranges overlap or leave a gap"
    if chunk.endBytesExclusive > size then throw s!"{joinPath path "initialization_ranges"}: range exceeds allocation size"
    cursor := chunk.endBytesExclusive
  if cursor != size then throw s!"{joinPath path "initialization_ranges"}: ranges do not cover the allocation"
  for relocation in relocations do
    if relocation.storageOffsetBytes + relocation.targetOffsetEncodedBytes.length / 2 > size then
      throw s!"{joinPath path "relocations"}: relocation's encoded pointer bytes exceed allocation size"
  let alignBytes ← fieldNat j "align_bytes" path
  if alignBytes == 0 then throw s!"{joinPath path "align_bytes"}: allocation alignment must be nonzero"
  return {
    sizeBytes := size
    alignBytes := alignBytes
    mutability := match ← fieldString j "mutability" path with
      | "mutable" => .mutable
      | "immutable" => .immutable
      | other => .unknown other
    bytesHex := bytes
    initializationRanges := ranges
    relocations := relocations
  }

def allocationKind (kind : String) : AllocationKind :=
  match kind with
  | "memory" => .memory
  | "function" => .function
  | "static" => .static
  | "vtable" => .vtable
  | "type_id" => .typeId
  | "" => .unknown
  | other => .other other

def parseDefinitionId (j : Json) (path : String) : Except String DefinitionId := do
  return ⟨← fieldNat j "crate" path, ← fieldNat j "index" path⟩

def parseSelectedScope (j : Json) (path : String) : Except String SelectedScope := do
  let kind ← fieldString j "kind" path
  let statusText ← fieldString j "status" path
  let rootsJson ← arrayField j "roots" path
  let mut roots := #[]
  for (root, index) in rootsJson.toList.zipIdx do
    let rootPath := s!"{joinPath path "roots"}[{index}]"
    let defPath ← fieldString root "def_path" rootPath
    if defPath.isEmpty then throw s!"{joinPath rootPath "def_path"}: selected root path cannot be empty"
    roots := roots.push ⟨defPath, ← parseDefinitionId (← field root "def_id" rootPath) (joinPath rootPath "def_id")⟩
  if roots.toList.eraseDups.length != roots.size then throw s!"{joinPath path "roots"}: duplicate selected roots"
  let unresolvedJson ← arrayField j "unresolved_obligations" path
  let mut unresolved := #[]
  let mut evidence := #[]
  for (entry, index) in unresolvedJson.toList.zipIdx do
    let entryPath := s!"{joinPath path "unresolved_obligations"}[{index}]"
    match entry with
    | .str message =>
      unresolved := unresolved.push message
      evidence := evidence.push ⟨entryPath,message⟩
    | .obj _ =>
      let sourcePath ← fieldString entry "path" entryPath
      let status ← fieldString entry "status" entryPath
      let kind ← fieldString entry "kind" entryPath
      let reason ← fieldString entry "reason" entryPath
      let message := s!"{status} {kind}: {reason}"
      unresolved := unresolved.push message
      evidence := evidence.push ⟨sourcePath,message⟩
    | _ => throw s!"{entryPath}: expected string or structured source obligation"
  return {
    kind := kind
    statusText := statusText
    status := parseStatus statusText
    semantics := ← fieldString j "semantics" path
    roots := roots
    unresolvedObligations := unresolved
    unresolvedEvidence := evidence
    payload := j
  }

def vtablePredicateKind (tag : String) : VtablePredicateKind :=
  match tag with
  | "trait" => .trait
  | "auto_trait" => .autoTrait
  | "projection" => .projection
  | other => .unknown other

def parseVtablePredicate (j : Json) (path : String) : Except String VtablePredicate := do
  let tag ← fieldString j "kind" path
  let definitionId ← match optionalJson j "def_id" with
    | none => pure none
    | some value => pure (some (← parseDefinitionId value (joinPath path "def_id")))
  let definitionPath ← optionalString j "def_path" path
  let genericArgs ← match optionalJson j "generic_args" with
    | none => pure none
    | some value => pure (some (← decodeValue value (joinPath path "generic_args")))
  return {
    kind := vtablePredicateKind tag
    status := parseStatus (← fieldString j "status" path)
    definitionId := definitionId
    definitionPath := definitionPath
    genericArgs := genericArgs
    payload := j
  }

def vtableEntryKind (tag : String) : VtableEntryKind :=
  match tag with
  | "drop_in_place_null" => .dropInPlaceNull
  | "drop_in_place" => .dropInPlace
  | "size_bytes" => .sizeBytes
  | "align_bytes" => .alignBytes
  | "vacant" => .vacant
  | "method" => .method
  | "supertrait_vtable_pointer" => .supertraitVtablePointer
  | other => .unknown other

def parseVtableEntry (j : Json) (path : String) : Except String VtableEntry := do
  let tag ← fieldString j "kind" path
  let definitionId ← match optionalJson j "def_id" with
    | none => pure none
    | some value => pure (some (← parseDefinitionId value (joinPath path "def_id")))
  let traitDefinitionId ← match optionalJson j "trait_def_id" with
    | none => pure none
    | some value => pure (some (← parseDefinitionId value (joinPath path "trait_def_id")))
  let allocationId ← match optionalJson j "allocation" with
    | none => pure none
    | some value => match isAllocationRef value with
      | some id => pure (some id)
      | none => throw s!"{joinPath path "allocation"}: expected allocation reference"
  let genericArgs ← match optionalJson j "generic_args" with
    | none => pure none
    | some value => pure (some (← decodeValue value (joinPath path "generic_args")))
  return {
    kind := vtableEntryKind tag
    status := parseStatus (← fieldString j "status" path)
    instanceId := ← optionalNat j "instance_id" path
    definitionId := definitionId
    definitionPath := ← optionalString j "def_path" path
    allocationId := allocationId
    traitDefinitionId := traitDefinitionId
    traitDefinitionPath := ← optionalString j "trait_def_path" path
    genericArgs := genericArgs
    payload := j
  }

/-- Decode a source `tcx.vtable_entries` row retained outside a GlobalAlloc
image. Runtime-created vtables use this exact metadata without borrowing the
CTFE probe's allocation identity. -/
def decodeVtableEntry (j : Json) (path : String := "$compiler_vtable_entry") :
    Except String VtableEntry := parseVtableEntry j path

/-- Decode compiler-query static metadata, retaining the original evidence. -/
def decodeStaticGlobalInfo (j : Json) (path : String := "$static_global_info") : Except String StaticGlobalInfo := do
  return {
    status := parseStatus (← fieldString j "status" path)
    sizeBytes := ← fieldNat j "size_bytes" path
    alignBytes := ← fieldNat j "align_bytes" path
    mutability := match ← fieldString j "mutability" path with
      | "mutable" => .mutable
      | "immutable" => .immutable
      | tag => .unknown tag
    isStatic := ← fieldBool j "is_static" path
    foreignItem := ← fieldBool j "is_foreign_item" path
    threadLocal := ← fieldBool j "thread_local" path
    payload := j
  }

def parseAllocation (j : Json) (path : String) : Except String AllocationNode := do
  let kindText ← fieldString j "kind" path
  let kind := allocationKind kindText
  let status := parseStatus (← fieldString j "status" path)
  let mut memory := none
  let mut data := none
  if status == .supported then
    match kind with
    | .memory =>
      let value ← parseAllocationMemory j path
      memory := some value
      data := some (.memory value)
    | .function =>
      let defId ← parseDefinitionId (← field j "instance_def_id" path) (joinPath path "instance_def_id")
      let args ← decodeValue (← field j "generic_args" path) (joinPath path "generic_args")
      data := some (.function {
        instanceId := ← fieldNat j "instance_id" path
        definitionId := defId
        definitionPath := ← fieldString j "instance_def_path" path
        genericArgs := args
        payload := j
      })
    | .static =>
      let globalInfo ← match optionalField j "global_info" with
        | none => pure none
        | some info => (decodeStaticGlobalInfo info (joinPath path "global_info")).map some
      let foreignItem := globalInfo.map (·.foreignItem) |>.getD false
      let initializer ← match optionalField j "initializer" with
        | some value => (parseAllocationMemory value (joinPath path "initializer")).map some
        | none => if foreignItem then pure none else throw s!"{joinPath path "initializer"}: non-foreign static is missing its initializer image"
      data := some (.static {
        globalInfo := globalInfo
        definitionId := ← parseDefinitionId (← field j "def_id" path) (joinPath path "def_id")
        definitionPath := ← fieldString j "def_path" path
        threadLocal := ← fieldBool j "thread_local" path
        initializer := initializer
        payload := j
      })
    | .vtable =>
      let predicatesJson ← arrayField j "predicates" path
      let entriesJson ← arrayField j "entries" path
      let mut predicates := #[]
      for (predicate, index) in predicatesJson.toList.zipIdx do
        predicates := predicates.push (← parseVtablePredicate predicate s!"{joinPath path "predicates"}[{index}]")
      let mut entries := #[]
      for (entry, index) in entriesJson.toList.zipIdx do
        entries := entries.push (← parseVtableEntry entry s!"{joinPath path "entries"}[{index}]")
      let typeRef ← field j "type" path
      let typeId ← match isTypeRef typeRef with
        | some id => pure id
        | none => throw s!"{joinPath path "type"}: expected type reference"
      data := some (.vtable {
        typeId := typeId
        sizeBytes := ← optionalNat j "size_bytes" path
        alignBytes := ← optionalNat j "align_bytes" path
        layoutStatus := parseStatus (← fieldString j "layout_status" path)
        predicates := predicates
        entries := entries
        payload := j
      })
    | .typeId =>
      let typeRef ← field j "type" path
      let typeId ← match isTypeRef typeRef with
        | some id => pure id
        | none => throw s!"{joinPath path "type"}: expected type reference"
      data := some (.typeId typeId)
    | .unknown | .other _ => pure ()
  return {
    id := ← fieldNat j "allocation_id" path
    sourceAllocId := ← do
      match ← optionalNat j "source_alloc_id" path with
      | none => pure none
      | some value =>
        if value == 0 || value >= 2^64 then
          throw s!"{joinPath path "source_alloc_id"}: expected a nonzero u64 rustc allocation identity"
        else pure (some (UInt64.ofNat value))
    status := status
    kind := kind
    memory := memory
    data := data
    payload := j
  }

def parseSourceAllocIdKind (value path : String) : Except String SourceAllocIdKind := do
  match value with
  | "dangling" => pure .dangling
  | "memory" => pure .memory
  | "function" => pure .function
  | "vtable" => pure .vtable
  | "static" => pure .static
  | "type_id" => pure .typeId
  | _ => throw s!"{path}: unknown source AllocId kind `{value}`"

def canonicalLowerHex (value : String) : Bool :=
  validHex value && value.toList.all (fun char =>
    (char >= '0' && char <= '9') || (char >= 'a' && char <= 'f'))

def allocationNodeMatchesSourceKind (sourceKind : SourceAllocIdKind)
    (nodeKind : AllocationKind) : Bool :=
  match sourceKind, nodeKind with
  | .memory, .memory | .function, .function | .vtable, .vtable
  | .static, .static | .typeId, .typeId => true
  | .static, .other "static_initializer_error" => true
  | _, _ => false

def parseSourceAllocIdDedupKind (value path : String) : Except String SourceAllocIdDedupKind := do
  match value with
  | "function" => pure .function
  | "vtable" => pure .vtable
  | "static" => pure .static
  | "type_id" => pure .typeId
  | "memory" | "memory_const_allocation" => pure .memory
  | "bytes" | "byte_memory" => pure .bytes
  | _ => throw s!"{path}: unknown source AllocId dedup key kind `{value}`"

def parseSourceAllocIdPoolRow (j : Json) (path : String) : Except String SourceAllocIdPoolRow := do
  let raw ← fieldNat j "source_alloc_id" path
  if raw == 0 || raw >= 2^64 then throw s!"{joinPath path "source_alloc_id"}: expected nonzero u64"
  let kind ← parseSourceAllocIdKind (← fieldString j "kind" path) (joinPath path "kind")
  let status ← match ← fieldString j "status" path with
    | "dangling" => pure SourceAllocIdStatus.dangling
    | "serialized" => pure .serialized
    | "opaque" => pure .opaque
    | value => throw s!"{joinPath path "status"}: unknown source AllocId pool status `{value}`"
  let allocationId ← optionalNatField j "allocation_id" path
  let opaqueAllocationId ← optionalNat j "opaque_allocation_id" path
  let (memoryMutability, memoryAlignBytes, memoryAllBytesInitialized, memoryHasProvenance) ←
    match kind with
    | .memory => do
      let mutability ← match ← fieldString j "memory_mutability" path with
        | "immutable" => pure MemoryMutability.immutable
        | "mutable" => pure .mutable
        | value => throw s!"{joinPath path "memory_mutability"}: unsupported value `{value}`"
      pure (some mutability,
        some (← fieldNat j "memory_align_bytes" path),
        some (← fieldBool j "memory_all_bytes_initialized" path),
        some (← fieldBool j "memory_has_provenance" path))
    | _ => pure (none,none,none,none)
  let byteImageHex ← optionalString j "byte_image_hex" path
  if let some image := byteImageHex then
    unless canonicalLowerHex image do throw s!"{joinPath path "byte_image_hex"}: expected canonical lowercase hexadecimal"
  let shapeIsValid := match kind, status, allocationId with
    | .dangling, .dangling, none => opaqueAllocationId.isNone
    | .memory, .serialized, some _ => opaqueAllocationId.isNone
    | .function, .serialized, some _ => opaqueAllocationId.isNone
    | .vtable, .serialized, some _ => opaqueAllocationId.isNone
    | .static, .serialized, some _ => opaqueAllocationId.isNone
    | .typeId, .serialized, some _ => opaqueAllocationId.isNone
    | .memory, .opaque, none => true
    | .function, .opaque, none => true
    | .vtable, .opaque, none => true
    | .static, .opaque, none => true
    | .typeId, .opaque, none => true
    | _, _, _ => false
  unless shapeIsValid do throw s!"{path}: inconsistent kind/status/allocation_id in source AllocId pool row"
  let byteEligible := kind == .memory && memoryMutability == some .immutable && memoryAlignBytes == some 1 &&
    memoryAllBytesInitialized == some true && memoryHasProvenance == some false
  match kind, byteEligible, byteImageHex with
  | .memory, true, some _ =>
    unless status == .serialized && allocationId.isSome do
      throw s!"{path}: eligible byte-memory key requires a serialized allocation node"
  | .memory, false, none => pure ()
  | .memory, _, _ => throw s!"{path}: inconsistent byte-memory eligibility and image"
  | _, _, none => pure ()
  | _, _, some _ => throw s!"{path}: byte-memory image is only valid for memory globals"
  pure ⟨UInt64.ofNat raw, kind, status, allocationId, opaqueAllocationId, memoryMutability, memoryAlignBytes,
    memoryAllBytesInitialized, memoryHasProvenance, byteImageHex⟩

def parseSourceAllocIdSaltResult (j : Json) (path : String) : Except String SourceAllocIdSaltResult := do
  let sourceId ← fieldNat j "source_alloc_id" path
  if sourceId == 0 || sourceId >= 2^64 then throw s!"{joinPath path "source_alloc_id"}: expected nonzero u64"
  let outcome ← match ← fieldString j "probe_result" path with
    | "preexisting_hit" => pure SourceAllocIdProbeOutcome.preexistingHit
    | "miss_reserved_by_probe" => pure .missReservedByProbe
    | value => throw s!"{joinPath path "probe_result"}: unknown probe result `{value}`"
  pure {
    salt := ← fieldNat j "salt" path
    allocationId := ← fieldNat j "allocation_id" path
    sourceAllocId := UInt64.ofNat sourceId
    outcome := outcome
  }

def parseSourceAllocIdDedupRow (j : Json) (path : String) : Except String SourceAllocIdDedupRow := do
  let keyKind ← parseSourceAllocIdDedupKind (← fieldString j "key_kind" path) (joinPath path "key_kind")
  let saltsJson ← arrayField j "salts" path
  let mut salts := #[]
  for (value, index) in saltsJson.toList.zipIdx do
    salts := salts.push (← parseSourceAllocIdSaltResult value s!"{path}.salts[{index}]")
  let byteImageHex ← optionalString j "bytes_hex" path
  if let some image := byteImageHex then
    unless canonicalLowerHex image do throw s!"{joinPath path "bytes_hex"}: expected canonical lowercase hexadecimal"
  let keyAllocationId ← fieldNat j "key_allocation_id" path
  match keyKind, byteImageHex with
  | .bytes, some _ => pure ()
  | .function, none => pure ()
  | .vtable, none => pure ()
  | .static, none => pure ()
  | .typeId, none => pure ()
  | .memory, none => pure ()
  | .bytes, none => throw s!"{joinPath path "bytes_hex"}: required for byte-image dedup key"
  | _, some _ => throw s!"{joinPath path "bytes_hex"}: only valid for byte-image dedup key"
  pure ⟨keyKind, keyAllocationId, byteImageHex, salts⟩

def parseCompilerAllocIdWorld (j : Json) (nodes : Array AllocationNode) : Except String CompilerAllocIdWorld := do
  unless (← fieldString j "schema" "$.compiler_alloc_id_world") == "rustc_alloc_id_world_v1" do
    throw "$.compiler_alloc_id_world.schema: unsupported source AllocId world schema"
  unless (← fieldString j "profile" "$.compiler_alloc_id_world") == "prepared_post_export" do
    throw "$.compiler_alloc_id_world.profile: unsupported source AllocId world profile"
  let path := "$.compiler_alloc_id_world"
  let frontier ← field j "frontier" path
  let lastNat ← fieldNat frontier "last_reserved_source_alloc_id" (joinPath path "frontier")
  let nextNat ← fieldNat frontier "next_source_alloc_id" (joinPath path "frontier")
  let sentinelNat ← fieldNat frontier "final_sentinel_source_alloc_id" (joinPath path "frontier")
  if lastNat == 0 || lastNat >= 2^64 then throw "$.compiler_alloc_id_world.frontier.last_reserved_source_alloc_id: expected nonzero u64"
  if nextNat == 0 || nextNat >= 2^64 then throw "$.compiler_alloc_id_world.frontier.next_source_alloc_id: expected nonzero u64"
  unless sentinelNat == lastNat && nextNat == lastNat + 1 do
    throw "$.compiler_alloc_id_world.frontier: sentinel, last reservation, and next counter disagree"
  let poolThrough ← fieldNat j "global_pool_complete_through" path
  unless poolThrough == lastNat do throw "$.compiler_alloc_id_world.global_pool_complete_through: does not equal frontier"
  let poolJson ← arrayField j "raw_pool" path
  unless poolJson.size == lastNat do throw "$.compiler_alloc_id_world.raw_pool: must contain exactly the raw ID prefix 1..=frontier"
  let mut nodeIndexByGraphId : Std.HashMap Nat Nat := {}
  let mut nodeIndexBySourceId : Std.HashMap Nat Nat := {}
  for (node, index) in nodes.toList.zipIdx do
    if nodeIndexByGraphId.contains node.id then throw "$.compiler_alloc_id_world: duplicate allocation graph identity"
    nodeIndexByGraphId := nodeIndexByGraphId.insert node.id index
    if let some sourceId := node.sourceAllocId then
      if nodeIndexBySourceId.contains sourceId.toNat then
        throw "$.compiler_alloc_id_world: duplicate source AllocId witness on allocation nodes"
      nodeIndexBySourceId := nodeIndexBySourceId.insert sourceId.toNat index
  let mut pool := #[]
  for (value, index) in poolJson.toList.zipIdx do
    let rowPath := s!"$.compiler_alloc_id_world.raw_pool[{index}]"
    let row ← parseSourceAllocIdPoolRow value rowPath
    unless row.sourceAllocId.toNat == index + 1 do
      throw s!"{rowPath}.source_alloc_id: pool rows must be ordered and contiguous from one"
    if row.status == .serialized then
      let some graphId := row.allocationId | throw s!"{rowPath}: serialized pool row lacks graph identity"
      let some nodeIndex := nodeIndexByGraphId[graphId]? | throw s!"{rowPath}.allocation_id: allocation node is absent"
      let some node := nodes[nodeIndex]? | throw s!"{rowPath}.allocation_id: allocation node index is absent"
      unless node.sourceAllocId == some row.sourceAllocId do throw s!"{rowPath}: source AllocId disagrees with allocation node witness"
      unless node.status == .supported do throw s!"{rowPath}: serialized source global lacks supported allocation status"
      let expectedKind := match row.kind with
        | .memory => AllocationKind.memory
        | .function => .function
        | .vtable => .vtable
        | .static => .static
        | .typeId => .typeId
        | .dangling => .unknown
      unless node.kind == expectedKind do throw s!"{rowPath}: source global kind disagrees with allocation node"
      let expectedData : Bool := match row.kind, node.data with
        | .memory, some (.memory _) => true
        | .function, some (.function _) => true
        | .vtable, some (.vtable _) => true
        | .static, some (.static _) => true
        | .typeId, some (.typeId _) => true
        | _, _ => false
      unless expectedData do throw s!"{rowPath}: serialized source global lacks matching typed payload"
      if row.kind == .memory then
        let some projectionMutability := row.memoryMutability | throw s!"{rowPath}: memory projection mutability is absent"
        let some projectionAlign := row.memoryAlignBytes | throw s!"{rowPath}: memory projection alignment is absent"
        let some projectionInitialized := row.memoryAllBytesInitialized | throw s!"{rowPath}: memory projection initialization status is absent"
        let some projectionProvenance := row.memoryHasProvenance | throw s!"{rowPath}: memory projection provenance status is absent"
        let some (.memory image) := node.data | throw s!"{rowPath}: serialized memory node has no memory image"
        let actualMutability := image.mutability
        let actualInitialized := image.initializationRanges.all (·.initialized)
        let actualProvenance := !image.relocations.isEmpty
        unless projectionMutability == actualMutability && projectionAlign == image.alignBytes &&
            projectionInitialized == actualInitialized && projectionProvenance == actualProvenance do
          throw s!"{rowPath}: source byte-key projection disagrees with serialized memory image"
        let actualByteEligible := actualMutability == .immutable && image.alignBytes == 1 &&
          actualInitialized && !actualProvenance
        if actualByteEligible then
          unless row.byteImageHex == some image.bytesHex do
            throw s!"{rowPath}: eligible byte-memory projection differs from serialized bytes"
        else unless row.byteImageHex.isNone do
          throw s!"{rowPath}: ineligible memory image must not publish a byte key"
    else if let some graphId := row.opaqueAllocationId then
      unless row.status == .opaque do throw s!"{rowPath}.opaque_allocation_id: only valid for opaque rows"
      let some nodeIndex := nodeIndexByGraphId[graphId]? | throw s!"{rowPath}.opaque_allocation_id: allocation node is absent"
      let some node := nodes[nodeIndex]? | throw s!"{rowPath}.opaque_allocation_id: allocation node index is absent"
      unless node.sourceAllocId == some row.sourceAllocId && node.status != .supported &&
          allocationNodeMatchesSourceKind row.kind node.kind do
        throw s!"{rowPath}.opaque_allocation_id: source witness does not identify an unsupported allocation of the same source kind"
    else if nodeIndexBySourceId.contains row.sourceAllocId.toNat then
      throw s!"{rowPath}: non-serialized source ID is attached to an allocation node"
    pool := pool.push row
  let some sentinel := pool[pool.size - 1]? | throw "$.compiler_alloc_id_world.raw_pool: sentinel row absent"
  unless sentinel.kind == .dangling && sentinel.status == .dangling && sentinel.allocationId.isNone do
    throw "$.compiler_alloc_id_world.raw_pool: final reserved sentinel must be dangling"
  for node in nodes do
    let some sourceId := node.sourceAllocId | throw "$.compiler_alloc_id_world: every imported allocation must carry an exact source_alloc_id witness"
    let some row := pool[sourceId.toNat - 1]? | throw "$.compiler_alloc_id_world: allocation witness lies outside captured raw prefix"
    if node.status == .supported then
      unless row.status == .serialized && row.allocationId == some node.id do
        throw "$.compiler_alloc_id_world: supported allocation node is not covered by exactly one serialized pool row"
    else unless row.status == .opaque && row.opaqueAllocationId == some node.id do
      throw "$.compiler_alloc_id_world: unsupported allocation node is not covered by its opaque pool row"
  let dedupJson ← arrayField j "dedup_catalog" path
  let mut dedup := #[]
  let mut byteRowByImage : Std.HashMap String Nat := {}
  let mut functionRowByInstance : Std.HashMap InstanceId Nat := {}
  let mut vtableRowsByType : Std.HashMap TypeId (Array (Array VtablePredicate)) := {}
  let mut staticDefinitionsSeen : Std.HashMap (Nat × Nat) Nat := {}
  let mut typeIdRowByType : Std.HashMap TypeId Nat := {}
  for (value, index) in dedupJson.toList.zipIdx do
    let rowPath := s!"$.compiler_alloc_id_world.dedup_catalog[{index}]"
    let row ← parseSourceAllocIdDedupRow value rowPath
    unless #[.bytes, .function, .vtable, .static, .typeId].contains row.keyKind do
      throw s!"{rowPath}.key_kind: dedup key family is not available in this prepared profile"
    let some keyIndex := nodeIndexByGraphId[row.keyAllocationId]? | throw s!"{rowPath}.key_allocation_id: selected key node is not serialized"
    let some keyNode := nodes[keyIndex]? | throw s!"{rowPath}.key_allocation_id: selected key index is absent"
    let expectedKeyKind := match row.keyKind with
      | .bytes => AllocationKind.memory
      | .function => .function
      | .vtable => .vtable
      | .static => .static
      | .typeId => .typeId
      | _ => .unknown
    unless keyNode.kind == expectedKeyKind && keyNode.status == .supported do
      throw s!"{rowPath}: selected key node has incompatible kind/status"
    let expectedSaltCount := if row.keyKind == .static || row.keyKind == .typeId then 1 else 32
    unless row.salts.size == expectedSaltCount do
      throw s!"{rowPath}.salts: selected dedup key has the wrong number of source salt results"
    let mut seenResultAllocations : Std.HashMap Nat Bool := {}
    for (saltResult, saltIndex) in row.salts.toList.zipIdx do
      let expectedSalt := if row.keyKind == .static || row.keyKind == .typeId then 0 else saltIndex
      unless saltResult.salt == expectedSalt do
        throw s!"{rowPath}.salts[{saltIndex}].salt: unexpected source salt for selected dedup key"
      if seenResultAllocations.contains saltResult.allocationId then
        throw s!"{rowPath}.salts[{saltIndex}]: duplicate result allocation across source salts"
      seenResultAllocations := seenResultAllocations.insert saltResult.allocationId true
      let some poolRow := pool[saltResult.sourceAllocId.toNat - 1]? | throw s!"{rowPath}.salts: result AllocId outside captured pool"
      unless poolRow.status == .serialized && poolRow.allocationId == some saltResult.allocationId do
        throw s!"{rowPath}.salts: result must resolve to its unique serialized allocation node"
      let some resultIndex := nodeIndexByGraphId[saltResult.allocationId]?
        | throw s!"{rowPath}.salts[{saltIndex}]: result allocation node is absent"
      let some resultNode := nodes[resultIndex]?
        | throw s!"{rowPath}.salts[{saltIndex}]: result node index is absent"
      unless resultNode.kind == expectedKeyKind && resultNode.status == .supported do
        throw s!"{rowPath}.salts[{saltIndex}]: result allocation has incompatible kind/status"
      if row.keyKind == .function then
        let some (.function keyFunction) := keyNode.data
          | throw s!"{rowPath}: function key witness lacks typed instance data"
        let some (.function resultFunction) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: function result lacks typed instance data"
        unless keyFunction.instanceId == resultFunction.instanceId &&
            keyFunction.definitionId == resultFunction.definitionId &&
            keyFunction.genericArgs == resultFunction.genericArgs do
          throw s!"{rowPath}.salts[{saltIndex}]: function result does not match the exact selected Instance key"
      if row.keyKind == .vtable then
        let some (.vtable keyVtable) := keyNode.data
          | throw s!"{rowPath}: vtable key witness lacks typed identity data"
        let some (.vtable resultVtable) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: vtable result lacks typed identity data"
        unless keyVtable.typeId == resultVtable.typeId && keyVtable.predicates == resultVtable.predicates do
          throw s!"{rowPath}.salts[{saltIndex}]: vtable result does not match the exact selected type/predicate key"
      if row.keyKind == .static then
        let some (.static keyStatic) := keyNode.data
          | throw s!"{rowPath}: static key witness lacks typed DefId data"
        let some (.static resultStatic) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: static result lacks typed DefId data"
        unless keyStatic.definitionId == resultStatic.definitionId do
          throw s!"{rowPath}.salts[{saltIndex}]: static result does not match the exact selected DefId key"
        unless saltResult.salt == 0 && saltResult.allocationId == row.keyAllocationId do
          throw s!"{rowPath}: static key must provide its exact salt-zero typed witness"
      if row.keyKind == .typeId then
        let some (.typeId keyType) := keyNode.data
          | throw s!"{rowPath}: TypeId key witness lacks typed Ty data"
        let some (.typeId resultType) := resultNode.data
          | throw s!"{rowPath}.salts[{saltIndex}]: TypeId result lacks typed Ty data"
        unless keyType == resultType do
          throw s!"{rowPath}.salts[{saltIndex}]: TypeId result does not match the exact selected Ty key"
        unless saltResult.salt == 0 && saltResult.allocationId == row.keyAllocationId do
          throw s!"{rowPath}: TypeId key must provide its exact salt-zero typed witness"
    if row.keyKind == .bytes then
      let some imageHex := row.byteImageHex | throw s!"{rowPath}: byte key lacks its exact image"
      let some (.memory image) := keyNode.data | throw s!"{rowPath}: byte key node has no memory image"
      let some keySourceId := keyNode.sourceAllocId | throw s!"{rowPath}: byte key node lacks a source identity"
      let some keyPoolRow := pool[keySourceId.toNat - 1]? | throw s!"{rowPath}: byte key node is absent from the source pool"
      unless keyPoolRow.memoryMutability == some .immutable && keyPoolRow.memoryAlignBytes == some 1 &&
          keyPoolRow.memoryAllBytesInitialized == some true && keyPoolRow.memoryHasProvenance == some false &&
          keyPoolRow.byteImageHex == some imageHex && keyNode.memory == some image && image.bytesHex == imageHex &&
          image.mutability == .immutable && image.alignBytes == 1 && image.relocations.isEmpty &&
          image.initializationRanges.all (·.initialized) do
        throw s!"{rowPath}: byte key image is not the exact immutable aligned initialized provenance-free source key"
      for saltResult in row.salts do
        let some resultIndex := nodeIndexByGraphId[saltResult.allocationId]?
          | throw s!"{rowPath}.salts: byte-key result node is absent"
        let some resultNode := nodes[resultIndex]? | throw s!"{rowPath}.salts: result node index is absent"
        let some (.memory resultImage) := resultNode.data
          | throw s!"{rowPath}.salts: byte-key result is not a memory global"
        unless resultImage.bytesHex == imageHex && resultImage.alignBytes == 1 &&
            resultImage.mutability == .immutable && resultImage.relocations.isEmpty &&
            resultImage.initializationRanges.all (·.initialized) do
          throw s!"{rowPath}.salts: byte-key result does not contain the exact queried byte image"
      let some imageHex := row.byteImageHex | throw s!"{rowPath}: byte key lacks its exact image"
      if byteRowByImage.contains imageHex then throw s!"{rowPath}: duplicate exact byte-image key"
      byteRowByImage := byteRowByImage.insert imageHex dedup.size
    else if row.keyKind == .function then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed function key carries an unexpected byte image"
      let some (.function keyFunction) := keyNode.data
        | throw s!"{rowPath}: function key witness lacks typed instance data"
      if functionRowByInstance.contains keyFunction.instanceId then
        throw s!"{rowPath}: duplicate exact function Instance key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero function result is not its typed key witness"
      functionRowByInstance := functionRowByInstance.insert keyFunction.instanceId dedup.size
    else if row.keyKind == .vtable then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed vtable key carries an unexpected byte image"
      let some (.vtable keyVtable) := keyNode.data
        | throw s!"{rowPath}: vtable key witness lacks typed identity data"
      let previous := vtableRowsByType[keyVtable.typeId]?.getD #[]
      if previous.contains keyVtable.predicates then
        throw s!"{rowPath}: duplicate exact compiler vtable type/predicate key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero vtable result is not its typed key witness"
      vtableRowsByType := vtableRowsByType.insert keyVtable.typeId (previous.push keyVtable.predicates)
    else if row.keyKind == .static then
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed static key carries an unexpected byte image"
      let some (.static keyStatic) := keyNode.data
        | throw s!"{rowPath}: static key witness lacks typed DefId data"
      let defKey := (keyStatic.definitionId.crateIndex, keyStatic.definitionId.index)
      if staticDefinitionsSeen.contains defKey then
        throw s!"{rowPath}: duplicate exact static DefId key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero static result is not its typed key witness"
      staticDefinitionsSeen := staticDefinitionsSeen.insert defKey dedup.size
    else
      unless row.byteImageHex.isNone do throw s!"{rowPath}: typed TypeId key carries an unexpected byte image"
      let some (.typeId keyType) := keyNode.data
        | throw s!"{rowPath}: TypeId key witness lacks typed Ty data"
      if typeIdRowByType.contains keyType then
        throw s!"{rowPath}: duplicate exact TypeId Ty key"
      unless (row.salts[0]?).map (·.allocationId) == some row.keyAllocationId do
        throw s!"{rowPath}: salt-zero TypeId result is not its typed key witness"
      typeIdRowByType := typeIdRowByType.insert keyType dedup.size
    dedup := dedup.push row
  for node in nodes do
    if node.status == .supported then
      if let some (.static static) := node.data then
        unless staticDefinitionsSeen.contains (static.definitionId.crateIndex, static.definitionId.index) do
          throw "$.compiler_alloc_id_world.dedup_catalog: selected source static node lacks its exact salt-zero key outcome"
      if let some (.typeId ty) := node.data then
        unless typeIdRowByType.contains ty do
          throw "$.compiler_alloc_id_world.dedup_catalog: selected TypeId node lacks its exact salt-zero key outcome"
  let mut completeFamilies := #[]
  let families ← arrayField j "complete_key_families" path
  for (family, index) in families.toList.zipIdx do
    let name ← family.getStr? |>.mapError fun _ => s!"$.compiler_alloc_id_world.complete_key_families[{index}]: expected string"
    unless name == "byte_memory" do
      throw s!"$.compiler_alloc_id_world.complete_key_families[{index}]: this decoder only recognizes the source-validated byte_memory family"
    let kind := SourceAllocIdDedupKind.bytes
    if completeFamilies.contains kind then throw "$.compiler_alloc_id_world.complete_key_families: duplicate key family"
    completeFamilies := completeFamilies.push kind
  unless completeFamilies.size == 1 && completeFamilies[0]? == some .bytes do
    throw "$.compiler_alloc_id_world.complete_key_families: prepared profile requires exactly byte_memory completeness"
  let unsupportedJson ← arrayField j "unsupported_key_families" path
  let mut unsupportedFamilies := #[]
  for (family, index) in unsupportedJson.toList.zipIdx do
    let name ← family.getStr? |>.mapError fun _ => s!"$.compiler_alloc_id_world.unsupported_key_families[{index}]: expected string"
    let kind ← parseSourceAllocIdDedupKind name s!"$.compiler_alloc_id_world.unsupported_key_families[{index}]"
    unless #[.function, .vtable, .static, .typeId, .memory].contains kind do
      throw s!"$.compiler_alloc_id_world.unsupported_key_families[{index}]: unknown or inapplicable unsupported family"
    if unsupportedFamilies.contains kind then throw "$.compiler_alloc_id_world.unsupported_key_families: duplicate family"
    if completeFamilies.contains kind then throw "$.compiler_alloc_id_world: key family is both complete and unsupported"
    unsupportedFamilies := unsupportedFamilies.push kind
  for required in #[SourceAllocIdDedupKind.function, .vtable, .static, .typeId, .memory] do
    unless unsupportedFamilies.contains required do
      throw "$.compiler_alloc_id_world.unsupported_key_families: function/vtable/static/type_id/memory_const_allocation must remain explicitly unsupported"
  for row in dedup do
    unless #[.bytes, .function, .vtable, .static, .typeId].contains row.keyKind do
      throw "$.compiler_alloc_id_world.dedup_catalog: unsupported selected key outcome family"
  if completeFamilies.contains .bytes then
    for row in pool do
      if row.kind == .memory then
        unless row.memoryMutability.isSome && row.memoryAlignBytes.isSome &&
            row.memoryAllBytesInitialized.isSome && row.memoryHasProvenance.isSome do
          throw "$.compiler_alloc_id_world.raw_pool: byte_memory completeness requires all source memory projection dimensions"
        let eligible := row.memoryMutability == some .immutable && row.memoryAlignBytes == some 1 &&
          row.memoryAllBytesInitialized == some true && row.memoryHasProvenance == some false
        if eligible then
          unless row.status == .serialized do
            throw "$.compiler_alloc_id_world.raw_pool: eligible byte-memory global is not serialized"
          let some imageHex := row.byteImageHex | throw "$.compiler_alloc_id_world.raw_pool: eligible byte key has no exact image"
          let some keyIndex := byteRowByImage[imageHex]? | throw "$.compiler_alloc_id_world.dedup_catalog: complete byte_memory family omits an eligible image"
          let some key := dedup[keyIndex]? | throw "$.compiler_alloc_id_world.dedup_catalog: key index is absent"
          unless key.salts.size == 32 && (List.range 32).all (fun salt => key.salts.any (·.salt == salt)) do
            throw "$.compiler_alloc_id_world.dedup_catalog: complete byte_memory family omits a full salt row for an eligible image"
  pure {
    lastReservedSourceAllocId := UInt64.ofNat lastNat
    nextSourceAllocId := UInt64.ofNat nextNat
    finalSentinelSourceAllocId := UInt64.ofNat sentinelNat
    rawPool := pool
    dedupCatalog := dedup
    completeKeyFamilies := completeFamilies
    unsupportedKeyFamilies := unsupportedFamilies
  }

/-- Revalidate allocation identity metadata against the exact retained raw
document. Public model records can be assembled or updated by callers, so the
prepared runtime must not trust the decoder's prior validation as a flag. -/
def validateCompilerAllocIdWorldRaw (raw : Json) (nodes : Array AllocationNode)
    (world : Option CompilerAllocIdWorld) : Except String Unit := do
  match optionalJson raw "compiler_alloc_id_world" with
  | none =>
    unless world.isNone do throw "source AllocId profile model is present but absent from its raw document"
  | some rawWorld =>
    let some world := world | throw "raw document contains a source AllocId profile absent from its typed model"
    let allocationsJson ← arrayField raw "allocations" "$"
    unless allocationsJson.size == nodes.size do
      throw "source AllocId profile no longer matches the raw allocation table"
    for (value, index) in allocationsJson.toList.zipIdx do
      let parsed ← parseAllocation value s!"$.allocations[{index}]"
      let some supplied := nodes[index]? | throw s!"$.allocations[{index}]: typed allocation row is absent"
      unless parsed.id == supplied.id && parsed.sourceAllocId == supplied.sourceAllocId &&
          parsed.status == supplied.status && parsed.kind == supplied.kind &&
          parsed.memory == supplied.memory && parsed.data == supplied.data &&
          parsed.payload.compress == supplied.payload.compress do
        throw s!"$.allocations[{index}]: source AllocId profile does not match the exact raw allocation node"
    let verified ← parseCompilerAllocIdWorld rawWorld nodes
    unless verified == world do
      throw "source AllocId profile model does not match its exact raw document object"

def parseLocal (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String LocalDecl := do
  let type ← field j "type" path
  let typeId ← match isTypeRef type with
    | some id => pure id
    | none => throw s!"{joinPath path "type"}: expected type reference object"
  let sourceInfo ← parseSourceInfo (← field j "source_info" path) (joinPath path "source_info") memo
  return {
    id := ← fieldNat j "local" path
    typeId := typeId
    sourceInfo := sourceInfo
    payload := j
  }

def parseMirNode (wrapper : Json) (path : String) (domain : Domain) (memo : DecodeMemo := {}) : Except String MirNode := do
  let sourceInfo ← parseSourceInfo (← field wrapper "source_info" path) (joinPath path "source_info") memo
  let kind ← field wrapper "kind" path
  let value ← decodeValue kind (joinPath path "kind") domain .none memo
  return ⟨value, sourceInfo⟩

def parseBasicBlock (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String BasicBlock := do
  let statementJson ← arrayField j "statements" path
  let mut statements := #[]
  let mut index := 0
  for statement in statementJson do
    statements := statements.push (← parseMirNode statement s!"{joinPath path "statements"}[{index}]" .statement memo)
    index := index + 1
  let terminatorObject ← field j "terminator" path
  if terminatorObject == .null then throw s!"{joinPath path "terminator"}: basic block has no terminator"
  return {
    id := ← fieldNat j "block" path
    statements := statements
    terminator := ← parseMirNode terminatorObject (joinPath path "terminator") .terminator memo
    cleanup := ← fieldBool j "is_cleanup" path
    payload := j
  }

def parseBodyCore (j : Json) (path fallbackName : String) (memo : DecodeMemo := {}) : Except String BodyCore := do
  let localsJson ← arrayField j "locals" path
  let mut locals := #[]
  let mut index := 0
  for localDecl in localsJson do
    locals := locals.push (← parseLocal localDecl s!"{joinPath path "locals"}[{index}]" memo)
    index := index + 1
  let blocksJson ← arrayField j "basic_blocks" path
  let mut blocks := #[]
  index := 0
  for block in blocksJson do
    blocks := blocks.push (← parseBasicBlock block s!"{joinPath path "basic_blocks"}[{index}]" memo)
    index := index + 1
  let defPath ← optionalString j "def_path" path
  let definitionId ← match optionalJson j "def_id" with
    | none => match optionalJson j "source_def_id" with
      | none => pure none
      | some value => pure (some (← parseDefinitionId value (joinPath path "source_def_id")))
    | some value => pure (some (← parseDefinitionId value (joinPath path "def_id")))
  let phase ← decodeValue (← field j "phase" path) (joinPath path "phase") .any (some .mirPhase) memo
  let injectionPhase ← match optionalJson j "injection_phase" with
    | none => pure none
    | some value => pure (some (← decodeValue value (joinPath path "injection_phase") .any (some .mirPhase) memo))
  let sourceScopes ← match optionalJson j "source_scopes" with
    | none => pure none
    | some value => some <$> jsonArray value (joinPath path "source_scopes")
  return {
    sourcePath := path
    defPath := match defPath with | some name => name | none => fallbackName
    definitionId := definitionId
    phase := phase
    injectionPhase := injectionPhase
    argumentCount := ← fieldNat j "arg_count" path
    spreadArgument := ← optionalNat j "spread_arg" path
    locals := locals
    blocks := blocks
    sourceScopes := sourceScopes
    payload := j
  }

def parsePromotedBodies (j : Json) (path fallbackName : String) (memo : DecodeMemo := {}) : Except String (Array PromotedBody) := do
  let promotedJson ← match optionalJson j "promoted_bodies" with
    | none => pure #[]
    | some value => jsonArray value (joinPath path "promoted_bodies")
  let mut promotedBodies := #[]
  for (entry, index) in promotedJson.toList.zipIdx do
    let promotedPath := s!"{joinPath path "promoted_bodies"}[{index}]"
    let promotedIndex ← match optionalField entry "promoted_index" with
      | none => pure index
      | some value => value.getNat? |>.mapError fun e => s!"{joinPath promotedPath "promoted_index"}: expected unsigned integer ({e})"
    let status ← match optionalField entry "status" with
      | none => pure (if (optionalField entry "body").isSome then .supported else .incomplete)
      | some value => parseStatus <$> (value.getStr? |>.mapError fun e => s!"{joinPath promotedPath "status"}: expected string ({e})")
    let body ← match optionalJson entry "body" with
      | none => pure none
      | some value => pure (some (← parseBodyCore value (joinPath promotedPath "body") s!"{fallbackName}::promoted[{promotedIndex}]" memo))
    promotedBodies := promotedBodies.push ⟨promotedIndex, status, body, entry⟩
  return promotedBodies

def parseBody (j : Json) (path fallbackName : String) (memo : DecodeMemo := {}) : Except String Body := do
  let core ← parseBodyCore j path fallbackName memo
  let promotedBodies ← parsePromotedBodies j path fallbackName memo
  return { core with promotedBodies := promotedBodies }

def parseInstance (j : Json) (path : String) : Except String InstanceNode := do
  let kindText ← fieldString j "kind" path
  let kind := match kindText with
    | "instance_mir" => .instanceMir
    | "instance_mir_template" => .instanceMirTemplate
    | "intrinsic_without_mir" => .intrinsicWithoutMir
    | "intrinsic_dispatch" => .intrinsicDispatch
    | "foreign_item_no_mir" => .foreignItemNoMir
    | "virtual_dispatch" => .virtualDispatch
    | "virtual_dispatch_target" => .virtualDispatchTarget
    | "instance_mir_unavailable" => .instanceMirUnavailable
    | "symbol_identity_only" => .symbolIdentityOnly
    | other => .other other
  let id ← fieldNat j "instance_id" path
  let defPath ← optionalString j "def_path" path
  let definitionId ← match optionalJson j "def_id" with
    | none => pure none
    | some value => pure (some (← parseDefinitionId value (joinPath path "def_id")))
  let fallback := match defPath with
    | some value => value
    | none => s!"instance[{id}]"
  let bodyInstantiation ← match optionalJson j "body_instantiation" with
    | none => pure none
    | some value => pure (some (← parseAbiTag value (joinPath path "body_instantiation")))
  let bodyTemplateIsPolymorphic ← match optionalField j "body_template_is_polymorphic" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "body_template_is_polymorphic"}: expected boolean ({e})"
  let instanceArgsAreMonomorphic ← match optionalField j "instance_args_are_monomorphic" with
    | none | some .null => pure none
    | some value => (value.getBool?).map some |>.mapError fun e => s!"{joinPath path "instance_args_are_monomorphic"}: expected boolean ({e})"
  let body ← match optionalJson j "body" with
    | none => pure none
    | some value => pure (some (← parseBody value (joinPath path "body") fallback))
  let promotedBodies ← parsePromotedBodies j path fallback
  return {
    id := id
    status := parseStatus (← fieldString j "status" path)
    kind := kind
    defPath := defPath
    definitionId := definitionId
    bodyInstantiation := bodyInstantiation
    bodyTemplateIsPolymorphic := bodyTemplateIsPolymorphic
    instanceArgsAreMonomorphic := instanceArgsAreMonomorphic
    body := body
    promotedBodies := promotedBodies
    payload := j
  }

def passModeKind (tag : String) : PassModeKind :=
  match tag with
  | "Ignore" => .ignore
  | "Direct" => .direct
  | "Pair" => .pair
  | "Cast" => .cast
  | "Indirect" => .indirect
  | "IndirectUnsized" => .indirectUnsized
  | other => .unknown other

def parseAbiAttributes (j : Json) (path : String) : Except String AbiAttributes := do
  return {
    noAlias := ← fieldBool j "no_alias" path
    noFree := ← fieldBool j "no_free" path
    noUndef := ← fieldBool j "no_undef" path
    nonNull := ← fieldBool j "non_null" path
    readOnly := ← fieldBool j "read_only" path
    writable := ← fieldBool j "writable" path
    inRegister := ← fieldBool j "in_register" path
    regularBits := ← fieldNat j "regular_bits" path
    pointeeSizeBytes := ← fieldNat j "pointee_size_bytes" path
    pointeeAlignBytes := ← optionalNat j "pointee_align_bytes" path
    argExtension := ← parseAbiTag (← field j "arg_extension" path) (joinPath path "arg_extension")
    captures := ← parseAbiTag (← field j "captures" path) (joinPath path "captures")
  }

def abiRegisterKind (tag : String) : AbiRegisterKind :=
  match tag with
  | "integer" => .integer
  | "float" => .float
  | "ppc_f128" => .ppcF128
  | "vector" => .vector
  | other => .unknown other

def canonicalAbiKind (tag : String) : CanonicalAbiKind :=
  match tag with
  | "c" => .c
  | "rust" => .rust
  | "rust_cold" => .rustCold
  | "rust_preserve_none" => .rustPreserveNone
  | "rust_tail" => .rustTail
  | "custom" => .custom
  | "swift" => .swift
  | "arm" => .arm
  | "gpu_kernel" => .gpuKernel
  | "interrupt" => .interrupt
  | "x86" => .x86
  | other => .unknown other

def armCallKind (tag : String) : ArmCallKind :=
  match tag with
  | "aapcs" => .aapcs
  | "cmse_nonsecure_call" => .cmseNonSecureCall
  | "cmse_nonsecure_entry" => .cmseNonSecureEntry
  | other => .unknown other

def interruptCallKind (tag : String) : InterruptCallKind :=
  match tag with
  | "avr" => .avr
  | "avr_non_blocking" => .avrNonBlocking
  | "msp430" => .msp430
  | "riscv_machine" => .riscvMachine
  | "riscv_supervisor" => .riscvSupervisor
  | "x86" => .x86
  | other => .unknown other

def x86CallKind (tag : String) : X86CallKind :=
  match tag with
  | "fastcall" => .fastcall
  | "stdcall" => .stdcall
  | "sysv64" => .sysv64
  | "thiscall" => .thiscall
  | "vectorcall" => .vectorcall
  | "win64" => .win64
  | other => .unknown other

def parseCanonicalAbi (j : Json) (path : String) : Except String CanonicalAbi := do
  let kindNode ← parseAbiTag j path
  return {
    status := kindNode.status
    kind := canonicalAbiKind kindNode.tag
    armCall := (← optionalString j "arm_call" path).map armCallKind
    interruptKind := (← optionalString j "interrupt_kind" path).map interruptCallKind
    x86Call := (← optionalString j "x86_call" path).map x86CallKind
    payload := j
  }

def parseAbiRegister (j : Json) (path : String) : Except String AbiRegister := do
  let kindNode ← field j "kind" path
  let kindTag ← fieldString kindNode "kind" (joinPath path "kind")
  let hintElement ← match optionalJson kindNode "hint_element" with
    | none => pure none
    | some value => pure (some (← parseAbiTag value (joinPath path "kind.hint_element")))
  return {
    kind := abiRegisterKind kindTag
    sizeBits := ← fieldNat j "size_bits" path
    hintElement := hintElement
    payload := j
  }

def parseAbiCastTarget (j : Json) (path : String) : Except String AbiCastTarget := do
  let prefixJson ← arrayField j "prefix_registers" path
  let mut prefixRegisters := #[]
  for (register, index) in prefixJson.toList.zipIdx do
    prefixRegisters := prefixRegisters.push (← parseAbiRegister register s!"{joinPath path "prefix_registers"}[{index}]")
  return {
    prefixRegisters := prefixRegisters
    restOffsetBytes := ← optionalNat j "rest_offset_bytes" path
    restRegister := ← parseAbiRegister (← field j "rest_register" path) (joinPath path "rest_register")
    restTotalBytes := ← fieldNat j "rest_total_bytes" path
    restIsConsecutive := ← fieldBool j "rest_is_consecutive" path
    attributes := ← parseAbiAttributes (← field j "attributes" path) (joinPath path "attributes")
    payload := j
  }

def parseAbiPassMode (j : Json) (path : String) : Except String AbiPassMode := do
  let tag ← fieldString j "kind" path
  let mut attributes := #[]
  for key in ["attributes", "first", "second", "metadata_attributes"] do
    if let some attr := optionalJson j key then
      if key == "attributes" || key == "metadata_attributes" then
        attributes := attributes.push (← parseAbiAttributes attr (joinPath path key))
      else if key == "first" || key == "second" then
        attributes := attributes.push (← parseAbiAttributes attr (joinPath path key))
  let castTarget ← match optionalJson j "target" with
    | none => pure none
    | some value => pure (some (← parseAbiCastTarget value (joinPath path "target")))
  let indirectMode ← match optionalJson j "mode" with
    | none => pure none
    | some value => pure (some (← parseAbiTag value (joinPath path "mode")))
  let padI32Count ← optionalNat j "pad_i32_count" path
  let addressSpace ← optionalNat j "address_space" path
  let kind := passModeKind tag
  match kind with
  | .cast => if castTarget.isNone || padI32Count.isNone then throw s!"{path}: Cast pass mode is missing target/padding data"
  | .indirect => if indirectMode.isNone then throw s!"{path}: Indirect pass mode is missing its mode tag"
  | .direct | .pair | .indirectUnsized | .ignore | .unknown _ => pure ()
  return {
    kind := kind
    attributes := attributes
    castTarget := castTarget
    padI32Count := padI32Count
    addressSpace := addressSpace
    indirectMode := indirectMode
    payload := j
  }

def parseAbiArgument (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String AbiArgument := do
  let typeRef ← field j "type" path
  let typeId ← match isTypeRef typeRef with
    | some id => pure id
    | none => throw s!"{joinPath path "type"}: expected type reference"
  let layout ← match optionalField j "layout" with
    | none => pure none
    | some value => pure (some (← parseLayout value (joinPath path "layout") memo))
  return {
    typeId := typeId
    layout := layout
    mode := ← parseAbiPassMode (← field j "mode" path) (joinPath path "mode")
    payload := j
  }

private def parseFunctionAbiUncached (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String FunctionAbi := do
  let argsJson ← arrayField j "arguments" path
  let mut args := #[]
  let mut index := 0
  for arg in argsJson do
    args := args.push (← parseAbiArgument arg s!"{joinPath path "arguments"}[{index}]" memo)
    index := index + 1
  let ret ← parseAbiArgument (← field j "return" path) (joinPath path "return") memo
  return {
    arguments := args
    returnValue := ret
    callingConvention := ← parseCanonicalAbi (← field j "calling_convention" path) (joinPath path "calling_convention")
    canUnwind := ← fieldBool j "can_unwind" path
    cVariadic := ← fieldBool j "c_variadic" path
    fixedCount := ← fieldNat j "fixed_count" path
    payload := j
  }

def parseFunctionAbi (j : Json) (path : String) (memo : DecodeMemo := {}) : Except String FunctionAbi :=
  match memo.functionAbis[j]? with
  | some abi => pure abi
  | none => parseFunctionAbiUncached j path memo

/-- Decode an exact compiler projection layout using the canonical schema. -/
def decodeCompilerLayout (j : Json) : Except String Layout :=
  parseLayout j "$.compiler_projection_layout"

/-- Decode an independently keyed compiler FnAbi query using the canonical schema. -/
def decodeCompilerFunctionAbi (j : Json) : Except String FunctionAbi :=
  parseFunctionAbi j "$.compiler_fn_abi"

/-- Decode a compiler FnAbi using successful layouts collected from the same
shared-payload table. Failures and diagnostics follow the uncached decoder. -/
def decodeCompilerFunctionAbiWithMemo (j : Json) (memo : CompilerFunctionAbiMemo) :
    Except String FunctionAbi :=
  parseFunctionAbi j "$.compiler_fn_abi" memo.memo


def isFunctionAbiCandidate (raw : Json) : Bool :=
  ["arguments", "return", "calling_convention", "can_unwind", "c_variadic", "fixed_count"]
    |>.all fun key => (raw.getObjVal? key).isOk

private def buildCompilerFunctionAbiEntries (nodes : Array Json) (memo : CompilerFunctionAbiMemo) :
    Array (Json × Except String FunctionAbi) := Id.run do
  let mut entries := #[]
  for raw in nodes do
    if isFunctionAbiCandidate raw then
      entries := entries.push (raw, decodeCompilerFunctionAbiWithMemo raw memo)
  return entries

/-- A typed projection bound to the exact immutable shared-node table. The
constructor cannot install results from another decoder or another document. -/
structure CompilerFunctionAbiTable (nodes : Array Json) where
  private mk ::
  entries : Array (Json × Except String FunctionAbi)
  /-- Existential evidence is erased; the large temporary decode memo is not
  retained in the imported document. -/
  private exact : ∃ memo : CompilerFunctionAbiMemo,
    entries = buildCompilerFunctionAbiEntries nodes memo

/-- Reuse the importer's successful layout memo. Failed query decodes are values,
not import failures, and keep the canonical demand-time diagnostic path. -/
def prepareCompilerFunctionAbiTableUsing (nodes : Array Json) (memo : DecodeMemo) :
    CompilerFunctionAbiTable nodes :=
  ⟨buildCompilerFunctionAbiEntries nodes ⟨memo⟩, ⟨⟨memo⟩, rfl⟩⟩

/-- Successful projections can also serve the occurrence-sensitive collector.
Failures deliberately fall through so its original path and first error survive. -/
def CompilerFunctionAbiTable.extendDecodeMemo (table : CompilerFunctionAbiTable nodes)
    (base : DecodeMemo) : DecodeMemo := Id.run do
  let mut result := base
  for (raw, decoded) in table.entries do
    if let .ok abi := decoded then
      if hasCanonicalJsonObjectKeys raw then
        result := { result with functionAbis := result.functionAbis.insert raw abi }
  return result

/-- The context used by compiler adapters is separate from runtime-readiness
summaries. These are complete typed values, including source coordinates. -/
def decodeCompilerValue (j : Json) : Except String TypedValue :=
  decodeValue j "$compiler_value"

private def buildCompilerValueEntries (nodes : Array Json) (memo : DecodeMemo) :
    Std.HashMap Json (Except String TypedValue) := Id.run do
  let mut entries := {}
  for node in nodes do
    let .obj fields := node | continue
    for (key, raw) in fields.toList do
      if ["generic_args", "rebased_args", "span", "preamble_def_span", "callsite_span"].contains key &&
          hasCanonicalJsonObjectKeys raw && !entries.contains raw then
        entries := entries.insert raw (decodeValue raw "$compiler_value" .any none memo)
  return entries

/-- Every entry is a checked decoder outcome for its JSON key. Unlike an
instance/type lookup, this cache may safely survive a document record update:
its immutable keys include the entire source value, never only a local ID. -/
structure CompilerValueMemo where
  private mk ::
  private entries : Std.HashMap Json (Except String TypedValue)
  private exact : ∃ (nodes : Array Json) (memo : DecodeMemo),
    entries = buildCompilerValueEntries nodes memo

def prepareCompilerValueMemoUsing (nodes : Array Json) (memo : DecodeMemo) : CompilerValueMemo :=
  ⟨buildCompilerValueEntries nodes memo, ⟨nodes, memo, rfl⟩⟩

def decodeCompilerValueWithMemo (raw : Json) (memo : Option CompilerValueMemo) : Except String TypedValue :=
  match memo with
  | some memo =>
    if !hasCanonicalJsonObjectKeys raw then decodeCompilerValue raw else
    match memo.entries[raw]? with
    | some result => result
    | none => decodeCompilerValue raw
  | none => decodeCompilerValue raw

end Miri.Input.DecoderValues

namespace Miri.Input
export DecoderValues (expectedMiriCommit expectedRustcCommit expectedSchema expectedSchemaVersion expectedCompilerAbiLayoutSchema CompilerFunctionAbiMemo prepareCompilerFunctionAbiMemo decodeCompilerPredicateEvidence decodeCompilerPattern decodeTypeCompilerFacts decodeVtableEntry decodeStaticGlobalInfo validateCompilerAllocIdWorldRaw decodeCompilerLayout decodeCompilerFunctionAbi decodeCompilerFunctionAbiWithMemo CompilerFunctionAbiTable CompilerValueMemo decodeCompilerValue decodeCompilerValueWithMemo)
end Miri.Input
