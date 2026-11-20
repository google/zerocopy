import Miri.Input.Model
import Miri.Input.Decoder
import Miri.MIR.Syntax

/-! Fail-closed bridge from decoded compiler data to the fixed interpreter AST.
Successful lowering is syntax construction, not execution readiness or UB freedom.
The original envelope and source scopes remain available beside the MIR body. -/
namespace Miri.Input

abbrev LowerResult := Except String

private def buildTypeSet (ids : Array TypeId) : Std.HashSet TypeId :=
  ids.foldl (fun found id => found.insert id) {}

private def buildAllocationSet (ids : Array AllocationId) : Std.HashSet AllocationId :=
  ids.foldl (fun found id => found.insert id) {}

/-- Preserve `Array.find?`'s first-row choice for duplicate scalar widths. -/
private def buildScalarMap (sizes : Array (TypeId × Nat)) : Std.HashMap TypeId Nat :=
  sizes.foldl (fun found (ty,size) =>
    if (found.get? ty).isSome then found else found.insert ty size) {}

set_option autoImplicit false in
/-- Membership acceleration whose type ties it to the exact source array.
Its constructor is private, and the exactness field proves that its value is
the corresponding index built from that array. Any update must preserve this
equality. -/
structure LowerContextTypeIndex (source : Array TypeId) where
  private mk ::
  values : Std.HashSet TypeId
  exact : values = buildTypeSet source

set_option autoImplicit false in
structure LowerContextAllocationIndex (source : Array AllocationId) where
  private mk ::
  values : Std.HashSet AllocationId
  exact : values = buildAllocationSet source

set_option autoImplicit false in
structure LowerContextScalarIndex (source : Array (TypeId × Nat)) where
  private mk ::
  values : Std.HashMap TypeId Nat
  exact : values = buildScalarMap source

private def buildTypeIndex (ids : Array TypeId) : LowerContextTypeIndex ids :=
  ⟨buildTypeSet ids, rfl⟩

private def buildAllocationIndex (ids : Array AllocationId) : LowerContextAllocationIndex ids :=
  ⟨buildAllocationSet ids, rfl⟩

private def buildScalarIndex (sizes : Array (TypeId × Nat)) : LowerContextScalarIndex sizes :=
  ⟨buildScalarMap sizes, rfl⟩

structure LowerContext where
  /-- Each supplied type ID must refer to this compilation's metadata graph. -/
  typeIds : Array TypeId
  /-- Exact byte widths from compiler layout metadata; required for scalar constants. -/
  scalarSizes : Array (TypeId × Nat)
  allocationIds : Array AllocationId := #[]
  obligations : Array Obligation := #[]
  /-- Raw source document used only to revalidate exact source-path roles while
  lowering. A bare caller-supplied path never discharges an obligation. -/
  sourceDocument : Option Lean.Json := none
  compilerValueMemo : Option CompilerValueMemo := none
  /-- Optional exact-array certificates; hand-built contexts default to the
  original linear lookup behavior. -/
  typeIndex : Option (LowerContextTypeIndex typeIds) := none
  allocationIndex : Option (LowerContextAllocationIndex allocationIds) := none
  scalarIndex : Option (LowerContextScalarIndex scalarSizes) := none

/-- Consume complete import-time compiler values; manual contexts decode directly. -/
def LowerContext.decodeCompilerValue (ctx : LowerContext) (raw : Lean.Json) : Except String TypedValue :=
  decodeCompilerValueWithMemo raw ctx.compilerValueMemo

def LowerContext.containsTypeId (ctx : LowerContext) (id : TypeId) : Bool :=
  match ctx.typeIndex with
  | some index => index.values.contains id
  | none => ctx.typeIds.contains id

def LowerContext.containsAllocationId (ctx : LowerContext) (id : AllocationId) : Bool :=
  match ctx.allocationIndex with
  | some index => index.values.contains id
  | none => ctx.allocationIds.contains id

def LowerContext.scalarSize (ctx : LowerContext) (id : TypeId) : Option Nat :=
  match ctx.scalarIndex with
  | some index => index.values.get? id
  | none => (ctx.scalarSizes.find? (fun pair => pair.1 == id)).map Prod.snd

/-- Rebase the source type universe and rebuild its private membership cache. -/
def LowerContext.withTypeIds (ctx : LowerContext) (ids : Array TypeId) : LowerContext :=
  { ctx with typeIds := ids, typeIndex := some (buildTypeIndex ids) }

/-- Rebase the allocation universe and rebuild its private membership cache. -/
def LowerContext.withAllocationIds (ctx : LowerContext) (ids : Array AllocationId) : LowerContext :=
  { ctx with allocationIds := ids, allocationIndex := some (buildAllocationIndex ids) }

/-- Rebase scalar layouts and rebuild the first-row-preserving width cache. -/
def LowerContext.withScalarSizes (ctx : LowerContext) (sizes : Array (TypeId × Nat)) : LowerContext :=
  { ctx with scalarSizes := sizes, scalarIndex := some (buildScalarIndex sizes) }

/-- Derive scalar widths from compiler metadata, never from bits or host types. -/
def LowerContext.ofTypes (types : Array TypeNode) : LowerContext := Id.run do
  let typeIds := types.map (·.id)
  let scalarSizes := types.filterMap fun ty =>
    if ty.layout.status == .supported then ty.layout.sizeBytes.map (ty.id, ·) else none
  let obligations : Array Obligation := types.filterMap fun ty =>
      if ty.shapeStatus == .supported then none else
        some ⟨s!"types[{ty.id}].shape", "type shape metadata remains unresolved; its compilation-local identity is preserved"⟩
  let mut ctx : LowerContext := {
    typeIds
    scalarSizes
    allocationIds := #[]
    obligations
    sourceDocument := none
  }
  ctx := { ctx with
    typeIndex := some (buildTypeIndex typeIds)
    scalarIndex := some (buildScalarIndex scalarSizes) }
  return ctx

/-- Resolve graph identities from the same decoded compilation. Metadata
semantics remain independent from syntax lowering and its obligations. -/
def LowerContext.ofDocument (document : ImportDocumentCore) : LowerContext :=
  let ctx := (ofTypes document.types).withAllocationIds (document.allocations.map (·.id))
  { ctx with sourceDocument := some document.raw, compilerValueMemo := document.compilerValueMemo }

set_option autoImplicit false in
/-- A prepared lowering context tied to one exact decoded source document.
The private constructor and equality field prevent reusing it for a different
document, even when the documents serialize to equal JSON. -/
structure LowerContext.Bound (document : ImportDocumentCore) where
  private mk ::
  value : LowerContext
  exact : value = LowerContext.ofDocument document

/-- Prepare the context and retain its exact document identity in the type. -/
def LowerContext.bindDocument (document : ImportDocumentCore) : LowerContext.Bound document :=
  ⟨LowerContext.ofDocument document, rfl⟩

structure LoweredBody where
  body : MIR.Body
  spans : Array SourceSpanData
  input : BodyCore
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst
  obligations : Array Obligation

/-- Resolve a crate-qualified compiler definition into this bundle's dense
identity. Raw rustc definition indices are never runtime definition IDs. -/
def lookupDefinitionId (definitions : Array DefinitionId) (sourceId : DefinitionId)
    : LowerResult MIR.DefId :=
  -- Compiler queries repeat this lookup; keep the search on the array rather
  -- than allocating a full list before examining the first matching ID.
  match definitions.idxOf? sourceId with
  | some id => pure id
  | none => throw s!"unresolved compiler definition {sourceId.crateIndex}:{sourceId.index}"

def LoweredBody.ownDefinitionId (body : LoweredBody) : LowerResult MIR.DefId := do
  let some sourceId := body.input.definitionId | throw "body is missing its source definition identity"
  lookupDefinitionId body.definitions sourceId

/-- Constructor inventory. `true` means a lowering branch exists, subject to
child metadata checks; it does not mean execution semantics is implemented.
Exhaustive matches make newly added input constructors require a decision. -/
def rvalueLoweringBranch : RvalueVariant → Bool
  | .use | .binaryOp | .unaryOp | .discriminant | .copyForDeref | .wrapUnsafeBinder => true
  | .repeat | .ref | .threadLocalRef | .rawPtr | .cast | .aggregate | .reborrow => true
  | .unknown _ => false

def statementLoweringBranch : StatementVariant → Bool
  | .assign | .setDiscriminant | .storageLive | .storageDead | .placeMention | .constEvalCounter | .nop => true
  | .fakeRead | .ascribeUserType | .coverage | .intrinsic | .backwardIncompatibleDropHint => true
  | .unknown _ => false

def terminatorLoweringBranch : TerminatorVariant → Bool
  | .goto | .unwindResume | .return | .unreachable | .assert | .coroutineDrop | .falseEdge => true
  | .switchInt | .unwindTerminate | .drop | .call | .tailCall | .yield | .falseUnwind | .inlineAsm => true
  | .unknown _ => false

private abbrev Fields := Array (String × TypedValue)
private structure LowerState where
  spans : Array SourceSpanData := #[]
  definitions : Array DefinitionId := #[]
  typeConstants : Array MIR.TypeConst := #[]
  /-- Enabled only by `lowerBodies`; standalone lowering keeps the original
  linear lookup path. Buckets are candidates, never substitutes for equality. -/
  spanCandidates : Option (Std.HashMap (String × Nat × Nat) (Array Nat)) := none
  definitionCandidates : Option (Std.HashMap (Nat × Nat) Nat) := none

private abbrev LowerM := StateT LowerState (Except String)

private def get (fs : Fields) (key : String) : LowerResult TypedValue :=
  match fs.find? (fun entry => entry.1 == key) with
  | some (_, v) => .ok v
  | none => .error s!"missing lowering field {key}"

private def fields : TypedValue → LowerResult Fields
  | .object fs | .enumTag _ _ fs => .ok fs
  | _ => .error "expected typed object"

private def nat : TypedValue → LowerResult Nat
  | .scalar j => j.getNat?
  | .localRef n | .blockRef n => .ok n
  | _ => .error "expected unsigned integer"

private def bool : TypedValue → LowerResult Bool
  | .scalar j => j.getBool?
  | _ => .error "expected boolean"

private def text : TypedValue → LowerResult String
  | .scalar j => j.getStr?
  | _ => .error "expected string"

private def array : TypedValue → LowerResult (Array TypedValue)
  | .array vs => .ok vs
  | _ => .error "expected typed array"

private def tag : TypedValue → LowerResult String
  | .enumTag _ t _ => .ok t.tag
  | .object fs => get fs "kind" >>= text
  | v => text v

private def typeId (ctx : LowerContext) : TypedValue → LowerResult MIR.TyId
  | .typeRef id => if ctx.containsTypeId id then .ok id else .error s!"unresolved type {id}"
  | _ => .error "expected type reference"

private def spanCandidateKey (span : SourceSpanData) : String × Nat × Nat :=
  (span.file, span.lo, span.hi)

private def intern (span : SourceSpanData) : LowerM MIR.SpanRef := do
  let state ← StateT.get
  match state.spanCandidates with
  | none =>
    match state.spans.toList.idxOf? span with
    | some i => pure ⟨i⟩
    | none =>
      StateT.set { state with spans := state.spans.push span }
      pure ⟨state.spans.size⟩
  | some candidates =>
    let bucket := candidates.getD (spanCandidateKey span) #[]
    if let some i := bucket.find? fun i =>
        match state.spans[i]? with
        | some previous => decide (previous = span)
        | none => false then
      pure ⟨i⟩
    else
      let i := state.spans.size
      let nextCandidates := candidates.insert (spanCandidateKey span) (bucket.push i)
      StateT.set { state with spans := state.spans.push span, spanCandidates := some nextCandidates }
      pure ⟨i⟩

private def source (info : SourceInfo) : LowerM MIR.SourceInfo := do
  return ⟨← intern info.span, info.scope⟩

private def optional (lower : TypedValue → LowerResult α) : TypedValue → LowerResult (Option α)
  | .scalar .null => pure none
  | value => some <$> lower value

private def optionalM (lower : TypedValue → LowerM α) : TypedValue → LowerM (Option α)
  | .scalar .null => pure none
  | value => some <$> lower value

private def number (v : TypedValue) : LowerResult Nat := do
  match v with
  | .scalar (.str s) => match s.toNat? with | some n => pure n | none => throw "invalid decimal integer"
  | v => nat v

private def definition (v : TypedValue) : LowerM MIR.DefId := do
  let id ← (show LowerM DefinitionId from match v with
    | .object fs => return DefinitionId.mk (← nat (← get fs "crate")) (← nat (← get fs "index"))
    | v => do
      let encoded ← text v
      match encoded.splitOn ":" with
      | [cratePart, indexPart] =>
        match cratePart.toNat?, indexPart.toNat? with
        | some c, some i => pure (DefinitionId.mk c i)
        | _, _ => throw "invalid compiler definition ID"
      | _ => throw "expected crate-qualified definition ID")
  let state ← StateT.get
  let key := (id.crateIndex,id.index)
  let found := match state.definitionCandidates with
    | some candidates => candidates.get? key
    | none => state.definitions.toList.idxOf? id
  match found with
  | some i => pure i
  | none =>
    let i := state.definitions.size
    let candidates := state.definitionCandidates.map (·.insert key i)
    StateT.set { state with definitions := state.definitions.push id, definitionCandidates := candidates }
    pure i

private def hasDefinition (state : LowerState) (id : DefinitionId) : Bool :=
  match state.definitionCandidates with
  | some candidates => (candidates.get? (id.crateIndex,id.index)).isSome
  | none => state.definitions.contains id

private def addDefinition (state : LowerState) (id : DefinitionId) : LowerState :=
  if hasDefinition state id then state
  else
    let index := state.definitions.size
    let candidates := state.definitionCandidates.map
      (·.insert (id.crateIndex,id.index) index)
    { state with definitions := state.definitions.push id, definitionCandidates := candidates }

private def spanRef : TypedValue → LowerM MIR.SpanRef
  | .sourceSpan span => intern span
  | _ => throw "missing typed source span"

private def mutability (v : TypedValue) : LowerResult MIR.Mutability := do
  match ← tag v with
  | "mutable" => pure .Mut
  | "immutable" => pure .Not
  | _ => throw "unknown mutability"

private def safety (v : TypedValue) : LowerResult MIR.Safety := do
  match ← tag v with
  | "safe" => pure .Safe
  | "unsafe" => pure .Unsafe
  | _ => throw "unknown safety"

private def castKind (v : TypedValue) : LowerResult MIR.CastKind := do
  let fs ← fields v
  match ← tag v with
  | "PointerExposeProvenance" => pure .PointerExposeProvenance
  | "PointerWithExposedProvenance" => pure .PointerWithExposedProvenance
  | "PointerCoercion" =>
    let c ← get fs "coercion"
    let cf ← fields c
    let coercion ← (show LowerResult MIR.PointerCoercion from match ← tag c with
      | "ReifyFnPointer" => return MIR.PointerCoercion.ReifyFnPointer (← safety (← get cf "safety"))
      | "UnsafeFnPointer" => pure .UnsafeFnPointer
      | "ClosureFnPointer" => return .ClosureFnPointer (← safety (← get cf "safety"))
      | "MutToConstPointer" => pure .MutToConstPointer
      | "ArrayToPointer" => pure .ArrayToPointer
      | "Unsize" => pure .Unsize
      | _ => throw "unknown pointer coercion")
    let source ← match ← tag (← get fs "source") with
      | "as_cast" => pure MIR.CoercionSource.AsCast
      | "implicit" => pure .Implicit
      | _ => throw "unknown coercion source"
    pure (.PointerCoercion coercion source)
  | "IntToInt" => pure .IntToInt
  | "FloatToInt" => pure .FloatToInt
  | "FloatToFloat" => pure .FloatToFloat
  | "IntToFloat" => pure .IntToFloat
  | "PtrToPtr" => pure .PtrToPtr
  | "FnPtrToPtr" => pure .FnPtrToPtr
  | "Transmute" => pure .Transmute
  | "BoxDerefTransmute" => pure .BoxDerefTransmute
  | "Subtype" => pure .Subtype
  | _ => throw "unknown cast kind"

private def boundIndex (v : TypedValue) : LowerResult MIR.BoundVarIndexKind := do
  let fs ← fields v
  match ← tag v with
  | "bound" => return .Bound (← nat (← get fs "debruijn_index"))
  | "canonical" => pure .Canonical
  | _ => throw "unknown bound index kind"

private def boundRegion (v : TypedValue) : LowerM MIR.BoundRegionKind := do
  let fs ← fields v
  match ← tag v with
  | "anonymous" => pure .Anon
  | "named_for_printing" => return .NamedForPrinting (← text (← get fs "name"))
  | "named" => return .Named (← definition (← get fs "def_id"))
  | "closure_environment" => pure .ClosureEnv
  | _ => throw "unknown bound region kind"

private def region (v : TypedValue) : LowerM MIR.Region := do
  let fs ← fields v
  match ← tag v with
  | "early_parameter" => return .EarlyParameter (← nat (← get fs "index")) (← text (← get fs "name"))
  | "bound" => return .Bound (← boundIndex (← get fs "index_kind")) (← nat (← get fs "variable_index")) (← boundRegion (← get fs "bound_kind"))
  | "late_parameter" =>
    let p ← get fs "parameter"
    let pf ← fields p
    let kind ← (show LowerM MIR.LateParamRegionKind from match ← tag p with
      | "anonymous" => return .Anon (← nat (← get pf "index"))
      | "named_anonymous" => return .NamedAnon (← nat (← get pf "index")) (← text (← get pf "name"))
      | "named" => return .Named (← definition (← get pf "def_id"))
      | "closure_environment" => pure .ClosureEnv
      | _ => throw "unknown late parameter region")
    return .LateParameter (← definition (← get fs "scope_def_id")) kind
  | "static" => pure .Static
  | "inference_variable" => return .InferenceVariable (← nat (← get fs "index"))
  | "placeholder" => return .Placeholder (← nat (← get fs "universe")) (← nat (← get fs "variable_index")) (← boundRegion (← get fs "bound_kind"))
  | "erased" => pure .Erased
  | "error" => pure .Error
  | _ => throw "unknown region"

private def borrow (v : TypedValue) : LowerResult MIR.BorrowKind := do
  let fs ← fields v
  match ← tag v with
  | "shared" => pure .Shared
  | "fake" =>
    match ← tag (← get fs "fake_kind") with
    | "shallow" => pure (.Fake .Shallow)
    | "deep" => pure (.Fake .Deep)
    | _ => throw "unknown fake borrow"
  | "mutable" =>
    match ← tag (← get fs "mutability_kind") with
    | "default" => pure (.Mut .Default)
    | "two_phase" => pure (.Mut .TwoPhaseBorrow)
    | "closure_capture" => pure (.Mut .ClosureCapture)
    | _ => throw "unknown mutable borrow"
  | _ => throw "unknown borrow kind"

private def projection (ctx : LowerContext) : TypedValue → LowerResult MIR.ProjectionElem
  | .projection k fs => do
    match k with
    | .deref => pure .Deref
    | .field => return .Field (← nat (← get fs "index")) (← typeId ctx (← get fs "field_type"))
    | .index => return .Index (← nat (← get fs "local"))
    | .constantIndex => return .ConstantIndex (← nat (← get fs "offset")) (← nat (← get fs "min_length")) (← bool (← get fs "from_end"))
    | .subslice => return .Subslice (← nat (← get fs "from")) (← nat (← get fs "to")) (← bool (← get fs "from_end"))
    | .downcast =>
      let name ← match ← get fs "name" with
        | .scalar .null => pure none
        | v => some <$> text v
      return .Downcast name (← nat (← get fs "variant_index"))
    | .opaqueCast => return .OpaqueCast (← typeId ctx (← get fs "cast_type"))
    | .unwrapUnsafeBinder => return .UnwrapUnsafeBinder (← typeId ctx (← get fs "inner_type"))
    | .phantomDeref => pure .PhantomDeref
    | .unknown name => throw s!"unknown projection {name}"
  | _ => .error "expected projection"

private def place (ctx : LowerContext) (v : TypedValue) : LowerResult MIR.Place := do
  let fs ← fields v
  return ⟨← nat (← get fs "local"), ← (← array (← get fs "projection")).mapM (projection ctx)⟩

private def binOp (v : TypedValue) : LowerResult MIR.BinOp := do
  match v with
  | .binOperator op .supported => pure op
  | _ =>
    match ← tag v with
    | "add" => pure .Add
    | "add_unchecked" => pure .AddUnchecked
    | "add_with_overflow" => pure .AddWithOverflow
    | "sub" => pure .Sub
    | "sub_unchecked" => pure .SubUnchecked
    | "sub_with_overflow" => pure .SubWithOverflow
    | "mul" => pure .Mul
    | "mul_unchecked" => pure .MulUnchecked
    | "mul_with_overflow" => pure .MulWithOverflow
    | "div" => pure .Div
    | "rem" => pure .Rem
    | "bit_xor" => pure .BitXor
    | "bit_and" => pure .BitAnd
    | "bit_or" => pure .BitOr
    | "shift_left" => pure .Shl
    | "shift_left_unchecked" => pure .ShlUnchecked
    | "shift_right" => pure .Shr
    | "shift_right_unchecked" => pure .ShrUnchecked
    | "equal" => pure .Eq
    | "less_than" => pure .Lt
    | "less_equal" => pure .Le
    | "not_equal" => pure .Ne
    | "greater_equal" => pure .Ge
    | "greater_than" => pure .Gt
    | "compare" => pure .Cmp
    | "pointer_offset" => pure .Offset
    | _ => throw "unknown binary operator"

private def unOp (v : TypedValue) : LowerResult MIR.UnOp := do
  match v with
  | .unOperator op .supported => pure op
  | _ =>
    match ← tag v with
    | "not" => pure .Not
    | "negate" => pure .Neg
    | "pointer_metadata" => pure .PtrMetadata
    | _ => throw "unknown unary operator"

private def internTypeConst (constant : MIR.TypeConst) : LowerM MIR.TypeConstId := do
  let state ← StateT.get
  match state.typeConstants.toList.idxOf? constant with
  | some i => pure i
  | none =>
    StateT.set { state with typeConstants := state.typeConstants.push constant }
    pure state.typeConstants.size

mutual
private partial def typeConst (ctx : LowerContext) (v : TypedValue) : LowerM MIR.TypeConst := do
  let fs ← fields v
  match ← tag v with
  | "parameter" =>
    let declared ← get fs "declared_type"
    let declared ← match declared with
      | .typeRef id => some <$> typeId ctx (.typeRef id)
      | .scalar .null => pure none
      | .object metadata =>
        match ← text (← get metadata "status") with
        | "unknown" => pure none
        | _ => throw "invalid parameter declared type metadata"
      | _ => throw "unresolved parameter declared type metadata"
    return .Param (← nat (← get fs "index")) (← text (← get fs "name")) declared
  | "inference" =>
    let infer ← get fs "inference"
    let inf ← fields infer
    match ← tag infer with
    | "variable" => return .InferVar (← nat (← get inf "index"))
    | "fresh" => return .InferFresh (← nat (← get inf "index"))
    | _ => throw "unknown const inference"
  | "bound" => return .Bound (← boundIndex (← get fs "index_kind")) (← nat (← get fs "variable_index"))
  | "placeholder" => return .Placeholder (← nat (← get fs "universe")) (← nat (← get fs "variable_index"))
  | "alias" =>
    let kind ← (show LowerM MIR.ConstAliasKind from match ← text (← get fs "alias_kind") with
      | "projection" => pure .Projection
      | "inherent_self" => pure .InherentSelf
      | "inherent_impl" => pure .InherentImpl
      | "free" => pure .Free
      | "anonymous" => pure .Anon
      | _ => throw "unknown const alias kind")
    let rigid ← match ← text (← get fs "rigidity") with
      | "rigid" => pure true
      | "not_rigid" => pure false
      | _ => throw "unknown const rigidity"
    return .Alias rigid kind (← definition (← get fs "def_id")) (← genericArgs ctx (← get fs "generic_args"))
  | "value" => return .Value (← typeId ctx (← get fs "type")) (← valTree ctx (← get fs "value"))
  | "error" => pure .Error
  | "expression" =>
    let kind ← (show LowerM MIR.ConstExpressionKind from match ← text (← get fs "expression_kind") with
      | "binary_operator" => return .Binop (← binOp (← get fs "operator"))
      | "unary_operator" => return .UnOp (← unOp (← get fs "operator"))
      | "function_call" => pure .FunctionCall
      | "cast" => do
        match ← text (← get fs "operator") with
        | "as" => pure (.Cast .As)
        | "use" => pure (.Cast .Use)
        | _ => throw "unknown abstract const cast"
      | _ => throw "unknown const expression")
    return .Expr kind (← genericArgs ctx (← get fs "arguments"))
  | _ => throw "unknown type constant"

private partial def genericArgs (ctx : LowerContext) (v : TypedValue) : LowerM (Array MIR.GenericArg) := do
  (← array v).mapM fun arg => do
    let fs ← fields arg
    match ← tag arg with
    | "type" => return .Type (← typeId ctx (← get fs "value"))
    | "lifetime" => return .Lifetime (← region (← get fs "value"))
    | "const" => return .Const (← internTypeConst (← typeConst ctx (← get fs "value")))
    | _ => throw "unknown generic argument"

private partial def valTree (ctx : LowerContext) (v : TypedValue) : LowerM MIR.ValTree := do
  let fs ← fields v
  match ← tag v with
  | "leaf" =>
    let size ← nat (← get fs "size_bytes")
    let bits ← number (← get fs "bits_unsigned")
    unless size > 0 && bits < 2 ^ (size * 8) do throw "invalid valtree scalar width"
    pure ⟨#[.Leaf bits size], 0⟩
  | "branch" =>
    let children ← (← array (← get fs "elements")).mapM fun child => do
      internTypeConst (← typeConst ctx child)
    pure ⟨#[.Branch children], 0⟩
  | _ => throw "unknown valtree"
end

private def annotation (v : TypedValue) : LowerResult Nat := do
  match v with
  | .scalar (.num _) => nat v
  | _ => let fs ← fields v; nat (← get fs "index")

private def aggregate (ctx : LowerContext) (v : TypedValue) : LowerM MIR.AggregateKind := do
  let fs ← fields v
  match ← tag v with
  | "Array" => return .Array (← typeId ctx (← get fs "element_type"))
  | "Tuple" => pure .Tuple
  | "Adt" =>
    return .Adt (← definition (← get fs "def_id")) (← nat (← get fs "variant_index"))
      (← genericArgs ctx (← get fs "generic_args")) (← optional annotation (← get fs "user_type_annotation"))
      (← optional nat (← get fs "active_union_field"))
  | "Closure" => return .Closure (← definition (← get fs "def_id")) (← genericArgs ctx (← get fs "generic_args"))
  | "Coroutine" => return .Coroutine (← definition (← get fs "def_id")) (← genericArgs ctx (← get fs "generic_args"))
  | "CoroutineClosure" => return .CoroutineClosure (← definition (← get fs "def_id")) (← genericArgs ctx (← get fs "generic_args"))
  | "RawPtr" => return .RawPtr (← typeId ctx (← get fs "pointee_type")) (← mutability (← get fs "mutability"))
  | _ => throw "unknown aggregate kind"

private def allocationId (ctx : LowerContext) : TypedValue → LowerResult MIR.AllocationId
  | .allocationRef id => if ctx.containsAllocationId id then pure id else throw s!"unresolved allocation {id}"
  | _ => throw "unresolved allocation reference"

private def constValue (ctx : LowerContext) (ty : MIR.TyId) (v : TypedValue) : LowerResult MIR.ConstValue := do
  let fs ← fields v
  match ← tag v with
  | "zero_sized" => pure .ZeroSized
  | "scalar" =>
    let bits ← number (← get fs "bits_unsigned")
    let size ← match ctx.scalarSize ty with
      | some size => pure size
      | none => throw s!"missing scalar byte width for type {ty}"
    unless size > 0 && bits < 2 ^ (8 * size) do throw "scalar bits exceed byte width"
    pure (.Scalar (.Int bits size))
  | "pointer_scalar" => return .Scalar (.Ptr (.Allocation (← allocationId ctx (← get fs "allocation")) (← nat (← get fs "offset_bytes")) (← bool (← get fs "immutable")) (← bool (← get fs "shared_ref"))))
  | "pointer_scalar_without_provenance" => return .Scalar (.Ptr (.Address (← number (← get fs "address")) (← nat (← get fs "address_width_bytes"))))
  | "slice_allocation" => return .Slice (← allocationId ctx (← get fs "allocation")) (← nat (← get fs "metadata_length"))
  | "indirect_allocation" => return .Indirect (← allocationId ctx (← get fs "allocation")) (← nat (← get fs "offset_bytes"))
  | _ => throw "unknown or unavailable evaluated constant"

private def constOperand (ctx : LowerContext) (v : TypedValue) : LowerM MIR.ConstOperand := do
  let c ← fields v
  let ty ← typeId ctx (← get c "type")
  let userType ← optional annotation (← get c "user_type_annotation")
  let span ← spanRef (← get c "span")
  let evaluated ← fields (← get c "constant")
  let originalValue ← get evaluated "source"
  let original ← fields originalValue
  let constant ← (show LowerM MIR.MirConst from match ← tag originalValue with
    | "already_evaluated" => return .Val (← constValue ctx ty (← get evaluated "value")) ty
    | "type_system_const" => return .Ty (← typeId ctx (← get original "type")) (← typeConst ctx (← get original "const"))
    | "unevaluated" => return .Unevaluated ⟨← definition (← get original "def_id"), ← genericArgs ctx (← get original "generic_args"), ← optional nat (← get original "promoted")⟩ (← typeId ctx (← get original "type"))
    | _ => throw "unknown MIR constant source")
  pure ⟨span, userType, constant⟩

private def operand (ctx : LowerContext) : TypedValue → LowerM MIR.Operand
  | .operand k _ fs => do
    match k with
    | .copy => return .Copy (← place ctx (← get fs "place"))
    | .move => return .Move (← place ctx (← get fs "place"))
    | .runtimeChecks =>
      let check ← tag (← get fs "check")
      let check ← match check with
        | "ub_checks" => pure MIR.RuntimeChecks.UbChecks
        | "contract_checks" => pure .ContractChecks
        | "overflow_checks" => pure .OverflowChecks
        | _ => throw "unknown runtime check"
      return .RuntimeChecks check
    | .constant => return .Constant (← constOperand ctx (← get fs "constant"))
    | .unknown name => throw s!"unknown operand {name}"
  | _ => throw "unsupported or malformed operand"

private def rvalue (ctx : LowerContext) : TypedValue → LowerM MIR.Rvalue
  | .rvalue k _ fs => do
    match k with
    | .use =>
      let retag ← tag (← get fs "retag")
      let retag ← match retag with
        | "yes" => pure MIR.WithRetag.Yes
        | "no" => pure .No
        | _ => throw "unknown retag mode"
      return .Use (← operand ctx (← get fs "operand")) retag
    | .binaryOp =>
      let op ← match ← get fs "operator" with
        | .binOperator op .supported => pure op
        | _ => throw "unsupported binary operator"
      return .BinaryOp op (← operand ctx (← get fs "left")) (← operand ctx (← get fs "right"))
    | .unaryOp =>
      let op ← match ← get fs "operator" with
        | .unOperator op .supported => pure op
        | _ => throw "unsupported unary operator"
      return .UnaryOp op (← operand ctx (← get fs "operand"))
    | .discriminant => return .Discriminant (← place ctx (← get fs "place"))
    | .copyForDeref => return .CopyForDeref (← place ctx (← get fs "place"))
    | .wrapUnsafeBinder => return .WrapUnsafeBinder (← operand ctx (← get fs "operand")) (← typeId ctx (← get fs "type"))
    | .repeat => return .Repeat (← operand ctx (← get fs "operand")) (← typeConst ctx (← get fs "count"))
    | .ref => return .Ref (← region (← get fs "region")) (← borrow (← get fs "borrow_kind")) (← place ctx (← get fs "place"))
    | .threadLocalRef => return .ThreadLocalRef (← definition (← get fs "def_id"))
    | .rawPtr =>
      let kind ← (show LowerM MIR.RawPtrKind from match ← tag (← get fs "pointer_kind") with
        | "mutable" => pure .Mut
        | "constant" => pure .Const
        | "metadata_only" => pure .FakeForPtrMetadata
        | _ => throw "unknown raw pointer kind")
      return .RawPtr kind (← place ctx (← get fs "place"))
    | .cast => return .Cast (← castKind (← get fs "cast_kind")) (← operand ctx (← get fs "operand")) (← typeId ctx (← get fs "target_type"))
    | .aggregate => return .Aggregate (← aggregate ctx (← get fs "aggregate_kind")) (← (← array (← get fs "operands")).mapM (operand ctx))
    | .reborrow => return .Reborrow (← typeId ctx (← get fs "type")) (← mutability (← get fs "mutability")) (← place ctx (← get fs "place"))
    | .unknown name => throw s!"unknown rvalue {name}"
  | _ => throw "unsupported or malformed rvalue"

private def fakeRead (v : TypedValue) : LowerM MIR.FakeReadCause := do
  let fs ← fields v
  match ← tag v with
  | "match_guard" => pure .ForMatchGuard
  | "matched_place" => return .ForMatchedPlace (← optionalM definition (← get fs "hoisted_from"))
  | "guard_binding" => pure .ForGuardBinding
  | "let_binding" => return .ForLet (← optionalM definition (← get fs "hoisted_from"))
  | "index" => pure .ForIndex
  | _ => throw "unknown fake read cause"

private def variance (v : TypedValue) : LowerResult MIR.Variance := do
  match ← tag v with
  | "covariant" => pure .Covariant
  | "contravariant" => pure .Contravariant
  | "invariant" => pure .Invariant
  | "bivariant" => pure .Bivariant
  | _ => throw "unknown variance"

private def userProjectionKind : UserTypeProjectionKind → LowerResult MIR.ProjectionKind
  | .deref => pure .Deref
  | .field i => pure (.Field i)
  | .index => pure .Index
  | .constantIndex a b c => pure (.ConstantIndex a b c)
  | .subslice a b c => pure (.Subslice a b c)
  | .downcast a b => pure (.Downcast a b)
  | .opaqueCast => pure .OpaqueCast
  | .unwrapUnsafeBinder => pure .UnwrapUnsafeBinder
  | .phantomDeref => pure .PhantomDeref
  | .unknown name => throw s!"unknown user projection {name}"

private def userProjection : TypedValue → LowerResult MIR.UserTypeProjection
  | .userTypeProjection p => do
    unless p.status == .supported do throw "unsupported user projection"
    let some base := p.baseIndex | throw "missing user projection base"
    let some ps := p.projections | throw "missing user projections"
    return ⟨base, ← ps.mapM userProjectionKind⟩
  | _ => throw "missing typed user projection"

private def coverage (v : TypedValue) : LowerM MIR.CoverageKind := do
  let fs ← fields v
  match ← tag v with
  | "point" =>
    let kind ← (show LowerM MIR.CoveragePointKind from match ← tag (← get fs "point_kind") with
      | "expr" => pure .Expr
      | "implicit_else" => pure .ImplicitElse
      | "function_end" => pure .FunctionEnd
      | _ => throw "unknown coverage point")
    let hir ← fields (← get fs "hir_id")
    return .Point kind ⟨← definition (← get hir "owner_def_id"), ← nat (← get hir "local_id")⟩
  | "block_marker" => return .BlockMarker (← nat (← get fs "id"))
  | "virtual_counter" => return .VirtualCounter (← nat (← get fs "bcb"))
  | _ => throw "unknown coverage kind"

private def statement (ctx : LowerContext) (node : MirNode) : LowerM MIR.Statement := do
  let kind ← (show LowerM MIR.StatementKind from match node.value with
    | .statement k _ fs => do
      match k with
      | .assign => return MIR.StatementKind.Assign (← place ctx (← get fs "place")) (← rvalue ctx (← get fs "rvalue"))
      | .storageLive => return .StorageLive (← nat (← get fs "local"))
      | .storageDead => return .StorageDead (← nat (← get fs "local"))
      | .placeMention => return .PlaceMention (← place ctx (← get fs "place"))
      | .setDiscriminant => return .SetDiscriminant (← place ctx (← get fs "place")) (← nat (← get fs "variant_index"))
      | .constEvalCounter => pure .ConstEvalCounter
      | .nop => pure .Nop
      | .fakeRead => return .FakeRead (← fakeRead (← get fs "cause")) (← place ctx (← get fs "place"))
      | .ascribeUserType => return .AscribeUserType (← place ctx (← get fs "place")) (← userProjection (← get fs "user_type_projection")) (← variance (← get fs "variance"))
      | .coverage => return .Coverage (← coverage (← get fs "coverage"))
      | .intrinsic =>
        let intrinsic ← (show LowerM MIR.NonDivergingIntrinsic from match ← text (← get fs "intrinsic") with
          | "Assume" => return .Assume (← operand ctx (← get fs "value"))
          | "CopyNonOverlapping" => return .CopyNonOverlapping ⟨← operand ctx (← get fs "src"), ← operand ctx (← get fs "dst"), ← operand ctx (← get fs "count")⟩
          | _ => throw "unknown nondiverging intrinsic")
        pure (.Intrinsic intrinsic)
      | .backwardIncompatibleDropHint =>
        unless (← tag (← get fs "reason")) == "edition_2024" do throw "unknown backward drop reason"
        return .BackwardIncompatibleDropHint (← place ctx (← get fs "place")) .Edition2024
      | .unknown name => throw s!"unknown statement {name}"
    | _ => throw "unsupported or malformed statement")
  return ⟨← source node.sourceInfo, kind⟩

private def unwindReason (v : TypedValue) : LowerResult MIR.UnwindTerminateReason := do
  match ← tag v with
  | "abi" => pure .Abi
  | "in_cleanup" => pure .InCleanup
  | _ => throw "unknown unwind termination reason"

private def coroutine (v : TypedValue) : LowerResult MIR.CoroutineKind := do
  let fs ← fields v
  match ← tag v with
  | "desugared" =>
    let desugaring ← (show LowerResult MIR.CoroutineDesugaring from match ← text (← get fs "desugaring") with
      | "async" => pure .Async
      | "gen" => pure .Gen
      | "async_gen" => pure .AsyncGen
      | _ => throw "unknown coroutine desugaring")
    let source ← (show LowerResult MIR.CoroutineSource from match ← text (← get fs "source") with
      | "block" => pure .Block
      | "closure" => pure .Closure
      | "function" => pure .Fn
      | _ => throw "unknown coroutine source")
    pure (.Desugared desugaring source)
  | "coroutine" =>
    match ← text (← get fs "movability") with
    | "static" => pure (.Coroutine .Static)
    | "movable" => pure (.Coroutine .Movable)
    | _ => throw "unknown coroutine movability"
  | _ => throw "unknown coroutine kind"

private def unwind (v : TypedValue) : LowerResult MIR.UnwindAction := do
  let fs ← fields v
  match ← text (← get fs "kind") with
  | "Continue" => pure .Continue
  | "Unreachable" => pure .Unreachable
  | "Cleanup" => return .Cleanup (← nat (← get fs "target"))
  | "Terminate" => return .Terminate (← unwindReason (← get fs "reason"))
  | _ => throw "unknown unwind action"

private def assertKind (ctx : LowerContext) (v : TypedValue) : LowerM MIR.AssertKind := do
  let fs ← fields v
  match ← tag v with
  | "Overflow" =>
    let op ← match ← get fs "operator" with
      | .binOperator op .supported => pure op
      | _ => throw "unsupported assertion operator"
    return .Overflow op (← operand ctx (← get fs "left")) (← operand ctx (← get fs "right"))
  | "BoundsCheck" => return .BoundsCheck (← operand ctx (← get fs "length")) (← operand ctx (← get fs "index"))
  | "OverflowNeg" => return .OverflowNeg (← operand ctx (← get fs "operand"))
  | "DivisionByZero" => return .DivisionByZero (← operand ctx (← get fs "operand"))
  | "RemainderByZero" => return .RemainderByZero (← operand ctx (← get fs "operand"))
  | "NullPointerDereference" => pure .NullPointerDereference
  | "NullReferenceConstructed" => pure .NullReferenceConstructed
  | "ResumedAfterReturn" => return .ResumedAfterReturn (← coroutine (← get fs "coroutine_kind"))
  | "ResumedAfterPanic" => return .ResumedAfterPanic (← coroutine (← get fs "coroutine_kind"))
  | "ResumedAfterDrop" => return .ResumedAfterDrop (← coroutine (← get fs "coroutine_kind"))
  | "MisalignedPointerDereference" => return .MisalignedPointerDereference (← operand ctx (← get fs "required")) (← operand ctx (← get fs "found"))
  | "InvalidEnumConstruction" => return .InvalidEnumConstruction (← operand ctx (← get fs "operand"))
  | _ => throw "unknown assertion kind"

private def loopHint (v : TypedValue) : LowerResult MIR.LoopHintAttr := do
  let fs ← fields v
  match ← text (← get fs "kind") with
  | "Hint" => pure .Hint
  | "Full" => pure .Full
  | "Never" => pure .Never
  | "Count" => return .Count (← nat (← get fs "count"))
  | _ => throw "unknown loop hint"

private def callSource (v : TypedValue) : LowerResult MIR.CallSource := do
  match ← tag v with
  | "overloaded_operator" => pure .OverloadedOperator
  | "match_comparison" => pure .MatchCmp
  | "miscellaneous_desugaring" => pure .Misc
  | "clone_or_use" => pure .Use
  | "normal_call" => pure .Normal
  | _ => throw "unknown call source"

private def spannedOperand (ctx : LowerContext) (v : TypedValue) : LowerM MIR.SpannedOperand := do
  let fs ← fields v
  return ⟨← spanRef (← get fs "span"), ← operand ctx (← get fs "operand")⟩

private def asmArch (v : TypedValue) : LowerResult MIR.InlineAsmArch := do
  match ← text v with
  | "X86" => pure .X86
  | "X86_64" => pure .X86_64
  | "Arm" => pure .Arm
  | "Arm64EC" => pure .Arm64EC
  | "AArch64" => pure .AArch64
  | "Amdgpu" => pure .Amdgpu
  | "RiscV32" => pure .RiscV32
  | "RiscV64" => pure .RiscV64
  | "Nvptx64" => pure .Nvptx64
  | "PowerPC" => pure .PowerPC
  | "PowerPC64" => pure .PowerPC64
  | "Hexagon" => pure .Hexagon
  | "LoongArch32" => pure .LoongArch32
  | "LoongArch64" => pure .LoongArch64
  | "Mips" => pure .Mips
  | "Mips64" => pure .Mips64
  | "Xtensa" => pure .Xtensa
  | "S390x" => pure .S390x
  | "Sparc" => pure .Sparc
  | "Sparc64" => pure .Sparc64
  | "SpirV" => pure .SpirV
  | "Wasm32" => pure .Wasm32
  | "Wasm64" => pure .Wasm64
  | "Bpf" => pure .Bpf
  | "Avr" => pure .Avr
  | "Msp430" => pure .Msp430
  | "M68k" => pure .M68k
  | "CSKY" => pure .CSky
  | _ => throw "unknown assembly architecture"

private def asmRegister (v : TypedValue) : LowerResult MIR.InlineAsmRegOrRegClass := do
  let fs ← fields v
  let arch ← asmArch (← get fs "arch")
  let name ← text (← get fs "name")
  match ← tag v with
  | "register" => pure (.Reg arch name)
  | "register_class" => pure (.RegClass arch name)
  | _ => throw "unknown assembly register kind"

private def asmPiece (v : TypedValue) : LowerM MIR.InlineAsmTemplatePiece := do
  let fs ← fields v
  match ← tag v with
  | "string" => return .String (← text (← get fs "text"))
  | "placeholder" =>
    let modifier ← optional (fun value => do
      let s ← text value
      match s.toList with
      | [c] => pure c
      | _ => throw "assembly modifier must be one character") (← get fs "modifier")
    return .Placeholder (← nat (← get fs "operand_index")) modifier (← spanRef (← get fs "span"))
  | _ => throw "unknown assembly template piece"

private def asmOperand (ctx : LowerContext) (v : TypedValue) : LowerM MIR.InlineAsmOperand := do
  let fs ← fields v
  match ← tag v with
  | "in" => return .In (← asmRegister (← get fs "register")) (← operand ctx (← get fs "value"))
  | "out" => return .Out (← asmRegister (← get fs "register")) (← bool (← get fs "late")) (← optional (place ctx) (← get fs "place"))
  | "inout" => return .InOut (← asmRegister (← get fs "register")) (← bool (← get fs "late")) (← operand ctx (← get fs "input")) (← optional (place ctx) (← get fs "output"))
  | "const" => return .Const (← constOperand ctx (← get fs "value"))
  | "sym_fn" => return .SymFn (← constOperand ctx (← get fs "value"))
  | "sym_static" => return .SymStatic (← definition (← get fs "def_id"))
  | "label" => return .Label (← nat (← get fs "target_index"))
  | _ => throw "unknown assembly operand"

private def inlineAsm (ctx : LowerContext) (fs : Fields) : LowerM MIR.InlineAsmTerminator := do
  let macroKind ← (show LowerM MIR.InlineAsmMacro from match ← text (← get fs "asm_macro") with
    | "asm" => pure .Asm
    | "naked_asm" => pure .NakedAsm
    | _ => throw "unknown assembly macro")
  let options ← fields (← get fs "options")
  let options : MIR.InlineAsmOptions := ⟨← bool (← get options "pure"), ← bool (← get options "nomem"),
    ← bool (← get options "readonly"), ← bool (← get options "preserves_flags"), ← bool (← get options "noreturn"),
    ← bool (← get options "nostack"), ← bool (← get options "att_syntax"), ← bool (← get options "raw"), ← bool (← get options "may_unwind")⟩
  let template ← (← array (← get fs "template")).mapM asmPiece
  let operands ← (← array (← get fs "operands")).mapM (asmOperand ctx)
  let spans ← (← array (← get fs "line_spans")).mapM spanRef
  let targets ← ((← array (← get fs "targets")).mapM nat : LowerResult _)
  for op in operands do
    match op with
    | .Label index => unless index < targets.size do throw "assembly label index exceeds target list"
    | _ => pure ()
  for piece in template do
    match piece with
    | .Placeholder index _ _ => unless index < operands.size do throw "assembly placeholder exceeds operand list"
    | _ => pure ()
  return ⟨macroKind, template, operands, options, spans, targets, ← unwind (← get fs "unwind")⟩

private def terminator (ctx : LowerContext) (node : MirNode) : LowerM MIR.Terminator := do
  let kind ← (show LowerM MIR.TerminatorKind from match node.value with
    | .terminator k _ fs => do
      match k with
      | .return => pure MIR.TerminatorKind.Return
      | .unreachable => pure .Unreachable
      | .unwindResume => pure .UnwindResume
      | .coroutineDrop => pure .CoroutineDrop
      | .assert => return .Assert (← operand ctx (← get fs "condition")) (← bool (← get fs "expected")) (← assertKind ctx (← get fs "message")) (← nat (← get fs "target")) (← unwind (← get fs "unwind"))
      | .falseEdge => return .FalseEdge (← nat (← get fs "real_target")) (← nat (← get fs "imaginary_target"))
      | .goto =>
        let hints ← array (← get fs "loop_hints")
        let lowered ← (hints.mapM loopHint : LowerResult _ )
        return .Goto (← nat (← get fs "target")) lowered
      | .switchInt =>
        let cases ← (← array (← get fs "targets")).mapM fun entry => do
          let ef ← fields entry
          pure (MIR.SwitchTarget.Case (← number (← get ef "value")) (← nat (← get ef "target")))
        return .SwitchInt (← operand ctx (← get fs "discriminant")) ⟨cases, ← nat (← get fs "otherwise")⟩
      | .unwindTerminate => return .UnwindTerminate (← unwindReason (← get fs "reason"))
      | .drop => return .Drop (← place ctx (← get fs "place")) (← nat (← get fs "target")) (← unwind (← get fs "unwind")) (← bool (← get fs "replace")) (← optional nat (← get fs "async_drop"))
      | .call => return .Call (← operand ctx (← get fs "function")) (← (← array (← get fs "args")).mapM (spannedOperand ctx)) (← place ctx (← get fs "destination")) (← optional nat (← get fs "target")) (← unwind (← get fs "unwind")) (← callSource (← get fs "call_source")) (← spanRef (← get fs "function_span"))
      | .tailCall => return .TailCall (← operand ctx (← get fs "function")) (← (← array (← get fs "args")).mapM (spannedOperand ctx)) (← spanRef (← get fs "function_span"))
      | .yield => return .Yield (← operand ctx (← get fs "value")) (← nat (← get fs "resume")) (← place ctx (← get fs "resume_arg")) (← optional nat (← get fs "drop"))
      | .falseUnwind => return .FalseUnwind (← nat (← get fs "real_target")) (← unwind (← get fs "unwind"))
      | .inlineAsm => return .InlineAsm (← inlineAsm ctx fs)
      | .unknown name => throw s!"unknown terminator {name}"
    | _ => throw "unsupported or malformed terminator")
  return ⟨← source node.sourceInfo, kind⟩

private def phase : TypedValue → LowerResult MIR.MirPhase
  | .enumTag .mirPhase t fs => do
    unless t.status == .supported do throw "unsupported MIR phase"
    match t.tag with
    | "built" => pure .Built
    | "analysis" =>
      match ← tag (← get fs "phase") with
      | "initial" => pure (.Analysis .Initial)
      | "post_cleanup" => pure (.Analysis .PostCleanup)
      | _ => throw "unknown analysis phase"
    | "runtime" =>
      match ← tag (← get fs "phase") with
      | "initial" => pure (.Runtime .Initial)
      | "post_cleanup" => pure (.Runtime .PostCleanup)
      | "optimized" => pure (.Runtime .Optimized)
      | _ => throw "unknown runtime phase"
    | _ => throw "unknown MIR phase"
  | _ => .error "missing typed MIR phase"

private partial def validateReferences (ctx : LowerContext) (locals blocks : Nat)
    (v : TypedValue) : LowerResult Unit := do
  match v with
  | .typeRef id => unless ctx.containsTypeId id do throw s!"unresolved type {id}"
  | .allocationRef id => unless ctx.containsAllocationId id do throw s!"unresolved allocation {id}"
  | .localRef id => unless id < locals do throw s!"out-of-range local {id}"
  | .blockRef id => unless id < blocks do throw s!"out-of-range block {id}"
  | .array vs => for child in vs do validateReferences ctx locals blocks child
  | .object fs | .statement _ _ fs | .terminator _ _ fs | .rvalue _ _ fs
  | .operand _ _ fs | .projection _ fs | .enumTag _ _ fs =>
    for (_, child) in fs do validateReferences ctx locals blocks child
  | .unknownBinOperator name _ | .unknownUnOperator name _ => throw s!"unknown operator {name}"
  | .diagnostic _ => pure ()
  | _ => pure ()

private def statusObligations (status : PayloadStatus) (path : String) : Array Obligation :=
  if status == .supported then #[] else #[⟨path, s!"compiler payload status remains {repr status}; syntax construction does not discharge execution obligations"⟩]

private def isValidatedProbeLeaf (sourceDocument : Option Lean.Json) (path : String) : Bool :=
  match sourceDocument with
  | some source => exactVtableProbeDiagnostic source path
  | none => false

private partial def payloadObligations (sourceDocument : Option Lean.Json)
    (v : TypedValue) (path : String) : Array Obligation := Id.run do
  match v with
  | .array vs => return (vs.toList.zipIdx).foldl (fun out (child, i) => out ++ payloadObligations sourceDocument child s!"{path}[{i}]") #[]
  | .diagnostic _ => return #[⟨path, "diagnostic-only compiler metadata remains unresolved"⟩]
  | _ => pure ()
  let (own, children) : Array Obligation × Fields := match v with
    | .statement _ status fs | .terminator _ status fs | .rvalue _ status fs | .operand _ status fs => (statusObligations status path, fs)
    | .enumTag _ t fs => (statusObligations t.status path, fs)
    | .object fs | .projection _ fs => (#[], fs)
    | _ => (#[], #[])
  let mut out := own
  for (key, child) in children do
    if key == "status" then
      match child with
      | .scalar (.str status) =>
        unless status == "supported" || status == "complete" ||
            (status != "supported" && isValidatedProbeLeaf sourceDocument (path ++ ".status")) do
          out := out.push ⟨path, s!"compiler metadata status remains {status}"⟩
      | _ => pure ()
    out := out ++ payloadObligations sourceDocument child (path ++ "." ++ key)
  return out

private def unwindTargets : MIR.UnwindAction → Array Nat
  | .Cleanup target => #[target]
  | .Continue | .Unreachable | .Terminate _ => #[]

private def controlTargets : MIR.TerminatorKind → Array Nat
  | .Goto target _ => #[target]
  | .SwitchInt _ targets => targets.cases.map (fun (.Case _ target) => target) ++ #[targets.otherwise]
  | .Drop _ target unwind _ asyncDrop => #[target] ++ unwindTargets unwind ++ asyncDrop.toArray
  | .Call _ _ _ target unwind _ _ => target.toArray ++ unwindTargets unwind
  | .Assert _ _ _ target unwind => #[target] ++ unwindTargets unwind
  | .Yield _ resume _ drop => #[resume] ++ drop.toArray
  | .FalseEdge real imaginary => #[real, imaginary]
  | .FalseUnwind real unwind => #[real] ++ unwindTargets unwind
  | .InlineAsm asm => asm.targets ++ unwindTargets asm.unwind
  | .UnwindResume | .UnwindTerminate _ | .Return | .Unreachable | .TailCall .. | .CoroutineDrop => #[]

private def typedValueMatchesSource (source : Lean.Json) (path : String)
    (value : TypedValue) : Bool := Id.run do
  let some raw := jsonAtPath source path | return false
  match decodeCompilerValue raw with
  | .ok decoded => return decoded == value
  | .error _ => return false

/-- Recheck that the typed MIR nodes used by lowering are exactly the ones
decoded from the same raw body. Retaining only a raw payload/path is not enough:
callers can construct or mutate an ImportDocument after decoding. -/
private def sourceBodyMatches (source : Lean.Json) (input : BodyCore) : Bool := Id.run do
  unless input.sourcePath.startsWith "$." && jsonAtPath source input.sourcePath == some input.payload do
    return false
  let some rawBlocks := ((input.payload.getObjVal? "basic_blocks").bind Lean.Json.getArr?).toOption
    | return false
  unless rawBlocks.size == input.blocks.size do return false
  for (block, index) in input.blocks.toList.zipIdx do
    let some rawBlock := rawBlocks[index]? | return false
    unless block.payload == rawBlock do return false
    unless (rawBlock.getObjValAs? Nat "block").toOption == some block.id do return false
    let some rawStatements := ((rawBlock.getObjVal? "statements").bind Lean.Json.getArr?).toOption
      | return false
    unless rawStatements.size == block.statements.size do return false
    for (node, statementIndex) in block.statements.toList.zipIdx do
      let path := s!"{input.sourcePath}.basic_blocks[{index}].statements[{statementIndex}].kind"
      unless typedValueMatchesSource source path node.value do return false
    let terminatorPath := s!"{input.sourcePath}.basic_blocks[{index}].terminator.kind"
    unless typedValueMatchesSource source terminatorPath block.terminator.value do return false
  return true

/-- Construct source-shaped MIR, preserving its decoded envelope and interning
actual source spans. Unsupported constructors and missing metadata are errors. -/
private def lowerBodyState (ctx : LowerContext) (input : BodyCore) (initial : LowerState) : LowerResult (LoweredBody × LowerState) := do
  let sourceDocument := match ctx.sourceDocument with
    | some source => if sourceBodyMatches source input then some source else none
    | none => none
  let mirPhase ← phase input.phase
  match input.injectionPhase with
  | some value => let _ ← phase value; pure ()
  | none => pure ()
  unless !input.blocks.isEmpty do throw "body has no entry basic block"
  let scopes ← match input.sourceScopes with
    | some scopes => pure scopes
    | none => throw "missing source scope metadata"
  for decl in input.locals do
    unless decl.sourceInfo.scope < scopes.size do throw "unresolved local source scope"
  unless input.argumentCount < input.locals.size do throw "argument count exceeds locals"
  for (decl, i) in input.locals.toList.zipIdx do
    unless decl.id == i do throw "noncontiguous local IDs"
    unless ctx.containsTypeId decl.typeId do throw s!"unresolved local type {decl.typeId}"
  for (block, i) in input.blocks.toList.zipIdx do
    unless block.id == i do throw "noncontiguous basic block IDs"
    for node in block.statements.push block.terminator do
      unless node.sourceInfo.scope < scopes.size do throw "unresolved instruction source scope"
      validateReferences ctx input.locals.size input.blocks.size node.value
  match input.spreadArgument with
  | some arg => unless arg > 0 && arg ≤ input.argumentCount do throw "invalid spread argument"
  | none => pure ()
  let action : LowerM (Array MIR.BasicBlock) := input.blocks.mapM fun block => do
    return ⟨← block.statements.mapM (statement ctx), ← terminator ctx block.terminator, block.cleanup⟩
  let initial := match input.definitionId with
    | some sourceId =>
      addDefinition initial sourceId
    | none => initial
  let (blocks, state) ← action.run initial
  for block in blocks do
    for target in controlTargets block.terminator.kind do
      unless target < blocks.size do throw s!"out-of-range control-flow target {target}"
  let obligations := input.blocks.toList.zipIdx.foldl (fun out (block, blockIndex) => Id.run do
    let bodyPrefix := if input.sourcePath.isEmpty then "" else input.sourcePath ++ "."
    let blockPrefix := s!"{bodyPrefix}basic_blocks[{blockIndex}]"
    let statements := block.statements.toList.zipIdx.foldl (fun issues (node, statementIndex) =>
      issues ++ payloadObligations sourceDocument node.value
        s!"{blockPrefix}.statements[{statementIndex}].kind") #[]
    let terminator := payloadObligations sourceDocument block.terminator.value
      s!"{blockPrefix}.terminator.kind"
    return out ++ statements ++ terminator) ctx.obligations
  let obligations := if input.definitionId.isSome then obligations else
    obligations.push ⟨"body.definitionId", "source definition identity is missing; runtime frame initialization must fail until supplied"⟩
  return (⟨⟨mirPhase, input.argumentCount, input.spreadArgument, input.locals.map (·.typeId), blocks⟩, state.spans, input, state.definitions, state.typeConstants, obligations⟩, state)

/-- A standalone body's definition/type-constant/span IDs are local to this
result. Use `lowerBodies` or `lowerProgram` for cross-function linking. -/
def lowerBody (ctx : LowerContext) (input : BodyCore) : LowerResult LoweredBody :=
  (lowerBodyState ctx input {}).map Prod.fst

structure LoweredBodies where
  bodies : Array LoweredBody
  spans : Array SourceSpanData
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst

/-- Lower a compilation's bodies through one shared interner, including
mutually recursive references. Every returned body uses the same ID tables. -/
def lowerBodies (ctx : LowerContext) (inputs : Array BodyCore)
    (seedDefinitions : Array DefinitionId := #[]) : LowerResult LoweredBodies := do
  let mut state : LowerState := { spanCandidates := some {}, definitionCandidates := some {} }
  for id in seedDefinitions do
    state := addDefinition state id
  -- Seed definition identities before traversing instructions: references to
  -- later and mutually recursive bodies resolve to the same dense identities.
  for input in inputs do
    if let some id := input.definitionId then
      state := addDefinition state id
  let mut bodies := #[]
  for input in inputs do
    let (body, next) ← lowerBodyState ctx input state
    bodies := bodies.push body
    state := next
  bodies := bodies.map fun body =>
    { body with
      spans := state.spans
      definitions := state.definitions
      typeConstants := state.typeConstants }
  pure ⟨bodies, state.spans, state.definitions, state.typeConstants⟩

structure LoweredProgram where
  bundle : LoweredBodies
  /-- Root body indices into `bundle.bodies`, in the original document order. -/
  roots : Array Nat
  /-- Instance graph identity to body index; the source graph is retained below. -/
  instances : Array (InstanceId × Nat)
  /-- (parent body index, promoted index, body index). -/
  promoted : Array (Nat × Nat × Nat)
  input : ImportDocumentCore

/-- Look up a document root's frame identity without assuming it was called
or that source and runtime definition indices coincide. -/
def LoweredProgram.rootDefinitionId (program : LoweredProgram) (rootIndex : Nat)
    : LowerResult MIR.DefId := do
  let some bodyIndex := program.roots[rootIndex]? | throw "root index is out of range"
  let some body := program.bundle.bodies[bodyIndex]? | throw "root body index is out of range"
  body.ownDefinitionId

/-- Lower all present root, instance, and promoted bodies with global compiler
identity tables. Unavailable bodies remain explicit source graph obligations. -/
def lowerCoreProgram (input : ImportDocumentCore) : LowerResult LoweredProgram := do
  let mut inputs : Array BodyCore := #[]
  let mut roots := #[]
  let mut instances := #[]
  let mut promoted := #[]
  for body in input.bodies do
    let parent := inputs.size
    roots := roots.push parent
    inputs := inputs.push body.toBodyCore
    for child in body.promotedBodies do
      if let some childBody := child.body then
        promoted := promoted.push (parent, child.index, inputs.size)
        inputs := inputs.push childBody
  for inst in input.instances do
    if let some body := inst.body then
      let parent := inputs.size
      instances := instances.push (inst.id, parent)
      inputs := inputs.push body.toBodyCore
      let children := if body.promotedBodies.isEmpty then inst.promotedBodies else body.promotedBodies
      for child in children do
        if let some childBody := child.body then
          promoted := promoted.push (parent, child.index, inputs.size)
          inputs := inputs.push childBody
  -- The complete source body list includes root/instance/promoted identities;
  -- seed all of them explicitly, plus graph instances that have no MIR body.
  let definitions := inputs.filterMap (·.definitionId) ++ input.instances.filterMap (·.definitionId)
  pure ⟨← lowerBodies (LowerContext.ofDocument input) inputs definitions, roots, instances, promoted, input⟩

/-- Compatibility entrypoint for full diagnostic documents. Runtime clients
that decode without retaining the typed JSON tree should call
`lowerCoreProgram`. -/
def lowerProgram (input : ImportDocument) : LowerResult LoweredProgram :=
  lowerCoreProgram input.toCore

/-- Interner state shared by metadata-query lowering and MIR syntax. Appending
entries preserves every previously lowered ID. -/
structure CompilerTables where
  spans : Array SourceSpanData
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst

def LoweredProgram.compilerTables (program : LoweredProgram) : CompilerTables :=
  ⟨program.bundle.spans, program.bundle.definitions, program.bundle.typeConstants⟩

def LoweredProgram.withCompilerTables (program : LoweredProgram) (tables : CompilerTables) : LoweredProgram :=
  let bodies := program.bundle.bodies.map fun body => { body with
    spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  { program with bundle := ⟨bodies, tables.spans, tables.definitions, tables.typeConstants⟩ }

def lowerCompilerGenericArgs (ctx : LowerContext) (tables : CompilerTables) (value : TypedValue) :
    LowerResult (Array MIR.GenericArg × CompilerTables) := do
  let (args, state) ← (genericArgs ctx value).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (args, ⟨state.spans, state.definitions, state.typeConstants⟩)

def lowerCompilerConstOperand (ctx : LowerContext) (tables : CompilerTables) (value : TypedValue) :
    LowerResult (MIR.ConstOperand × CompilerTables) := do
  let (operand, state) ← (constOperand ctx value).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (operand, ⟨state.spans, state.definitions, state.typeConstants⟩)

def lowerCompilerConstValue (ctx : LowerContext) (ty : MIR.TyId) (value : TypedValue) :
    LowerResult MIR.ConstValue := constValue ctx ty value

/-- Canonical type-constant interning for compiler pattern/query metadata. -/
def lowerCompilerTypeConst (ctx : LowerContext) (tables : CompilerTables) (value : TypedValue) :
    LowerResult (MIR.TypeConstId × CompilerTables) := do
  let (id, state) ← (do internTypeConst (← typeConst ctx value)).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (id, ⟨state.spans, state.definitions, state.typeConstants⟩)

/-- Intern a compiler span without synthesizing a source location. -/
def lowerCompilerSpan (tables : CompilerTables) (value : TypedValue) :
    LowerResult (MIR.SpanRef × CompilerTables) := do
  let (id, state) ← (spanRef value).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (id, ⟨state.spans, state.definitions, state.typeConstants⟩)

private structure SpanArrayReflexivity (spans : Array SourceSpanData) where
  reflexive : (spans == spans) = true

private theorem SpanArrayReflexivity.prepare
    (spans : Array SourceSpanData) : SpanArrayReflexivity spans :=
  ⟨by simp⟩

private def SpanArrayReflexivity.matchesRight
    {spans : Array SourceSpanData}
    (certificate : SpanArrayReflexivity spans)
    (candidate : Array SourceSpanData) : Bool :=
  withPtrEq spans candidate (fun _ => spans == candidate)
    (by intro equal; cases equal; exact certificate.reflexive)

private theorem SpanArrayReflexivity.matchesRight_eq
    {spans : Array SourceSpanData}
    (certificate : SpanArrayReflexivity spans)
    (candidate : Array SourceSpanData) :
    certificate.matchesRight candidate = (spans == candidate) := by
  simp [matchesRight, withPtrEq]

/-- Incremental exact span interning for compiler source-map batches. The
candidate index is seeded once from the existing table; buckets only narrow
the search and full span equality remains authoritative. -/
structure CompilerSpanInterner where
  private mk ::
  private tables : CompilerTables
  private candidates : Std.HashMap (String × Nat × Nat) (Array Nat)
  private spanReflexivity : SpanArrayReflexivity tables.spans

def CompilerSpanInterner.ofTables (tables : CompilerTables) : CompilerSpanInterner := Id.run do
  let mut candidates : Std.HashMap (String × Nat × Nat) (Array Nat) := {}
  for index in [:tables.spans.size] do
    if let some span := tables.spans[index]? then
      let key := spanCandidateKey span
      candidates := candidates.insert key ((candidates.getD key #[]).push index)
  return ⟨tables, candidates, .prepare tables.spans⟩

/-- Reuse an index only when the complete span arrays compare equal. The
certificate makes the common same-array case constant time while preserving a
full equality check for independently allocated or reordered tables. -/
def CompilerSpanInterner.rebind (interner : CompilerSpanInterner) (tables : CompilerTables) :
    CompilerSpanInterner :=
  if interner.spanReflexivity.matchesRight tables.spans then
    ⟨{ tables with spans := interner.tables.spans }, interner.candidates,
      interner.spanReflexivity⟩
  else
    .ofTables tables

def CompilerSpanInterner.getTables (interner : CompilerSpanInterner) : CompilerTables :=
  interner.tables

def lowerCompilerSpanWithInterner (interner : CompilerSpanInterner) (value : TypedValue) :
    LowerResult (MIR.SpanRef × CompilerSpanInterner) := do
  let (id, state) ← (spanRef value).run
    { spans := interner.tables.spans
      definitions := interner.tables.definitions
      typeConstants := interner.tables.typeConstants
      spanCandidates := some interner.candidates }
  let tables : CompilerTables := ⟨state.spans, state.definitions, state.typeConstants⟩
  return (id, ⟨tables, state.spanCandidates.getD interner.candidates,
    .prepare state.spans⟩)

/-- Compare the result of an independent lowering against the unchanged base.
The checked pointer shortcut retains the full original array comparator. -/
def CompilerSpanInterner.sameSpansAs (result base : CompilerSpanInterner) : Bool :=
  base.spanReflexivity.matchesRight result.tables.spans

theorem CompilerSpanInterner.sameSpansAs_eq (result base : CompilerSpanInterner) :
    result.sameSpansAs base = (base.getTables.spans == result.getTables.spans) := by
  exact base.spanReflexivity.matchesRight_eq result.tables.spans

/-- Lower a compiler constant operand using an exact, persistent span index. -/
def lowerCompilerConstOperandWithInterner (ctx : LowerContext)
    (interner : CompilerSpanInterner) (value : TypedValue) :
    LowerResult (MIR.ConstOperand × CompilerSpanInterner) := do
  let (operand, state) ← (constOperand ctx value).run
    { spans := interner.tables.spans
      definitions := interner.tables.definitions
      typeConstants := interner.tables.typeConstants
      spanCandidates := some interner.candidates }
  let tables : CompilerTables := ⟨state.spans, state.definitions, state.typeConstants⟩
  return (operand, ⟨tables, state.spanCandidates.getD interner.candidates,
    .prepare state.spans⟩)

/-- Decode the source place key for compiler query evidence. Projection types
must already belong to the shared input type graph. -/
def lowerCompilerPlace (ctx : LowerContext) (value : TypedValue) : LowerResult MIR.Place :=
  place ctx value

end Miri.Input
