import Lean
import Miri.Memory.CtfeProvenance
import Miri.MIR.Operators

/-!
Typed data model for the pinned rustc MIR export.  These structures describe
compiler input only; neither a `supported` tag nor successful decoding is a
claim that Lean has implemented the corresponding Miri operation.
-/

namespace Miri.Input

abbrev TypeId := Nat
abbrev AllocationId := Nat
abbrev InstanceId := Nat
abbrev LocalId := Nat
abbrev BlockId := Nat

inductive PayloadStatus where
  | supported
  | unsupported
  | unknown
  | incomplete
  | debugPayload
  | unrecognized (value : String)
  deriving Repr, DecidableEq

inductive TypeShapeKind where
  | bool | char | int | uint | float | adt | foreign | str | array
  | patternType | slice | rawPointer | reference | functionDefinition
  | functionPointer | unsafeBinder | dynamicTraitObject | closure
  | coroutineClosure | coroutine | coroutineWitness | never | tuple
  | alias | parameter | boundType | placeholderType | inferenceType
  | errorType | unknown (value : String)
  deriving Repr, DecidableEq

inductive StatementVariant where
  | assign | fakeRead | setDiscriminant | storageLive | storageDead
  | placeMention | ascribeUserType | coverage | intrinsic
  | constEvalCounter | nop | backwardIncompatibleDropHint
  | unknown (value : String)
  deriving Repr, DecidableEq

inductive TerminatorVariant where
  | goto | switchInt | unwindResume | unwindTerminate | return
  | unreachable | drop | call | tailCall | assert | yield
  | coroutineDrop | falseEdge | falseUnwind | inlineAsm
  | unknown (value : String)
  deriving Repr, DecidableEq

inductive RvalueVariant where
  | use | repeat | ref | threadLocalRef | rawPtr | cast | binaryOp
  | unaryOp | discriminant | aggregate | copyForDeref
  | wrapUnsafeBinder | reborrow | unknown (value : String)
  deriving Repr, DecidableEq

inductive OperandVariant where
  | copy | move | constant | runtimeChecks | unknown (value : String)
  deriving Repr, DecidableEq

inductive ProjectionVariant where
  | deref | field | index | constantIndex | subslice | downcast
  | opaqueCast | unwrapUnsafeBinder | phantomDeref
  | unknown (value : String)
  deriving Repr, DecidableEq

inductive LayoutKind where
  | layout | layoutQueryError | unknown (value : String)
  deriving Repr, DecidableEq

inductive LayoutVariantsKind where
  | single | multiple | empty | unknown (value : String)
  deriving Repr, DecidableEq

inductive BackendReprKind where
  | scalar | scalarPair | memory | simdVector | scalableSimdVector
  | unknown (value : String)
  deriving Repr, DecidableEq

inductive FieldShapeKind where
  | primitive | union | array | arbitrary | unknown (value : String)
  deriving Repr, DecidableEq

inductive IntegerTypeTag where
  | known (kind : Miri.MIR.IntegerKind)
  | unknown (value : String)
  deriving Repr, DecidableEq

inductive FloatTypeTag where
  | f16 | f16b | f32 | f64 | f128 | ppcf128 | unknown (value : String)
  deriving Repr, DecidableEq

inductive AdtKind where
  | structKind | unionKind | enumKind | unknown (value : String)
  deriving Repr, DecidableEq

structure TypeShapeMetadata where
  signedKind : Option IntegerTypeTag
  unsignedKind : Option IntegerTypeTag
  floatKind : Option FloatTypeTag
  adtKind : Option AdtKind
  deriving Repr, DecidableEq

inductive PrimitiveKind where
  | integer | float | pointer | unknown (value : String)
  deriving Repr, DecidableEq

inductive ScalarShapeKind where
  | initialized | union | unknown (value : String)
  deriving Repr, DecidableEq


inductive PassModeKind where
  | ignore | direct | pair | cast | indirect | indirectUnsized | unknown (value : String)
  deriving Repr, DecidableEq

inductive AllocationKind where
  | memory | function | static | vtable | typeId
  | other (value : String) | unknown
  deriving Repr, DecidableEq

inductive InstanceKind where
  | instanceMir | instanceMirTemplate | intrinsicWithoutMir | intrinsicDispatch
  | foreignItemNoMir
  | virtualDispatch | virtualDispatchTarget | instanceMirUnavailable
  | symbolIdentityOnly
  | other (value : String)
  deriving Repr, DecidableEq

structure Obligation where
  path : String
  message : String
  deriving Repr, DecidableEq

/-- Exact source coordinate payload emitted by the pinned rustc span exporter.
`file` and `context` retain the compiler's diagnostic spellings; no consumer
should parse them to recover instruction semantics. -/
structure SourcePosition where
  line : Nat
  column : Nat
  deriving Repr, DecidableEq

structure SourceSpanData where
  originalPayload : String
  lo : Nat
  hi : Nat
  start : SourcePosition
  «end» : SourcePosition
  context : String
  file : String
  deriving Repr, DecidableEq

structure SourceInfo where
  span : SourceSpanData
  scope : Nat
  deriving Repr, DecidableEq

structure Producer where
  miriCommit : String
  rustcCommit : String
  rustcVersion : String
  targetTriple : String
  deriving Repr, DecidableEq

structure TaggedNode where
  status : PayloadStatus
  tag : String
  -- Kept for round-tripping and diagnostics.  Semantic consumers must use the
  -- typed tag/status and explicitly decoded children, never inspect debug text.
  payload : Lean.Json
  deriving BEq

structure FieldShape where
  kind : FieldShapeKind
  fieldCount : Nat
  offsetBytes : Option Nat
  strideBytes : Option Nat
  offsetsBytes : Array Nat
  memoryOrder : Array Nat
  payload : Lean.Json

structure PrimitiveLayout where
  kind : PrimitiveKind
  sizeBytes : Nat
  integerKind : Option IntegerTypeTag
  signed : Option Bool
  floatKind : Option FloatTypeTag
  addressSpace : Option Nat
  payload : Lean.Json

structure ScalarLayout where
  kind : ScalarShapeKind
  primitive : PrimitiveLayout
  validRange : Option (Nat × Nat)
  payload : Lean.Json

structure BackendRepr where
  kind : BackendReprKind
  sized : Option Bool
  scalar : Option ScalarLayout
  first : Option ScalarLayout
  second : Option ScalarLayout
  secondOffsetBytes : Option Nat
  element : Option ScalarLayout
  laneCount : Option Nat
  vectorCount : Option Nat
  payload : Lean.Json

structure LayoutVariant where
  variantIndex : Nat
  sizeBytes : Nat
  backendRepr : BackendRepr
  fieldOffsetsBytes : Array Nat
  uninhabited : Bool
  payload : Lean.Json

inductive TagEncodingKind where
  | direct | niche | unknown (value : String)
  deriving Repr, DecidableEq

structure TagEncoding where
  status : PayloadStatus
  kind : TagEncodingKind
  untaggedVariant : Option Nat
  nicheVariants : Option (Nat × Nat)
  nicheStart : Option Nat
  payload : Lean.Json

structure VariantsLayout where
  kind : LayoutVariantsKind
  variantIndex : Option Nat
  tag : Option ScalarLayout
  tagEncoding : Option TagEncoding
  tagFieldIndex : Option Nat
  variants : Array LayoutVariant
  payload : Lean.Json

structure Layout where
  status : PayloadStatus
  kind : LayoutKind
  sizeBytes : Option Nat
  abiAlignBytes : Option Nat
  unadjustedAbiAlignBytes : Option Nat
  fieldOffsetsBytes : Array Nat
  fields : Option FieldShape
  variantsLayout : Option VariantsLayout
  backendRepresentation : Option BackendRepr
  variantsKind : Option LayoutVariantsKind
  backendReprKind : Option BackendReprKind
  variants : Option TaggedNode
  backendRepr : Option TaggedNode
  payload : Lean.Json

structure ExternAbi where
  kind : TaggedNode
  unwind : Option Bool
  sourceSpelling : Option String
  payload : Lean.Json

inductive ArmCallKind where
  | aapcs | cmseNonSecureCall | cmseNonSecureEntry | unknown (value : String)
  deriving Repr, DecidableEq

inductive InterruptCallKind where
  | avr | avrNonBlocking | msp430 | riscvMachine | riscvSupervisor | x86
  | unknown (value : String)
  deriving Repr, DecidableEq

inductive X86CallKind where
  | fastcall | stdcall | sysv64 | thiscall | vectorcall | win64
  | unknown (value : String)
  deriving Repr, DecidableEq

inductive CanonicalAbiKind where
  | c | rust | rustCold | rustPreserveNone | rustTail | custom | swift
  | arm | gpuKernel | interrupt | x86 | unknown (value : String)
  deriving Repr, DecidableEq

structure CanonicalAbi where
  status : PayloadStatus
  kind : CanonicalAbiKind
  armCall : Option ArmCallKind
  interruptKind : Option InterruptCallKind
  x86Call : Option X86CallKind
  payload : Lean.Json

inductive TypedEnumTag where
  | safety | borrowKind | fakeBorrowKind | mutBorrowKind | mutability
  | castKind | pointerCoercion | coercionSource | unwindReason
  | aggregateKind | unwindAction
  | mirPhase | mirPhaseStage | withRetag | runtimeCheck | fakeReadCause
  | callSource | backwardDropReason | regionKind | boundRegionKind
  | boundVarIndexKind | lateParamRegionKind | integerType | floatType | adtKind
  | variance | coverageKind | coveragePointKind | fakeBorrowRetagMode
  | other (value : String)
  deriving Repr, DecidableEq, Hashable

inductive UserTypeProjectionKind where
  | deref
  | field (index : Nat)
  | index
  | constantIndex (offset minLength : Nat) (fromEnd : Bool)
  | subslice (startIndex endIndex : Nat) (fromEnd : Bool)
  | downcast (name : Option String) (variantIndex : Nat)
  | opaqueCast
  | unwrapUnsafeBinder
  | phantomDeref
  | unknown (tag : String)
  deriving Repr, DecidableEq

structure UserTypeProjection where
  status : PayloadStatus
  baseIndex : Option Nat
  projections : Option (Array UserTypeProjectionKind)
  payload : Lean.Json
  deriving BEq

structure FunctionSignature where
  inputs : Array TypeId
  output : TypeId
  safety : TaggedNode
  abi : ExternAbi
  cVariadic : Bool

/-- Source compiler pattern AST; range endpoints retain original const payloads
until lowered through the shared TypeConst interner. -/
inductive CompilerPattern where
  | range (start finish : Lean.Json)
  | or (patterns : Array CompilerPattern)
  | notNull

/-- Exact rustc query evidence; unsupported is never interpreted as false. -/
structure CompilerBooleanEvidence where
  status : PayloadStatus
  value : Option Bool
  reason : Option String
  payload : Lean.Json
structure CompilerTypeEvidence where
  status : PayloadStatus
  /-- Supported null is an actual None result (e.g. builtin_deref). -/
  value : Option TypeId
  reason : Option String
  payload : Lean.Json
structure TypeCompilerFacts where
  typingEnvironment : String
  inputTypeId : TypeId
  booleanQueries : Array (String × CompilerBooleanEvidence)
  typeQueries : Array (String × CompilerTypeEvidence)
  adtPayload : Option Lean.Json
  captureNames : Option (Array (Option String)) := none
  captureNamesStatus : Option PayloadStatus := none
  payload : Lean.Json

structure TypeNode where
  pattern : Option CompilerPattern := none
  compilerFacts : Option TypeCompilerFacts := none
  id : TypeId
  display : String
  shapeStatus : PayloadStatus
  shapeKind : TypeShapeKind
  shapeMetadata : TypeShapeMetadata
  signature : Option FunctionSignature
  layout : Layout
  payload : Lean.Json

structure InitRange where
  initialized : Bool
  startBytes : Nat
  endBytesExclusive : Nat
  deriving Repr, DecidableEq

structure Relocation where
  storageOffsetBytes : Nat
  target : AllocationId
  targetOffsetEncodedBytes : String
  immutable : Bool
  sharedRef : Bool
  ctfeProvenance : Miri.Memory.CtfeProvenance
  deriving Repr, DecidableEq


inductive MemoryMutability where
  | mutable | immutable | unknown (value : String)
  deriving Repr, DecidableEq

structure AllocationMemory where
  sizeBytes : Nat
  alignBytes : Nat
  mutability : MemoryMutability
  bytesHex : String
  initializationRanges : Array InitRange
  relocations : Array Relocation
  deriving Repr, DecidableEq

structure AbiAttributes where
  noAlias : Bool
  noFree : Bool
  noUndef : Bool
  nonNull : Bool
  readOnly : Bool
  writable : Bool
  inRegister : Bool
  regularBits : Nat
  pointeeSizeBytes : Nat
  pointeeAlignBytes : Option Nat
  argExtension : TaggedNode
  captures : TaggedNode

inductive AbiRegisterKind where
  | integer | float | ppcF128 | vector | unknown (value : String)
  deriving Repr, DecidableEq

structure AbiRegister where
  kind : AbiRegisterKind
  sizeBits : Nat
  hintElement : Option TaggedNode
  payload : Lean.Json

structure AbiCastTarget where
  prefixRegisters : Array AbiRegister
  restOffsetBytes : Option Nat
  restRegister : AbiRegister
  restTotalBytes : Nat
  restIsConsecutive : Bool
  attributes : AbiAttributes
  payload : Lean.Json

structure AbiPassMode where
  kind : PassModeKind
  attributes : Array AbiAttributes
  castTarget : Option AbiCastTarget
  padI32Count : Option Nat
  addressSpace : Option Nat
  indirectMode : Option TaggedNode
  payload : Lean.Json

structure AbiArgument where
  typeId : TypeId
  /-- Physical compiler TyAndLayout for this FnAbi argument. The logical type
  remains `typeId`; Rust can adjust the ABI layout independently (notably the
  forced-thin virtual-call receiver). Legacy exports leave this unavailable. -/
  layout : Option Layout := none
  mode : AbiPassMode
  payload : Lean.Json

structure FunctionAbi where
  arguments : Array AbiArgument
  returnValue : AbiArgument
  callingConvention : CanonicalAbi
  canUnwind : Bool
  cVariadic : Bool
  fixedCount : Nat
  payload : Lean.Json

inductive TypedValue where
  | scalar (value : Lean.Json)
  | diagnostic (value : Lean.Json)
  | array (values : Array TypedValue)
  | object (fields : Array (String × TypedValue))
  | typeRef (id : TypeId)
  | allocationRef (id : AllocationId)
  | instanceRef (id : InstanceId)
  | localRef (id : LocalId)
  | blockRef (id : BlockId)
  | sourceSpan (value : SourceSpanData)
  | sourceInfo (value : SourceInfo)
  | statement (variant : StatementVariant) (status : PayloadStatus)
      (fields : Array (String × TypedValue))
  | terminator (variant : TerminatorVariant) (status : PayloadStatus)
      (fields : Array (String × TypedValue))
  | rvalue (variant : RvalueVariant) (status : PayloadStatus)
      (fields : Array (String × TypedValue))
  | binOperator (operator : Miri.MIR.BinOp) (status : PayloadStatus)
  | unknownBinOperator (tag : String) (status : PayloadStatus)
  | unOperator (operator : Miri.MIR.UnOp) (status : PayloadStatus)
  | unknownUnOperator (tag : String) (status : PayloadStatus)
  | enumTag (category : TypedEnumTag) (tag : TaggedNode)
      (children : Array (String × TypedValue))
  | userTypeProjection (value : UserTypeProjection)
  | operand (variant : OperandVariant) (status : PayloadStatus)
      (fields : Array (String × TypedValue))
  | projection (variant : ProjectionVariant)
      (fields : Array (String × TypedValue))
  deriving BEq


structure DefinitionId where
  crateIndex : Nat
  index : Nat
  deriving Repr, DecidableEq

inductive VtableEntryKind where
  | dropInPlaceNull | dropInPlace | sizeBytes | alignBytes | vacant
  | method | supertraitVtablePointer | unknown (value : String)
  deriving Repr, DecidableEq

inductive VtablePredicateKind where
  | trait | autoTrait | projection | unknown (value : String)
  deriving Repr, DecidableEq

structure FunctionAllocation where
  instanceId : InstanceId
  definitionId : DefinitionId
  definitionPath : String
  genericArgs : TypedValue
  payload : Lean.Json
  deriving BEq

/-- Exact compiler GlobalAlloc::Static metadata queries, independent of
initializer evaluation and runtime allocation adjustment. -/
structure StaticGlobalInfo where
  status : PayloadStatus
  sizeBytes : Nat
  alignBytes : Nat
  mutability : MemoryMutability
  isStatic : Bool
  foreignItem : Bool
  threadLocal : Bool
  payload : Lean.Json
  deriving BEq

structure StaticAllocation where
  globalInfo : Option StaticGlobalInfo := none
  definitionId : DefinitionId
  definitionPath : String
  threadLocal : Bool
  initializer : Option AllocationMemory
  payload : Lean.Json
  deriving BEq

structure VtablePredicate where
  kind : VtablePredicateKind
  status : PayloadStatus
  definitionId : Option DefinitionId
  definitionPath : Option String
  genericArgs : Option TypedValue
  payload : Lean.Json
  deriving BEq

structure VtableEntry where
  kind : VtableEntryKind
  status : PayloadStatus
  instanceId : Option InstanceId
  definitionId : Option DefinitionId
  definitionPath : Option String
  allocationId : Option AllocationId
  traitDefinitionId : Option DefinitionId
  traitDefinitionPath : Option String
  genericArgs : Option TypedValue
  payload : Lean.Json
  deriving BEq

structure VtableAllocation where
  typeId : TypeId
  sizeBytes : Option Nat
  alignBytes : Option Nat
  layoutStatus : PayloadStatus
  predicates : Array VtablePredicate
  entries : Array VtableEntry
  payload : Lean.Json
  deriving BEq

inductive AllocationData where
  | memory (value : AllocationMemory)
  | function (value : FunctionAllocation)
  | static (value : StaticAllocation)
  | vtable (value : VtableAllocation)
  | typeId (value : TypeId)
  deriving BEq

structure AllocationNode where
  id : AllocationId
  /-- Exact rustc `AllocId.0.get()` witness supplied by the pinned exporter.
  This is absent in legacy exports and is never inferred from `id`. -/
  sourceAllocId : Option UInt64 := none
  status : PayloadStatus
  kind : AllocationKind
  memory : Option AllocationMemory
  data : Option AllocationData
  payload : Lean.Json
  deriving BEq

/-- The optional prepared post-export rustc allocator snapshot. Raw rustc IDs
remain separate from exporter graph IDs and from the runtime's dense IDs. -/
inductive SourceAllocIdKind where
  | dangling | memory | function | vtable | static | typeId
  deriving Repr, DecidableEq

inductive SourceAllocIdStatus where
  | dangling | serialized | opaque
  deriving Repr, DecidableEq

structure SourceAllocIdPoolRow where
  sourceAllocId : UInt64
  kind : SourceAllocIdKind
  status : SourceAllocIdStatus
  allocationId : Option AllocationId
  opaqueAllocationId : Option AllocationId := none
  memoryMutability : Option MemoryMutability := none
  memoryAlignBytes : Option Nat := none
  memoryAllBytesInitialized : Option Bool := none
  memoryHasProvenance : Option Bool := none
  byteImageHex : Option String := none
  deriving Repr, DecidableEq

inductive SourceAllocIdDedupKind where
  | function | vtable | static | typeId | memory | bytes
  deriving Repr, DecidableEq

inductive SourceAllocIdProbeOutcome where
  | preexistingHit | missReservedByProbe
  deriving Repr, DecidableEq

structure SourceAllocIdSaltResult where
  salt : Nat
  allocationId : AllocationId
  sourceAllocId : UInt64
  outcome : SourceAllocIdProbeOutcome
  deriving Repr, DecidableEq

structure SourceAllocIdDedupRow where
  keyKind : SourceAllocIdDedupKind
  keyAllocationId : AllocationId
  byteImageHex : Option String
  salts : Array SourceAllocIdSaltResult
  deriving Repr, DecidableEq

structure CompilerAllocIdWorld where
  lastReservedSourceAllocId : UInt64
  nextSourceAllocId : UInt64
  finalSentinelSourceAllocId : UInt64
  rawPool : Array SourceAllocIdPoolRow
  dedupCatalog : Array SourceAllocIdDedupRow
  completeKeyFamilies : Array SourceAllocIdDedupKind := #[]
  unsupportedKeyFamilies : Array SourceAllocIdDedupKind := #[]
  deriving Repr, DecidableEq

structure MirNode where
  value : TypedValue
  sourceInfo : SourceInfo

structure BasicBlock where
  id : BlockId
  statements : Array MirNode
  terminator : MirNode
  cleanup : Bool
  payload : Lean.Json

structure LocalDecl where
  id : LocalId
  typeId : TypeId
  sourceInfo : SourceInfo
  payload : Lean.Json

structure BodyCore where
  /-- Exact location of this body in the source document. Lowering checks this
  path against the retained raw document before using source-scoped metadata. -/
  sourcePath : String := ""
  defPath : String
  definitionId : Option DefinitionId
  phase : TypedValue
  injectionPhase : Option TypedValue
  argumentCount : Nat
  spreadArgument : Option LocalId
  locals : Array LocalDecl
  blocks : Array BasicBlock
  sourceScopes : Option (Array Lean.Json)
  payload : Lean.Json

structure PromotedBody where
  index : Nat
  status : PayloadStatus
  body : Option BodyCore
  payload : Lean.Json

structure Body extends BodyCore where
  promotedBodies : Array PromotedBody

structure InstanceNode where
  id : InstanceId
  status : PayloadStatus
  kind : InstanceKind
  defPath : Option String
  definitionId : Option DefinitionId
  bodyInstantiation : Option TaggedNode
  bodyTemplateIsPolymorphic : Option Bool
  instanceArgsAreMonomorphic : Option Bool
  body : Option Body
  promotedBodies : Array PromotedBody
  payload : Lean.Json

structure ScopeRoot where
  defPath : String
  definitionId : DefinitionId
  deriving Repr, DecidableEq

structure SelectedScope where
  kind : String
  statusText : String
  status : PayloadStatus
  semantics : String
  roots : Array ScopeRoot
  unresolvedObligations : Array String
  unresolvedEvidence : Array Obligation := #[]
  payload : Lean.Json

/-- Compiler-query target layout evidence, retained independently of a runtime
layout validator. Missing evidence is not inferred from the target triple. -/
structure TargetDataLayoutEvidence where
  status : PayloadStatus
  payload : Lean.Json

/-- Exact compiler existential-predicate identity, stable comparison rank and
late-bound-region-erasing normalization result under an explicit environment. -/
structure CompilerPredicateEvidence where
  id : Nat
  typingEnvironment : String
  stableKey : Nat
  autoTrait : Bool
  normalizationStatus : PayloadStatus
  normalizedId : Option Nat
  original : Lean.Json
  payload : Lean.Json


end Miri.Input
