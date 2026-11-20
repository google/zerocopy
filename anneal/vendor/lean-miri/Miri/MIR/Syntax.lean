import Miri.MIR.Operators

/-!
Pinned, typed mirror of the MIR syntax datatypes used by the interpreter.

This module contains data constructors only; it does not claim that Lean has
implemented their operational semantics.  In particular, decoder failures and
unsupported execution features belong in the Input layer as obligations, never
as an executable "other" constructor here.  Compiler-owned values (types,
definition identities, spans, regions and generic constants) use explicit IDs
or typed records; no JSON object or tag/string dispatch is part of this AST.
-/

namespace Miri.MIR

/-! Stable references for compiler graph nodes. These are compilation-local and
must be resolved against the corresponding typed metadata tables before
execution. -/

abbrev TyId := Nat
abbrev DefId := Nat
abbrev LocalId := Nat
abbrev BasicBlockId := Nat
abbrev AllocationId := Nat
abbrev TypeConstId := Nat
abbrev SpanId := Nat
abbrev FieldIndex := Nat
abbrev VariantIndex := Nat
abbrev UserTypeAnnotationIndex := Nat
abbrev HirOwnerId := Nat
abbrev HirLocalId := Nat

/-! Source MIR locations identify the start of a statement, or the terminator
when `statementIndex` equals that block's statement count. -/
structure Location where
  block : BasicBlockId
  statementIndex : Nat
  deriving Repr, DecidableEq

namespace Location

def start : Location := ⟨0, 0⟩

def successorWithinBlock (location : Location) : Location :=
  { location with statementIndex := location.statementIndex + 1 }

end Location

structure SpanRef where
  id : SpanId
  deriving Repr, DecidableEq

inductive Mutability where
  | Not
  | Mut
  deriving Repr, DecidableEq

inductive Safety where
  | Safe
  | Unsafe
  deriving Repr, DecidableEq

inductive Variance where
  | Covariant
  | Contravariant
  | Invariant
  | Bivariant
  deriving Repr, DecidableEq

inductive PointerCoercion where
  | ReifyFnPointer (safety : Safety)
  | UnsafeFnPointer
  | ClosureFnPointer (safety : Safety)
  | MutToConstPointer
  | ArrayToPointer
  | Unsize
  deriving Repr, DecidableEq

inductive CoercionSource where
  | AsCast
  | Implicit
  deriving Repr, DecidableEq

inductive CastKind where
  | PointerExposeProvenance
  | PointerWithExposedProvenance
  | PointerCoercion (coercion : PointerCoercion) (source : CoercionSource)
  | IntToInt
  | FloatToInt
  | FloatToFloat
  | IntToFloat
  | PtrToPtr
  | FnPtrToPtr
  | Transmute
  | BoxDerefTransmute
  | Subtype
  deriving Repr, DecidableEq

inductive FakeBorrowKind where
  | Shallow
  | Deep
  deriving Repr, DecidableEq

inductive MutBorrowKind where
  | Default
  | TwoPhaseBorrow
  | ClosureCapture
  deriving Repr, DecidableEq

inductive BorrowKind where
  | Shared
  | Fake (kind : FakeBorrowKind)
  | Mut (kind : MutBorrowKind)
  deriving Repr, DecidableEq

inductive RawPtrKind where
  | Mut
  | Const
  | FakeForPtrMetadata
  deriving Repr, DecidableEq

inductive WithRetag where
  | Yes
  | No
  deriving Repr, DecidableEq

inductive RuntimeChecks where
  | UbChecks
  | ContractChecks
  | OverflowChecks
  deriving Repr, DecidableEq

inductive LoopHintAttr where
  | Hint
  | Full
  | Never
  | Count (count : Nat)
  deriving Repr, DecidableEq

inductive FakeReadCause where
  | ForMatchGuard
  | ForMatchedPlace (closure : Option DefId)
  | ForGuardBinding
  | ForLet (closure : Option DefId)
  | ForIndex
  deriving Repr, DecidableEq

inductive CallSource where
  | OverloadedOperator
  | MatchCmp
  | Misc
  | Use
  | Normal
  deriving Repr, DecidableEq

inductive InlineAsmMacro where
  | Asm
  | NakedAsm
  deriving Repr, DecidableEq

inductive UnwindTerminateReason where
  | Abi
  | InCleanup
  deriving Repr, DecidableEq

inductive UnwindAction where
  | Continue
  | Unreachable
  | Terminate (reason : UnwindTerminateReason)
  | Cleanup (target : BasicBlockId)
  deriving Repr, DecidableEq

inductive CoroutineSource where
  | Block
  | Closure
  | Fn
  deriving Repr, DecidableEq

inductive CoroutineDesugaring where
  | Async
  | Gen
  | AsyncGen
  deriving Repr, DecidableEq

inductive Movability where
  | Static
  | Movable
  deriving Repr, DecidableEq

inductive CoroutineKind where
  | Desugared (kind : CoroutineDesugaring) (source : CoroutineSource)
  | Coroutine (movability : Movability)
  deriving Repr, DecidableEq

structure HirId where
  owner : HirOwnerId
  localId : HirLocalId
  deriving Repr, DecidableEq

inductive CoveragePointKind where
  | Expr
  | ImplicitElse
  | FunctionEnd
  deriving Repr, DecidableEq

inductive CoverageKind where
  | Point (pointKind : CoveragePointKind) (hirId : HirId)
  | BlockMarker (id : Nat)
  | VirtualCounter (basicCoverageBlock : Nat)
  deriving Repr, DecidableEq

inductive BackwardIncompatibleDropReason where
  | Edition2024
  deriving Repr, DecidableEq

inductive ProjectionKind where
  | Deref
  | Field (index : FieldIndex)
  | Index
  | ConstantIndex (offset minLength : Nat) (fromEnd : Bool)
  | Subslice (fromIndex toIndex : Nat) (fromEnd : Bool)
  | Downcast (name : Option String) (variant : VariantIndex)
  | OpaqueCast
  | UnwrapUnsafeBinder
  | PhantomDeref
  deriving Repr, DecidableEq

structure UserTypeProjection where
  base : UserTypeAnnotationIndex
  projections : Array ProjectionKind
  deriving Repr, DecidableEq

inductive AnalysisPhase where
  | Initial
  | PostCleanup
  deriving Repr, DecidableEq

inductive RuntimePhase where
  | Initial
  | PostCleanup
  | Optimized
  deriving Repr, DecidableEq

inductive MirPhase where
  | Built
  | Analysis (phase : AnalysisPhase)
  | Runtime (phase : RuntimePhase)
  deriving Repr, DecidableEq

/-! Constant values and type-system constants are explicit trees. `ScalarBits`
stores the exact low-bit encoding together with its byte width. Pointer scalar
provenance remains an allocation-graph identity and is not a runtime AllocId. -/

inductive ConstPointer where
  | Allocation (allocation : AllocationId) (offsetBytes : Nat) (immutable sharedRef : Bool)
  | Address (address widthBytes : Nat)
  deriving Repr, DecidableEq

inductive ScalarValue where
  | Int (bits : Nat) (sizeBytes : Nat)
  | Ptr (pointer : ConstPointer)
  deriving Repr, DecidableEq

inductive ConstValue where
  | Scalar (value : ScalarValue)
  | ZeroSized
  | Slice (allocation : AllocationId) (metadata : Nat)
  | Indirect (allocation : AllocationId) (offsetBytes : Nat)
  deriving Repr, DecidableEq

inductive ConstAliasKind where
  | Projection
  | InherentSelf
  | InherentImpl
  | Free
  | Anon
  deriving Repr, DecidableEq

inductive ConstExpressionCastKind where
  | As
  | Use
  deriving Repr, DecidableEq

inductive ConstExpressionKind where
  | Binop (operator : BinOp)
  | UnOp (operator : UnOp)
  | FunctionCall
  | Cast (kind : ConstExpressionCastKind)
  deriving Repr, DecidableEq

inductive BoundVarIndexKind where
  | Bound (debruijnIndex : Nat)
  | Canonical
  deriving Repr, DecidableEq

inductive BoundRegionKind where
  | Anon
  | NamedForPrinting (name : String)
  | Named (definition : DefId)
  | ClosureEnv
  deriving Repr, DecidableEq

inductive BoundTypeKind where
  | Anon
  | Param (definition : DefId)
  deriving Repr, DecidableEq

inductive BoundVariableKind where
  | Type (kind : BoundTypeKind)
  | Region (kind : BoundRegionKind)
  | Const
  deriving Repr, DecidableEq

inductive LateParamRegionKind where
  | Anon (index : Nat)
  | NamedAnon (index : Nat) (name : String)
  | Named (definition : DefId)
  | ClosureEnv
  deriving Repr, DecidableEq

inductive Region where
  | EarlyParameter (index : Nat) (name : String)
  | Bound (indexKind : BoundVarIndexKind) (variableIndex : Nat) (kind : BoundRegionKind)
  | LateParameter (scope : DefId) (kind : LateParamRegionKind)
  | Static
  | InferenceVariable (index : Nat)
  | Placeholder (universeIndex : Nat) (variableIndex : Nat) (kind : BoundRegionKind)
  | Erased
  | Error
  deriving Repr, DecidableEq

inductive GenericArg where
  | Type (ty : TyId)
  | Lifetime (region : Region)
  | Const (value : TypeConstId)
  deriving Repr, DecidableEq

inductive ValTreeNode where
  | Leaf (bits : Nat) (sizeBytes : Nat)
  | Branch (fields : Array TypeConstId)
  deriving Repr, DecidableEq

structure ValTree where
  nodes : Array ValTreeNode
  root : Nat
  deriving Repr, DecidableEq

inductive TypeConst where
  | Param (index : Nat) (name : String) (declaredType : Option TyId)
  | InferVar (id : Nat)
  | InferFresh (id : Nat)
  | Bound (indexKind : BoundVarIndexKind) (variableIndex : Nat)
  | Placeholder (universeIndex : Nat) (variableIndex : Nat)
  | Alias (rigid : Bool) (kind : ConstAliasKind) (definition : DefId)
      (arguments : Array GenericArg)
  | Value (ty : TyId) (tree : ValTree)
  | Error
  | Expr (kind : ConstExpressionKind) (arguments : Array GenericArg)
  deriving Repr, DecidableEq

structure UnevaluatedConst where
  definition : DefId
  arguments : Array GenericArg
  promoted : Option Nat
  deriving Repr, DecidableEq

inductive MirConst where
  | Ty (ty : TyId) (value : TypeConst)
  | Unevaluated (constant : UnevaluatedConst) (ty : TyId)
  | Val (value : ConstValue) (ty : TyId)
  deriving Repr, DecidableEq

structure ConstOperand where
  span : SpanRef
  userType : Option UserTypeAnnotationIndex
  value : MirConst
  deriving Repr, DecidableEq

inductive ProjectionElem where
  | Deref
  | Field (field : FieldIndex) (ty : TyId)
  | Index (localId : LocalId)
  | ConstantIndex (offset minLength : Nat) (fromEnd : Bool)
  | Subslice (fromIndex toIndex : Nat) (fromEnd : Bool)
  | Downcast (name : Option String) (variant : VariantIndex)
  | OpaqueCast (ty : TyId)
  | UnwrapUnsafeBinder (ty : TyId)
  | PhantomDeref
  deriving Repr, DecidableEq

structure Place where
  localId : LocalId
  projection : Array ProjectionElem
  deriving Repr, DecidableEq

inductive Operand where
  | Copy (place : Place)
  | Move (place : Place)
  | Constant (constant : ConstOperand)
  | RuntimeChecks (check : RuntimeChecks)
  deriving Repr, DecidableEq

structure CopyNonOverlapping where
  source : Operand
  destination : Operand
  count : Operand
  deriving Repr, DecidableEq

inductive NonDivergingIntrinsic where
  | Assume (condition : Operand)
  | CopyNonOverlapping (args : CopyNonOverlapping)
  deriving Repr, DecidableEq

inductive AggregateKind where
  | Array (elementType : TyId)
  | Tuple
  | Adt (definition : DefId) (variant : VariantIndex) (arguments : Array GenericArg)
      (userType : Option UserTypeAnnotationIndex) (activeField : Option FieldIndex)
  | Closure (definition : DefId) (arguments : Array GenericArg)
  | Coroutine (definition : DefId) (arguments : Array GenericArg)
  | CoroutineClosure (definition : DefId) (arguments : Array GenericArg)
  | RawPtr (pointeeType : TyId) (mutability : Mutability)
  deriving Repr, DecidableEq

inductive Rvalue where
  | Use (operand : Operand) (retag : WithRetag)
  | Repeat (operand : Operand) (count : TypeConst)
  | Ref (region : Region) (borrow : BorrowKind) (place : Place)
  | ThreadLocalRef (definition : DefId)
  | RawPtr (kind : RawPtrKind) (place : Place)
  | Cast (kind : CastKind) (operand : Operand) (targetType : TyId)
  | BinaryOp (operator : BinOp) (left right : Operand)
  | UnaryOp (operator : UnOp) (operand : Operand)
  | Discriminant (place : Place)
  | Aggregate (kind : AggregateKind) (operands : Array Operand)
  | CopyForDeref (place : Place)
  | WrapUnsafeBinder (operand : Operand) (targetType : TyId)
  | Reborrow (ty : TyId) (mutability : Mutability) (place : Place)
  deriving Repr, DecidableEq

inductive StatementKind where
  | Assign (destination : Place) (value : Rvalue)
  | FakeRead (cause : FakeReadCause) (place : Place)
  | SetDiscriminant (place : Place) (variant : VariantIndex)
  | StorageLive (localId : LocalId)
  | StorageDead (localId : LocalId)
  | PlaceMention (place : Place)
  | AscribeUserType (place : Place) (projection : UserTypeProjection) (variance : Variance)
  | Coverage (coverage : CoverageKind)
  | Intrinsic (intrinsic : NonDivergingIntrinsic)
  | ConstEvalCounter
  | Nop
  | BackwardIncompatibleDropHint (place : Place) (reason : BackwardIncompatibleDropReason)
  deriving Repr, DecidableEq

inductive SwitchTarget where
  | Case (value : Nat) (target : BasicBlockId)
  deriving Repr, DecidableEq

structure SwitchTargets where
  cases : Array SwitchTarget
  otherwise : BasicBlockId
  deriving Repr, DecidableEq

structure SpannedOperand where
  span : SpanRef
  operand : Operand
  deriving Repr, DecidableEq

structure InlineAsmOptions where
  pure : Bool
  nomem : Bool
  readonly : Bool
  preservesFlags : Bool
  noReturn : Bool
  noStack : Bool
  attSyntax : Bool
  raw : Bool
  mayUnwind : Bool
  deriving Repr, DecidableEq

inductive InlineAsmTemplatePiece where
  | String (text : String)
  | Placeholder (operandIndex : Nat) (modifier : Option Char) (span : SpanRef)
  deriving Repr, DecidableEq

/-! The pinned compiler resolves a register to a target-specific enum before
constructing MIR. We preserve both the target architecture and the resolved
register/class spelling. This is a typed serialization view, not an inline
assembly evaluator; the importer must block executable readiness until the
machine supports that target/register operation. -/
inductive InlineAsmArch where
  | X86 | X86_64 | Arm | Arm64EC | AArch64 | Amdgpu | RiscV32 | RiscV64
  | Nvptx64 | PowerPC | PowerPC64 | Hexagon | LoongArch32 | LoongArch64
  | Mips | Mips64 | Xtensa | S390x | Sparc | Sparc64 | SpirV | Wasm32
  | Wasm64 | Bpf | Avr | Msp430 | M68k | CSky
  deriving Repr, DecidableEq

inductive InlineAsmRegOrRegClass where
  | Reg (arch : InlineAsmArch) (resolvedRegister : String)
  | RegClass (arch : InlineAsmArch) (resolvedClass : String)
  deriving Repr, DecidableEq

inductive InlineAsmOperand where
  | In (register : InlineAsmRegOrRegClass) (value : Operand)
  | Out (register : InlineAsmRegOrRegClass) (late : Bool) (place : Option Place)
  | InOut (register : InlineAsmRegOrRegClass) (late : Bool) (input : Operand)
      (output : Option Place)
  | Const (value : ConstOperand)
  | SymFn (value : ConstOperand)
  | SymStatic (definition : DefId)
  | Label (targetIndex : Nat)
  deriving Repr, DecidableEq

structure InlineAsmTerminator where
  asmMacro : InlineAsmMacro
  template : Array InlineAsmTemplatePiece
  operands : Array InlineAsmOperand
  options : InlineAsmOptions
  lineSpans : Array SpanRef
  targets : Array BasicBlockId
  unwind : UnwindAction
  deriving Repr, DecidableEq

inductive AssertKind where
  | BoundsCheck (length index : Operand)
  | Overflow (operator : BinOp) (left right : Operand)
  | OverflowNeg (operand : Operand)
  | DivisionByZero (operand : Operand)
  | RemainderByZero (operand : Operand)
  | ResumedAfterReturn (coroutine : CoroutineKind)
  | ResumedAfterPanic (coroutine : CoroutineKind)
  | ResumedAfterDrop (coroutine : CoroutineKind)
  | MisalignedPointerDereference (required found : Operand)
  | NullPointerDereference
  | NullReferenceConstructed
  | InvalidEnumConstruction (operand : Operand)
  deriving Repr, DecidableEq

inductive TerminatorKind where
  | Goto (target : BasicBlockId) (loopHints : Array LoopHintAttr)
  | SwitchInt (discriminant : Operand) (targets : SwitchTargets)
  | UnwindResume
  | UnwindTerminate (reason : UnwindTerminateReason)
  | Return
  | Unreachable
  | Drop (place : Place) (target : BasicBlockId) (unwind : UnwindAction)
      (replace : Bool) (asyncDrop : Option BasicBlockId)
  | Call (function : Operand) (arguments : Array SpannedOperand) (destination : Place)
      (target : Option BasicBlockId) (unwind : UnwindAction) (source : CallSource)
      (functionSpan : SpanRef)
  | TailCall (function : Operand) (arguments : Array SpannedOperand) (functionSpan : SpanRef)
  | Assert (condition : Operand) (expected : Bool) (message : AssertKind)
      (target : BasicBlockId) (unwind : UnwindAction)
  | Yield (value : Operand) (resume : BasicBlockId) (resumeArgument : Place)
      (drop : Option BasicBlockId)
  | CoroutineDrop
  | FalseEdge (realTarget imaginaryTarget : BasicBlockId)
  | FalseUnwind (realTarget : BasicBlockId) (unwind : UnwindAction)
  | InlineAsm (asm : InlineAsmTerminator)
  deriving Repr, DecidableEq

structure SourceInfo where
  span : SpanRef
  scope : Nat
  deriving Repr, DecidableEq

structure Statement where
  sourceInfo : SourceInfo
  kind : StatementKind
  deriving Repr, DecidableEq

structure Terminator where
  sourceInfo : SourceInfo
  kind : TerminatorKind
  deriving Repr, DecidableEq

structure BasicBlock where
  statements : Array Statement
  terminator : Terminator
  cleanup : Bool
  deriving Repr, DecidableEq

structure Body where
  phase : MirPhase
  argumentCount : Nat
  spreadArgument : Option LocalId
  locals : Array TyId
  basicBlocks : Array BasicBlock
  deriving Repr, DecidableEq

end Miri.MIR
