import Miri.Memory.Allocation
import Miri.ABI.WrappingRange

/-!
The scalar and primitive validity core from pinned
`rustc_const_eval::interpret::validity`. It preserves the source distinction
between invalid integer bits, a possibly-null relative pointer, and a pointer
whose absolute address is unknown. Allocation reads and pointer/null checks
remain explicit inputs; aggregate and metadata validation return delegation
steps rather than being treated as successful values.
-/

namespace Miri.Memory

open Miri.ABI

structure ScalarValidityLayout where
  size : Size
  validRange : WrappingRange
  deriving DecidableEq, Repr

inductive ExpectedValue where
  | boolean
  | character
  | float
  | integer
  | functionPointer
  | rawPointer
  | reference
  | box
  | string
  deriving DecidableEq, Repr

inductive SafePointerKind where
  | reference (mutable : Bool)
  | box
  deriving DecidableEq, Repr

inductive PathElem where
  | field (name : String)
  | variant (name : String)
  | coroutineState (index : Nat)
  | capturedVar (name : String)
  | arrayElem (index : Nat)
  | tupleElem (index : Nat)
  | deref
  | enumTag
  | coroutineTag
  | dynDowncast (typeName : String)
  | vtable
  deriving DecidableEq, Repr

structure ValidationPath where
  originalType : String
  projections : Array PathElem := #[]
  deriving DecidableEq, Repr

def ValidationPath.push (path : ValidationPath) (projection : PathElem) : ValidationPath :=
  { path with projections := path.projections.push projection }

def ValidationPath.withElem {α : Type} (path : ValidationPath) (projection : PathElem)
    (visit : ValidationPath → α) : α :=
  visit (path.push projection)

def PathElem.render : PathElem → String
  | .field name => s!".{name}"
  | .variant name => s!".<enum-variant({name})>"
  | .coroutineState index => s!".<coroutine-state({index})>"
  | .capturedVar name => s!".<captured-var({name})>"
  | .arrayElem index => s!"[{index}]"
  | .tupleElem index => s!".{index}"
  | .deref => ".<deref>"
  | .enumTag => ".<enum-tag>"
  | .coroutineTag => ".<coroutine-tag>"
  | .dynDowncast typeName => s!".<dyn-downcast({typeName})>"
  | .vtable => ".<vtable>"

/-- Render projections with the same spelling and order as validity.rs's
`write_path`; `originalType` is kept separately, as in the source `Path`. -/
def ValidationPath.render (path : ValidationPath) : String :=
  String.join (path.projections.toList.map PathElem.render)

inductive RangeSetError where
  | memory (reason : MemoryError)
  | malformedRangeSet
  deriving DecidableEq, Repr

inductive PaddingPlanError where
  | memory (reason : MemoryError)
  | invalidDataRangeOrder (previousEnd nextStart : Size)
  | finalCoverageMismatch (expectedEnd actualEnd : Size)
  deriving DecidableEq, Repr

inductive AggregatePathError where
  | multipleTagOnNonVariantType (typeName : String)
  | emptyEnumField
  | multipleEnumFieldWithoutActiveVariant
  | missingFieldName (typeName : String) (field : Nat)
  | missingVariantName (typeName : String) (variant : Nat)
  | dynamicFieldIndex (field : Nat)
  | unexpectedVariantType (typeName : String)
  | unsupportedAggregate (typeName : String)
  deriving DecidableEq, Repr

inductive UnionDataRangeError where
  | invalidNodeIndex (index available : Nat)
  | recursiveLayout (node : Nat)
  | malformedFieldOffsets (children offsets : Nat)
  | memory (reason : MemoryError)
  | rangeSet (reason : RangeSetError)
  deriving DecidableEq, Repr

inductive ValidityFailure where
  | uninitialized (expected : ExpectedValue) (info : Option BadBytesAccess)
  | pointerAsInt (expected : ExpectedValue) (info : Option BadBytesAccess)
  | partialPointer (offset : Size)
  | invalidBool (value : UInt8)
  | invalidChar (value : UInt32)
  | invalidScalarBits (bits : U128) (layout : ScalarValidityLayout)
  | maybeNullPointer
  | unknownAbsoluteAddress (layout : ScalarValidityLayout)
  | nullSafePointer (kind : SafePointerKind) (maybe : Bool)
  | uninhabitedPointee (kind : SafePointerKind)
  | addressTooClose (kind : SafePointerKind) (size : Size)
  | readOnlyPointer (kind : SafePointerKind)
  | unsafeCellInReadOnlyMemory
  | nullFunctionPointer (maybe : Bool)
  | danglingSafePointer (kind : SafePointerKind)
  | mutablePointerToReadOnly (kind : SafePointerKind)
  | neverValue
  deriving DecidableEq, Repr

inductive ValidityError (MachineError : Type) where
  | failure (reason : ValidityFailure)
  | pathFailure (path : ValidationPath) (reason : ValidityFailure)
  | scalar (reason : ScalarError)
  | range (reason : WrappingRangeError)
  | rangeSet (reason : RangeSetError)
  | padding (reason : PaddingPlanError)
  | pathInvariant (reason : AggregatePathError)
  | unionRange (reason : UnionDataRangeError)
  | walkInvariant (reason : String)
  | rangeInvariant (reason : String)
  | machine (reason : MachineError)
  deriving DecidableEq, Repr

inductive PrimitiveKind where
  | boolean
  | character
  | scalar
  | never
  | foreign
  | functionDefinition
  | rawPointer (pointeeSized : Bool)
  | safeReference
  | box
  | functionPointer
  | aggregate
  deriving DecidableEq, Repr

/-- Non-scalar work is returned to the caller as a required validation step.
The caller must supply the matching recursive, metadata, or pointer hooks. -/
inductive PrimitiveStep where
  | valid
  | recurse
  | rawPointerMetadata
  | safePointer
  | boxPointer
  | functionPointer
  deriving DecidableEq, Repr

namespace Validity

/-- Sorted, disjoint, non-adjacent set of data-byte ranges used by the source
visitor's padding reset. Its constructor is private so malformed interval
arrays cannot enter the visitor through this API. -/
structure DataRangeSet where
  private mk ::
  private ranges : Array AllocRange
  deriving DecidableEq, Repr

namespace DataRangeSet

def empty : DataRangeSet := ⟨#[]⟩

def toArray (ranges : DataRangeSet) : Array AllocRange := ranges.ranges

private def endOf (range : AllocRange) : Except RangeSetError Size :=
  range.endExclusive |>.mapError RangeSetError.memory

private def splitBefore (offset : Size) : List AllocRange →
    Except RangeSetError (List AllocRange × List AllocRange)
  | [] => .ok ([], [])
  | range :: rest => do
    let finish ← endOf range
    if finish.bytes < offset.bytes then
      let (before, after) ← splitBefore offset rest
      return (range :: before, after)
    return ([], range :: rest)

private def absorbAdjacent (finish : Size) : List AllocRange →
    Except RangeSetError (Size × List AllocRange)
  | [] => .ok (finish, [])
  | range :: rest => do
    if range.start.bytes > finish.bytes then return (finish, range :: rest)
    let rangeFinish ← endOf range
    absorbAdjacent (if rangeFinish.bytes > finish.bytes then rangeFinish else finish) rest

/-- Source `RangeSet::add_range`: zero-sized ranges are ignored; overlapping
and adjacent ranges coalesce, preserving sorted disjoint storage. -/
def addRange (ranges : DataRangeSet) (offset size : Size) :
    Except RangeSetError DataRangeSet := do
  if size == Size.ZERO then return ranges
  let finish ← (allocRange offset size).endExclusive |>.mapError RangeSetError.memory
  let (before, after) ← splitBefore offset ranges.ranges.toList
  match after with
  | [] => return ⟨(before ++ [allocRange offset size]).toArray⟩
  | first :: rest =>
    if finish.bytes < first.start.bytes then
      return ⟨(before ++ allocRange offset size :: after).toArray⟩
    let firstFinish ← endOf first
    let mergedStart := if first.start.bytes < offset.bytes then first.start else offset
    let mergedFinish := if firstFinish.bytes > finish.bytes then firstFinish else finish
    let (mergedFinish, remaining) ← absorbAdjacent mergedFinish rest
    let mergedSize ← (Size.sub mergedFinish mergedStart).mapError
      (RangeSetError.memory ∘ MemoryError.sizeError)
    return ⟨(before ++ allocRange mergedStart mergedSize :: remaining).toArray⟩

def containsRange (ranges : DataRangeSet) (range : AllocRange) : Bool :=
  ranges.ranges.any (· == range)

end DataRangeSet

inductive UnionFieldsShape where
  | primitive
  | unionFields (children : Array Nat)
  | array (element : Nat) (stride : Size) (count : UInt64) (elementIsScalar : Bool)
  | arbitrary (children : Array Nat) (offsets : Array Size)
  deriving DecidableEq, Repr

inductive UnionVariantsShape where
  | single
  | empty
  | multiple (variants : Array Nat)
  deriving DecidableEq, Repr

/-- A finite, indexed description of one `TyAndLayout` node for the pure
`union_data_range_uncached` traversal. Child indices deliberately remain
checked at runtime: malformed synthetic layouts cannot be mistaken for an
empty union. `elementIsScalar` is the upstream backend-representation
fast-path fact for array elements. -/
structure UnionLayoutNode where
  size : Size
  fields : UnionFieldsShape
  variants : UnionVariantsShape
  deriving DecidableEq, Repr

structure UnionLayoutGraph where
  root : Nat
  nodes : Array UnionLayoutNode
  deriving DecidableEq, Repr

private inductive UnionRangeTask where
  | enter (node : Nat) (base : Size)
  | leave (node : Nat)
  | arrayElement (element : Nat) (stride : Size) (count next : UInt64) (base : Size)

private def checkedOffset (base offset : Size) : Except UnionDataRangeError Size :=
  (Size.add base offset).mapError (UnionDataRangeError.memory ∘ MemoryError.sizeError)

private def checkedScaledOffset (stride : Size) (index : UInt64) :
    Except UnionDataRangeError Size :=
  (Size.mul stride index).mapError (UnionDataRangeError.memory ∘ MemoryError.sizeError)

/-- Exact recursive layout walk from `ValidityVisitor::union_data_range`.
The work stack implements its depth-first recursion while detecting malformed
cycles and checking each source `Size` operation. -/
def unionDataRange (graph : UnionLayoutGraph) :
    Except UnionDataRangeError DataRangeSet := Id.run do
  let mut output := DataRangeSet.empty
  let mut work : Array UnionRangeTask := #[.enter graph.root Size.ZERO]
  let mut active : Array Nat := #[]
  while let some task := work.back? do
    work := work.pop
    match task with
    | .leave node =>
      if active.back? != some node then
        return .error (.recursiveLayout node)
      active := active.pop
    | .arrayElement element stride count next base =>
      if next < count then
        let scaled ← match checkedScaledOffset stride next with
          | .ok value => pure value
          | .error reason => return .error reason
        let offset ← match checkedOffset base scaled with
          | .ok value => pure value
          | .error reason => return .error reason
        if next + 1 < count then
          work := work.push (.arrayElement element stride count (next + 1) base)
        work := work.push (.enter element offset)
    | .enter nodeId base =>
      if active.contains nodeId then return .error (.recursiveLayout nodeId)
      let some node := graph.nodes[nodeId]? | return .error (.invalidNodeIndex nodeId graph.nodes.size)
      if node.size == Size.ZERO then continue
      active := active.push nodeId
      work := work.push (.leave nodeId)
      let mut children : Array UnionRangeTask := #[]
      match node.fields with
      | .primitive =>
        match output.addRange base node.size with
        | .ok updated => output := updated
        | .error reason => return .error (.rangeSet reason)
      | .unionFields fields =>
        for child in fields do
          children := children.push (.enter child base)
      | .array element stride count elementIsScalar =>
        if elementIsScalar then
          let some elementNode := graph.nodes[element]?
            | return .error (.invalidNodeIndex element graph.nodes.size)
          let arraySize ← match Size.mul elementNode.size count with
            | .ok value => pure value
            | .error reason => return .error (.memory (.sizeError reason))
          match output.addRange base arraySize with
          | .ok updated => output := updated
          | .error reason => return .error (.rangeSet reason)
        else if count != 0 then
          children := children.push (.arrayElement element stride count 0 base)
      | .arbitrary fields offsets =>
        if fields.size != offsets.size then
          return .error (.malformedFieldOffsets fields.size offsets.size)
        for index in [:fields.size] do
          let some child := fields[index]? | return .error (.malformedFieldOffsets fields.size offsets.size)
          let some relative := offsets[index]? | return .error (.malformedFieldOffsets fields.size offsets.size)
          let childBase ← match checkedOffset base relative with
            | .ok value => pure value
            | .error reason => return .error reason
          children := children.push (.enter child childBase)
      match node.variants with
      | .single | .empty => pure ()
      | .multiple variants =>
        for variant in variants do
          children := children.push (.enter variant base)
      for child in children.reverse do
        work := work.push child
  return .ok output

inductive CtfeMode where
  | static (mutable : Bool)
  | promoted
  | constant (allowImmutableUnsafeCell : Bool)
  deriving DecidableEq, Repr

def allowsImmutableUnsafeCell : CtfeMode → Bool
  | .constant allow => allow
  | .static _ | .promoted => false

/-- Source `visit_value`'s `UnsafeCell` check for the current ADT node. The
memory mutability query is required only after CTFE policy, dynamic ZST, and
the type predicate establish that it matters. -/
def checkUnsafeCell {MachineError HookState : Type}
    (mode : Option CtfeMode) (isZeroSized isUnsafeCell : Bool)
    (path : ValidationPath)
    (isMutableMemory : HookState → EStateM.Result (ValidityError MachineError)
      HookState Bool) :
    EStateM (ValidityError MachineError) HookState Unit := fun state => Id.run do
  if let some mode := mode then
    if !allowsImmutableUnsafeCell mode && !isZeroSized && isUnsafeCell then
      match isMutableMemory state with
      | .ok true next => return .ok () next
      | .ok false next => return .error (.pathFailure path .unsafeCellInReadOnlyMemory) next
      | .error reason next => return .error reason next
  return .ok () state

structure UnionVisitHooks (MachineError HookState : Type) where
  dynamicSize : HookState → EStateM.Result (ValidityError MachineError)
    HookState (Option Size)
  isFreeze : HookState → EStateM.Result (ValidityError MachineError) HookState Bool
  isMutableMemory : HookState → EStateM.Result (ValidityError MachineError) HookState Bool
  dataRangeOffset : HookState → EStateM.Result (ValidityError MachineError) HookState Size

/-- Source `ValueVisitor::visit_union`: CTFE checks `!Freeze` before data
range collection, and only tracked typed copies query the containing offset.
Union layout/range failures remain distinct from validation UB and machine
lookup failures. -/
def visitUnion {MachineError HookState : Type}
    (hooks : UnionVisitHooks MachineError HookState)
    (mode : Option CtfeMode) (path : ValidationPath)
    (resetProvenanceAndPadding : Bool) (dataBytes : Option DataRangeSet)
    (layout : UnionLayoutGraph) :
    EStateM (ValidityError MachineError) HookState (Option DataRangeSet) :=
  fun initialState => Id.run do
    let mut state := initialState
    if let some mode := mode then
      if !allowsImmutableUnsafeCell mode then
        let (dynamicSize, nextState) ← match hooks.dynamicSize state with
          | .ok value next => pure (value, next)
          | .error reason next => return .error reason next
        state := nextState
        if dynamicSize != some Size.ZERO then
          let (isFreeze, nextState) ← match hooks.isFreeze state with
            | .ok value next => pure (value, next)
            | .error reason next => return .error reason next
          state := nextState
          if !isFreeze then
            match hooks.isMutableMemory state with
            | .ok true next => state := next
            | .ok false next =>
              return .error (.pathFailure path .unsafeCellInReadOnlyMemory) next
            | .error reason next => return .error reason next
    if !resetProvenanceAndPadding then return .ok dataBytes state
    let some dataBytes := dataBytes | return .ok none state
    let (base, nextState) ← match hooks.dataRangeOffset state with
      | .ok value next => pure (value, next)
      | .error reason next => return .error reason next
    state := nextState
    let relativeRanges ← match unionDataRange layout with
      | .ok value => pure value
      | .error reason => return .error (.unionRange reason) state
    let mut updated := dataBytes
    for range in relativeRanges.ranges do
      let absoluteStart ← match checkedOffset base range.start with
        | .ok value => pure value
        | .error reason => return .error (.unionRange reason) state
      let nextUpdated ← match updated.addRange absoluteStart range.size with
        | .ok value => pure value
        | .error reason => return .error (.rangeSet reason) state
      updated := nextUpdated
    return .ok (some updated) state

inductive AggregateTypeKind where
  | closure
  | coroutine
  | coroutineClosure
  | tuple
  | enum
  | struct
  | array
  | slice
  | dynamic
  | other (typeName : String)
  deriving DecidableEq, Repr

inductive VariantLayoutKind where
  | multiple (tagField : Nat)
  | single
  | empty
  deriving DecidableEq, Repr

structure AggregatePathInfo where
  typeName : String
  kind : AggregateTypeKind
  variants : VariantLayoutKind
  field : Nat
  fieldName : Option String := none
  capturedVariableName : Option String := none
  fieldTypeName : String := "?"
  deriving DecidableEq, Repr

/-- Port of `aggregate_field_path_elem`. Layout and HIR lookup facts are
explicit inputs; closure captures fall back to the source's numeric symbol. -/
def aggregateFieldPathElem (info : AggregatePathInfo) :
    Except AggregatePathError PathElem := do
  match info.variants with
  | .multiple tagField =>
    if info.field == tagField then
      match info.kind with
      | .enum => return .enumTag
      | .coroutine => return .coroutineTag
      | _ => throw (.multipleTagOnNonVariantType info.typeName)
  | .single | .empty => pure ()
  match info.kind with
  | .closure | .coroutine | .coroutineClosure =>
    return .capturedVar (info.capturedVariableName.getD (toString info.field))
  | .tuple => return .tupleElem info.field
  | .enum =>
    match info.variants with
    | .single =>
      match info.fieldName with
      | some name => return .field name
      | none => throw (.missingFieldName info.typeName info.field)
    | .empty => throw .emptyEnumField
    | .multiple _ => throw .multipleEnumFieldWithoutActiveVariant
  | .struct =>
    match info.fieldName with
    | some name => return .field name
    | none => throw (.missingFieldName info.typeName info.field)
  | .array | .slice => return .arrayElem info.field
  | .dynamic =>
    if info.field != 0 then throw (.dynamicFieldIndex info.field)
    return .dynDowncast info.fieldTypeName
  | .other name => throw (.unsupportedAggregate name)

/-- Source `visit_field` path scoping. The projection lookup is evaluated
before the child visitor, and only that child sees the extended path. -/
def visitAggregateField {MachineError HookState α : Type}
    (path : ValidationPath) (info : AggregatePathInfo)
    (visit : ValidationPath → EStateM (ValidityError MachineError) HookState α) :
    EStateM (ValidityError MachineError) HookState α := fun state =>
  match aggregateFieldPathElem info with
  | .error reason => .error (.pathInvariant reason) state
  | .ok projection => visit (path.push projection) state

/-- Source `visit_variant` path selection for ADTs and coroutines. -/
def variantPathElem (typeName : String) (kind : AggregateTypeKind)
    (variant : Nat) (name : Option String) : Except AggregatePathError PathElem := do
  match kind with
  | .enum =>
    match name with
    | some name => return .variant name
    | none => throw (.missingVariantName typeName variant)
  | .coroutine => return .coroutineState variant
  | _ => throw (.unexpectedVariantType typeName)

def visitAggregateVariant {MachineError HookState α : Type}
    (path : ValidationPath) (typeName : String) (kind : AggregateTypeKind)
    (variant : Nat) (name : Option String)
    (visit : ValidationPath → EStateM (ValidityError MachineError) HookState α) :
    EStateM (ValidityError MachineError) HookState α := fun state =>
  match variantPathElem typeName kind variant name with
  | .error reason => .error (.pathInvariant reason) state
  | .ok projection => visit (path.push projection) state

private def paddingPlanLoop (start cursor : Size) :
    List AllocRange → Array AllocRange → Except PaddingPlanError (Size × Array AllocRange)
  | [], writes => .ok (cursor, writes)
  | range :: rest, writes => do
    if range.start.bytes < cursor.bytes then
      throw (.invalidDataRangeOrder cursor range.start)
    let writes ← if range.start.bytes > cursor.bytes then do
      let relativeStart ← (Size.sub cursor start).mapError
        (PaddingPlanError.memory ∘ MemoryError.sizeError)
      let paddingSize ← (Size.sub range.start cursor).mapError
        (PaddingPlanError.memory ∘ MemoryError.sizeError)
      pure (writes.push (allocRange relativeStart paddingSize))
    else pure writes
    let nextCursor ← range.endExclusive |>.mapError PaddingPlanError.memory
    paddingPlanLoop start nextCursor rest writes

/-- Compute source `reset_padding` writes. The final zero-length sentinel
closes the last gap; malformed/out-of-object ranges return explicit
invariant failures instead of relying on rustc assertions or Size panics. -/
def paddingWrites (data : DataRangeSet) (start size : Size) :
    Except PaddingPlanError (Array AllocRange) := do
  if data.ranges == #[allocRange start size] then return #[]
  if size == Size.ZERO then return #[]
  let finalEnd ← (Size.add start size).mapError
    (PaddingPlanError.memory ∘ MemoryError.sizeError)
  let withFinalizer := data.ranges.push (allocRange finalEnd Size.ZERO)
  let (cursor, writes) ← paddingPlanLoop start start withFinalizer.toList #[]
  if cursor != finalEnd then throw (.finalCoverageMismatch finalEnd cursor)
  return writes

/-- Execute the planned padding writes in source order. The allocation lookup
and byte-mask mutations stay on explicit machine callbacks; a failed write
retains all earlier callback state. `none` data tracking and ZST places are
source no-ops. -/
def resetPadding {MachineError HookState : Type}
    (data : Option DataRangeSet)
    (allocationRange : HookState → EStateM.Result (ValidityError MachineError)
      HookState (Option (Size × Size)))
    (writeUninit : AllocRange → HookState →
      EStateM.Result (ValidityError MachineError) HookState Unit) :
    EStateM (ValidityError MachineError) HookState Unit := fun initialState => Id.run do
  let some data := data | return .ok () initialState
  let (placeRange, state) ← match allocationRange initialState with
    | .ok placeRange state => pure (placeRange, state)
    | .error reason state => return .error reason state
  let some (start, size) := placeRange | return .ok () state
  let writes ← match paddingWrites data start size with
    | .ok writes => pure writes
    | .error reason => return .error (.padding reason) state
  let mut state := state
  for range in writes do
    match writeUninit range state with
    | .ok () next => state := next
    | .error reason next => return .error reason next
  return .ok () state

inductive MetadataKind where
  | sized
  | dynamic
  | slice
  | string
  | foreign
  | unexpected (description : String)
  deriving DecidableEq, Repr

inductive GlobalAllocationKind where
  | static (nested foreignItem : Bool)
  | other
  deriving DecidableEq, Repr

/-- Machine lookup facts needed by the source CTFE recursion policy. The
allocation identity/global query itself belongs to the interpreter callback;
the policy decisions are performed here. -/
inductive PointerAllocLookup where
  | noAllocationId
  | missingGlobal (stillInMemory : Bool)
  | global (size : Size) (mutability : Mutability) (kind : GlobalAllocationKind)
  deriving DecidableEq, Repr

/-- Source CTFE-only allocation and mutability checks performed before adding
a safe pointer to the recursive worklist. The `true` result means skip the
descent (including the source's delayed-bug/missing-interning early return). -/
def ctfeRecursionDecision (mode : CtfeMode) (kind : SafePointerKind)
    (lookup : PointerAllocLookup) : Except ValidityFailure Bool := do
  match lookup with
  | .noAllocationId => return false
  | .missingGlobal true => return true
  | .missingGlobal false => throw (.danglingSafePointer kind)
  | .global size mutability allocationKind =>
    let mut skipRecursiveCheck := false
    match allocationKind with
    | .static nested foreignItem =>
      match mode with
      | .static _ | .promoted => skipRecursiveCheck := !nested
      | .constant _ =>
        skipRecursiveCheck := mutability == .Mut || foreignItem
    | .other => pure ()
    let expectsMutable := match kind with
      | .box => true
      | .reference mutable => mutable
    if size != Size.ZERO && expectsMutable && mutability == .Not then
      throw (.mutablePointerToReadOnly kind)
    return skipRecursiveCheck

/-- Persistent visitor flags. `withMaybeDangling` scopes the source's
`may_dangle |= is_like_maybe_dangling()` update and restores the old value on
successful return. Errors unwind the visitor just as the source macro does. -/
structure VisitorFlags where
  resetProvenanceAndPadding : Bool := false
  mayDangle : Bool := false
  deriving DecidableEq, Repr

def withMaybeDangling {Error HookState α : Type} (flags : VisitorFlags)
    (isLikeMaybeDangling : Bool)
    (visit : VisitorFlags → EStateM Error HookState α) :
    EStateM Error HookState (α × VisitorFlags) := fun state =>
  match visit { flags with mayDangle := flags.mayDangle || isLikeMaybeDangling } state with
  | .ok value next => .ok (value, flags) next
  | .error reason next => .error reason next

/-- Mutation and machine-resolution boundary used by
`ValidityVisitor::try_visit_primitive`. -/
structure PrimitiveHooks (Prov : Type) (MachineError HookState : Type) where
  clearProvenance : HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  resetPointerProvenance : Scalar Prov → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  addDataRange : HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  checkRawPointerMetadata : Scalar Prov → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  checkFunctionPointer : Scalar Prov → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit

/-- Facts returned by the machine's `imm_ptr_to_mplace` boundary. Dynamic
size/alignment and pointer access remain separate callbacks so their ordering
matches the pinned visitor. -/
structure SafePointerTarget (Prov Key : Type) where
  original : Scalar Prov
  pointer : Scalar Prov
  metadataKind : MetadataKind
  layoutSize : Size
  layoutAlign : Align
  absoluteAddress : Option UInt64
  key : Key

/-- A small, explicit recursive-reference worklist matching rustc's
`RefTracking`: `seen` persists after an item is popped, and `todo` is LIFO. -/
structure RefTracking (Key Path : Type) where
  seen : Array Key := #[]
  todo : Array (Key × Path) := #[]
  deriving Repr

namespace RefTracking

def empty : RefTracking Key Path := {}

def start (key : Key) (path : Path) : RefTracking Key Path :=
  ⟨#[key], #[(key, path)]⟩

def next (tracking : RefTracking Key Path) :
    Option ((Key × Path) × RefTracking Key Path) := do
  let item ← tracking.todo.back?
  return (item, { tracking with todo := tracking.todo.pop })

/-- Duplicate references are ignored; `makePath` is only evaluated on the
first visit, matching the source's lazy path construction. -/
def track (tracking : RefTracking Key Path) (key : Key)
    (makePath : Unit → Path) [DecidableEq Key] : RefTracking Key Path :=
  if tracking.seen.any (fun item => decide (item = key)) then tracking
  else { seen := tracking.seen.push key,
         todo := tracking.todo.push (key, makePath ()) }

end RefTracking

inductive ValueWalkFields where
  | primitive
  | union (fieldCount : Nat)
  | arbitrary (inMemoryOrder : Array Nat) (fields : Array Nat)
  | array (elements : Array Nat)
  deriving DecidableEq, Repr

inductive ValueWalkVariants where
  | single
  | empty
  | multiple (variants : Array Nat)
  deriving DecidableEq, Repr

inductive ValueWalkSpecial where
  | none
  | dynamic (inner : Nat)
  | box (pointer allocator : Nat)
  deriving DecidableEq, Repr

/-- Resolved projection facts for the generic `ValueVisitor::walk_value`
engine. The machine/layout adapter supplies child handles in source projection
order; each index and field/variant lookup is validated before traversal. -/
structure ValueWalkNode where
  typeName : String
  pathInfo : AggregatePathInfo
  fields : ValueWalkFields
  variants : ValueWalkVariants
  special : ValueWalkSpecial := .none
  fieldNames : Array (Option String) := #[]
  capturedNames : Array (Option String) := #[]
  variantNames : Array (Option String) := #[]
  isLikeMaybeDangling : Bool := false
  deriving DecidableEq, Repr

structure ValueWalkGraph where
  root : Nat
  nodes : Array ValueWalkNode
  deriving DecidableEq, Repr

structure ValueWalkHooks (MachineError HookState : Type) where
  tryVisitPrimitive : Nat → ValidationPath → VisitorFlags → HookState →
    EStateM.Result (ValidityError MachineError) HookState Bool
  checkUnsafeCell : Nat → ValidationPath → VisitorFlags → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  tryVisitSpecialCase : Nat → ValidationPath → VisitorFlags → HookState →
    EStateM.Result (ValidityError MachineError) HookState Bool
  visitUnion : Nat → Nat → ValidationPath → VisitorFlags → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  visitBox : Nat → Nat → ValidationPath → VisitorFlags → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  readDiscriminant : Nat → HookState →
    EStateM.Result (ValidityError MachineError) HookState Nat
  visitVariantless : Nat → ValidationPath → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit

private inductive ValueWalkTask where
  | visit (node : Nat) (path : ValidationPath) (flags : VisitorFlags)
  | variants (node : Nat) (path : ValidationPath) (flags : VisitorFlags)
  | leave (node : Nat)

private def valueWalkNode (graph : ValueWalkGraph) (index : Nat) :
    Except String ValueWalkNode :=
  match graph.nodes[index]? with
  | some node => .ok node
  | none => .error s!"value walk node {index} is outside {graph.nodes.size} nodes"

private def valueWalkFieldPath (graph : ValueWalkGraph) (parent : ValueWalkNode)
    (field child : Nat) : Except String PathElem := do
  let childNode ← valueWalkNode graph child
  let fieldName := parent.fieldNames[field]?.join
  let capturedName := parent.capturedNames[field]?.join
  let info := { parent.pathInfo with
    field := field
    fieldName := fieldName
    capturedVariableName := capturedName
    fieldTypeName := childNode.typeName }
  (aggregateFieldPathElem info).mapError reprStr

/-- Source `ValueVisitor::walk_value` traversal order, composed with the
validity-specific primitive, UnsafeCell, optimized-case, union, and Box hooks.
The finite graph contains layout projections supplied by the interpreter;
missing projection or machine operations remain explicit failures. -/
def walkValue {MachineError HookState : Type}
    (hooks : ValueWalkHooks MachineError HookState)
    (graph : ValueWalkGraph) (rootPath : ValidationPath) (flags : VisitorFlags) :
    EStateM (ValidityError MachineError) HookState Unit :=
  fun initialState => Id.run do
    let mut work : Array ValueWalkTask := #[.visit graph.root rootPath flags]
    let mut active : Array Nat := #[]
    let mut state := initialState
    while let some task := work.back? do
      work := work.pop
      match task with
      | .leave node =>
        if active.back? != some node then
          return .error (.walkInvariant s!"unbalanced value walk for node {node}") state
        active := active.pop
      | .variants nodeId path currentFlags =>
        let node ← match valueWalkNode graph nodeId with
          | .ok node => pure node
          | .error reason => return .error (.walkInvariant reason) state
        match node.variants with
        | .single => pure ()
        | .empty =>
          match hooks.visitVariantless nodeId path state with
          | .ok () next => state := next
          | .error reason next => return .error reason next
        | .multiple variants =>
          let (variant, nextState) ← match hooks.readDiscriminant nodeId state with
            | .ok variant next => pure (variant, next)
            | .error reason next => return .error reason next
          state := nextState
          let some child := variants[variant]?
            | return .error (.walkInvariant
              s!"variant {variant} is outside {variants.size} variants for {node.typeName}") state
          let name := node.variantNames[variant]?.join
          let projection ← match variantPathElem node.typeName node.pathInfo.kind variant name with
            | .ok projection => pure projection
            | .error reason => return .error (.pathInvariant reason) state
          work := work.push (.visit child (path.push projection) currentFlags)
      | .visit nodeId path currentFlags =>
        if active.contains nodeId then
          return .error (.walkInvariant s!"recursive by-value layout at node {nodeId}") state
        let node ← match valueWalkNode graph nodeId with
          | .ok node => pure node
          | .error reason => return .error (.walkInvariant reason) state
        let (primitive, nextState) ← match hooks.tryVisitPrimitive nodeId path currentFlags state with
          | .ok value next => pure (value, next)
          | .error reason next => return .error reason next
        state := nextState
        if primitive then continue
        match hooks.checkUnsafeCell nodeId path currentFlags state with
        | .ok () next => state := next
        | .error reason next => return .error reason next
        let (specialHandled, nextState) ← match
            hooks.tryVisitSpecialCase nodeId path currentFlags state with
          | .ok value next => pure (value, next)
          | .error reason next => return .error reason next
        state := nextState
        if specialHandled then continue
        let walkFlags := { currentFlags with
          mayDangle := currentFlags.mayDangle || node.isLikeMaybeDangling }
        active := active.push nodeId
        work := work.push (.leave nodeId)
        match node.special with
        | .dynamic inner =>
          let projection ← match valueWalkFieldPath graph node 0 inner with
            | .ok projection => pure projection
            | .error reason => return .error (.walkInvariant reason) state
          work := work.push (.visit inner (path.push projection) walkFlags)
        | .box pointer allocator =>
          match hooks.visitBox nodeId pointer path walkFlags state with
          | .ok () next => state := next
          | .error reason next => return .error reason next
          let projection ← match valueWalkFieldPath graph node 1 allocator with
            | .ok projection => pure projection
            | .error reason => return .error (.walkInvariant reason) state
          work := work.push (.visit allocator (path.push projection) walkFlags)
        | .none =>
          let mut children : Array ValueWalkTask := #[]
          match node.fields with
          | .primitive => pure ()
          | .union fieldCount =>
            if fieldCount == 0 then
              return .error (.walkInvariant s!"zero-field union for {node.typeName}") state
            match hooks.visitUnion nodeId fieldCount path walkFlags state with
            | .ok () next => state := next
            | .error reason next => return .error reason next
          | .array elements =>
            for index in [:elements.size] do
              let some child := elements[index]?
                | return .error (.walkInvariant s!"missing array element {index}") state
              children := children.push (.visit child (path.push (.arrayElem index)) walkFlags)
          | .arbitrary order fields =>
            for field in order do
              let some child := fields[field]?
                | return .error (.walkInvariant
                  s!"field {field} is outside {fields.size} fields for {node.typeName}") state
              let projection ← match valueWalkFieldPath graph node field child with
                | .ok projection => pure projection
                | .error reason => return .error (.walkInvariant reason) state
              children := children.push (.visit child (path.push projection) walkFlags)
          if node.variants != .single then
            work := work.push (.variants nodeId path walkFlags)
          for child in children.reverse do
            work := work.push child
    return .ok () state

/-- Per-invocation state passed through the source `visit_value` traversal.
The path is a value so child scopes can push a projection and restore it on
return; data tracking and recursive-reference discovery are returned by the
visitor rather than hidden in a default-success operation. -/
structure ValidationSession (Key : Type) where
  path : ValidationPath
  flags : VisitorFlags
  ctfeMode : Option CtfeMode
  refTracking : Option (RefTracking Key ValidationPath)
  dataBytes : Option DataRangeSet

structure ValidatePlaceHooks (Place Key MachineError HookState : Type) where
  isStoredInMemory : Place → HookState →
    EStateM.Result (ValidityError MachineError) HookState Bool
  visitValue : Place → ValidationSession Key → HookState →
    EStateM.Result (ValidityError MachineError) HookState (ValidationSession Key)
  allocationRange : Place → HookState →
    EStateM.Result (ValidityError MachineError) HookState (Option (Size × Size))
  writeUninit : Place → AllocRange → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  trackedPlace : Key → HookState →
    EStateM.Result (ValidityError MachineError) HookState Place

/-- The pinned `validate_place_internal` orchestration. The actual MIR place
projection and recursive type walk are an explicit callback because they
depend on rustc's `PlaceTy`/layout engine; this driver preserves the source
setup, mutation order, padding finalizer, and recursive `RefTracking` drain.
Each tracked pointee is visited without provenance reset, with no further
tracking, and under `may_dangle`, as in `validate_place`. -/
def validatePlace {Place Key MachineError HookState : Type}
    [DecidableEq Key]
    (hooks : ValidatePlaceHooks Place Key MachineError HookState)
    (root : Place) (originalType : String)
    (resetProvenanceAndPadding : Bool) (ctfeMode : Option CtfeMode)
    (initialTracking : Option (RefTracking Key ValidationPath))
    (drainTracking : Bool) :
    EStateM (ValidityError MachineError) HookState Unit := fun initialHookState => Id.run do
  let mut state := initialHookState
  let mut session : ValidationSession Key := {
    path := ⟨originalType, #[]⟩
    flags := ⟨resetProvenanceAndPadding, false⟩
    ctfeMode := ctfeMode
    refTracking := initialTracking
    dataBytes := none
  }
  if resetProvenanceAndPadding then
    let (stored, nextState) ← match hooks.isStoredInMemory root state with
      | .ok stored next => pure (stored, next)
      | .error reason next => return .error reason next
    state := nextState
    if stored then session := { session with dataBytes := some DataRangeSet.empty }

  let validateOne : Place → ValidationSession Key → HookState →
      EStateM.Result (ValidityError MachineError) HookState (ValidationSession Key) :=
    fun place current hookState => Id.run do
    let (visited, nextState) ← match hooks.visitValue place current hookState with
      | .ok visited next => pure (visited, next)
      | .error reason next => return .error reason next
    let nextStateForReset := nextState
    let normalized := { visited with
      path := current.path
      flags := current.flags
      ctfeMode := current.ctfeMode }
    match resetPadding normalized.dataBytes
        (hooks.allocationRange place) (hooks.writeUninit place) nextStateForReset with
    | .ok () finalState => return .ok normalized finalState
    | .error reason finalState => return .error reason finalState

  let (rootSession, nextState) ← match validateOne root session state with
    | .ok value next => pure (value, next)
    | .error reason next => return .error reason next
  session := rootSession
  state := nextState

  if drainTracking then
    let mut keepGoing := true
    while keepGoing do
      match session.refTracking with
      | none => keepGoing := false
      | some tracker =>
        match tracker.next with
        | none => keepGoing := false
        | some ((key, path), remaining) =>
          session := { session with refTracking := some remaining }
          let (place, nextState) ← match hooks.trackedPlace key state with
            | .ok place next => pure (place, next)
            | .error reason next => return .error reason next
          state := nextState
          let trackedSession : ValidationSession Key := {
            path := path
            flags := ⟨false, true⟩
            ctfeMode := none
            refTracking := none
            dataBytes := none
          }
          let (ignored, nextState) ← match validateOne place trackedSession state with
            | .ok value next => pure (value, next)
            | .error reason next => return .error reason next
          let _ := ignored
          state := nextState
  return .ok () state

/-- Required operations for the source `check_safe_pointer` path. Each
callback stands at a real machine/layout boundary; absent semantics cannot be
silently interpreted as success. Callbacks return a `ValidityError` when the
source maps an underlying UB category to a validation failure. -/
structure SafePointerHooks (Prov Key : Type) (MachineError HookState : Type) where
  readImmediate : HookState → EStateM.Result (ValidityError MachineError)
    HookState (Scalar Prov)
  resolvePlace : Scalar Prov → HookState →
    EStateM.Result (ValidityError MachineError) HookState
      (SafePointerTarget Prov Key)
  checkWideMetadata : SafePointerTarget Prov Key → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  sizeAndAlign : SafePointerTarget Prov Key → HookState →
    EStateM.Result (ValidityError MachineError) HookState (Option (Size × Align))
  checkAccess : Scalar Prov → Size → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  retagPointer : Scalar Prov → SafePointerKind → HookState →
    EStateM.Result (ValidityError MachineError) HookState (Option (Scalar Prov))
  writeAdjustedPointer : Scalar Prov → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  resetPointerProvenance : Scalar Prov → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  markPointerData : HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  scalarMayBeNull : Scalar Prov → HookState →
    EStateM.Result (ValidityError MachineError) HookState Bool
  checkInhabited : SafePointerTarget Prov Key → HookState →
    EStateM.Result (ValidityError MachineError) HookState Bool
  checkAlignment : Scalar Prov → Align → HookState →
    EStateM.Result (ValidityError MachineError) HookState Unit
  ctfePointerAllocLookup : SafePointerTarget Prov Key → CtfeMode → HookState →
    EStateM.Result (ValidityError MachineError) HookState PointerAllocLookup

/-- Run source-ordered safe-reference/Box validation. The optional tracker,
CTFE policy, and reset/may-dangle flags are explicit visitor state. A source
machine error or validation failure preserves callback state at the exact
failing step. `targetUsizeMax` is the machine target's maximum address. -/
def checkSafePointer {Prov MachineError HookState Key Path : Type}
    [PointerProvenance Prov] [DecidableEq Key]
    (hooks : SafePointerHooks Prov Key MachineError HookState)
    (kind : SafePointerKind) (resetProvenanceAndPadding mayDangle : Bool)
    (ctfeMode : Option CtfeMode) (targetUsizeMax : UInt64)
    (tracking : Option (RefTracking Key Path × Path))
    (makeDerefPath : Path → Path)
    (invalidMetadataTail : String → ValidityError MachineError) :
    EStateM (ValidityError MachineError) HookState (Option (RefTracking Key Path)) :=
  fun initialState => Id.run do
    let original ← match hooks.readImmediate initialState with
      | .ok value state => pure (value, state)
      | .error reason state => return .error reason state
    let (original, state0) := original
    let mut state := state0
    if resetProvenanceAndPadding then
      match hooks.markPointerData state with
      | .ok () next => state := next
      | .error reason next => return .error reason next
    let (target, nextState) ← match hooks.resolvePlace original state with
      | .ok target next => pure (target, next)
      | .error reason next => return .error reason next
    state := nextState
    if target.metadataKind != .sized then
      match target.metadataKind with
      | .unexpected description => return .error (invalidMetadataTail description) state
      | _ =>
        match hooks.checkWideMetadata target state with
        | .ok () next => state := next
        | .error reason next => return .error reason next
    let (dynamicLayout, nextState) ← match hooks.sizeAndAlign target state with
      | .ok value next => pure (value, next)
      | .error reason next => return .error reason next
    state := nextState
    let (size, align) := dynamicLayout.getD (target.layoutSize, target.layoutAlign)
    if !mayDangle then
      match hooks.checkAccess target.pointer size state with
      | .ok () next => state := next
      | .error reason next => return .error reason next
      if resetProvenanceAndPadding then
        let adjusted ← match hooks.retagPointer original kind state with
          | .ok value next => pure (value, next)
          | .error reason next => return .error reason next
        let (adjusted, nextState) := adjusted
        state := nextState
        match adjusted with
        | some pointer =>
          match hooks.writeAdjustedPointer pointer state with
          | .ok () next => state := next
          | .error reason next => return .error reason next
        | none =>
          match hooks.resetPointerProvenance original state with
          | .ok () next => state := next
          | .error reason next => return .error reason next
    else
      match target.absoluteAddress with
      | none => pure () -- Relative CTFE pointers have no absolute address to check.
      | some address =>
        let endNat := address.toNat + size.bytes.toNat
        if endNat > 18446744073709551615 then
          return .error (.failure (.addressTooClose kind size)) state
        if endNat >= targetUsizeMax.toNat then
          return .error (.failure (.addressTooClose kind size)) state
      if resetProvenanceAndPadding then
        match hooks.resetPointerProvenance original state with
        | .ok () next => state := next
        | .error reason next => return .error reason next
    let (nullable, nextState) ← match hooks.scalarMayBeNull target.pointer state with
      | .ok nullable next => pure (nullable, next)
      | .error reason next => return .error reason next
    state := nextState
    if nullable then
      return .error (.failure (.nullSafePointer kind
        (!PointerProvenance.offsetIsAddr (Prov := Prov) && target.pointer.isPointer))) state
    let (inhabited, nextState) ← match hooks.checkInhabited target state with
      | .ok inhabited next => pure (inhabited, next)
      | .error reason next => return .error reason next
    state := nextState
    if !inhabited then return .error (.failure (.uninhabitedPointee kind)) state
    match hooks.checkAlignment target.pointer align state with
    | .ok () next => state := next
    | .error reason next => return .error reason next
    match tracking with
    | none => return .ok none state
    | some (tracker, path) =>
      if mayDangle then return .ok (some tracker) state
      if let some mode := ctfeMode then
        let (lookup, nextState) ← match hooks.ctfePointerAllocLookup target mode state with
          | .ok lookup next => pure (lookup, next)
          | .error reason next => return .error reason next
        state := nextState
        match ctfeRecursionDecision mode kind lookup with
        | .error failure => return .error (.failure failure) state
        | .ok true => return .ok (some tracker) state
        | .ok false => pure ()
      let tracker := tracker.track target.key (fun _ => makeDerefPath path)
      return .ok (some tracker) state

private def maxValue (layout : ScalarValidityLayout) :
    Except WrappingRangeError U128 :=
  (Size.unsignedIntMax layout.size).mapError .sizeFailure

/-- Port of `validity.rs::fmt_range`, retaining its invariant failures as
explicit errors instead of Lean/Rust panics. -/
def formatRange (range : WrappingRange) (maxHi : U128) :
    Except String String := do
  let lo := range.start.toNat
  let hi := range.end.toNat
  let maximum := maxHi.toNat
  if hi > maximum then throw "fmt_range end exceeds scalar width"
  if lo > hi then
    return s!"less or equal to {hi}, or greater or equal to {lo}"
  if lo == hi then return s!"equal to {lo}"
  if lo == 0 then
    if hi >= maximum then throw "fmt_range was called for a full range"
    return s!"less or equal to {hi}"
  if hi == maximum then
    if lo == 0 then throw "fmt_range full-range lower-bound assertion failed"
    return s!"greater or equal to {lo}"
  return s!"in the range {lo}..={hi}"

def formatFailure (failure : ValidityFailure) : Except String String := do
  match failure with
  | .uninitialized expected _ =>
      return s!"encountered uninitialized memory, but {reprStr expected}"
  | .pointerAsInt expected _ =>
      return s!"encountered a pointer, but {reprStr expected}"
  | .partialPointer _ => return "encountered a partial pointer or a mix of pointers"
  | .invalidBool value => return s!"invalid boolean byte {value.toNat}"
  | .invalidChar value =>
      return s!"encountered {value.toNat}, but expected a valid Unicode scalar value"
  | .invalidScalarBits bits layout => do
      let maximum ← (maxValue layout).mapError fun error => reprStr error
      let expected ← formatRange layout.validRange maximum
      return s!"encountered {bits.toNat}, but expected something {expected}"
  | .maybeNullPointer =>
      return "encountered a maybe-null pointer, but expected something that is definitely non-zero"
  | .unknownAbsoluteAddress layout => do
      let maximum ← (maxValue layout).mapError fun error => reprStr error
      let expected ← formatRange layout.validRange maximum
      return s!"encountered a pointer with unknown absolute address, but expected something that is definitely {expected}"
  | .nullSafePointer kind maybe =>
      let name := match kind with
        | .reference false => "reference"
        | .reference true => "mutable reference"
        | .box => "box"
      return s!"encountered a {if maybe then "maybe-" else ""}null {name}"
  | .uninhabitedPointee kind =>
      let name := match kind with
        | .reference false => "reference"
        | .reference true => "mutable reference"
        | .box => "box"
      return s!"encountered a {name} pointing to an uninhabited type"
  | .addressTooClose kind size =>
      let name := match kind with
        | .reference false => "reference"
        | .reference true => "mutable reference"
        | .box => "box"
      return s!"encountered a {name} that is too close to the end of the address space for a pointee of {size.bytes} bytes"
  | .readOnlyPointer kind =>
      let name := match kind with
        | .reference false => "mutable reference"
        | .reference true => "mutable reference"
        | .box => "box"
      return s!"encountered {name} pointing to read-only memory"
  | .unsafeCellInReadOnlyMemory =>
      return "encountered `UnsafeCell` in read-only memory"
  | .nullFunctionPointer maybe =>
      return s!"encountered a {if maybe then "maybe-" else ""}null function pointer"
  | .danglingSafePointer kind =>
      let name := match kind with
        | .reference false => "reference"
        | .reference true => "mutable reference"
        | .box => "box"
      return s!"encountered a dangling {name} (use-after-free)"
  | .mutablePointerToReadOnly kind =>
      let name := match kind with
        | .reference _ => "mutable reference"
        | .box => "box"
      return s!"encountered {name} pointing to read-only memory"
  | .neverValue => return "encountered a value of the never type `!`"

def classifyReadError (expected : ExpectedValue) (error : AllocError) :
    Option ValidityFailure :=
  match error with
  | .invalidUninitBytes info => some (.uninitialized expected info)
  | .readPointerAsInt info => some (.pointerAsInt expected info)
  | .readPartialPointer offset => some (.partialPointer offset)
  | _ => none

private def checkedLayout (layout : ScalarValidityLayout) :
    Except (ValidityError MachineError) (U128 × Bool) := do
  let maximum ← maxValue layout |>.mapError ValidityError.range
  if layout.validRange.end.toNat > maximum.toNat then
    throw (.rangeInvariant "visit_scalar asserted that the valid-range end fits the scalar width")
  let alwaysValid ← WrappingRange.isFullFor layout.validRange layout.size
    |>.mapError ValidityError.range
  return (maximum, alwaysValid)

/-- Source `ValidityVisitor::visit_scalar`, with `scalar_may_be_null` as a
required machine callback. Callback errors pass through unchanged, while the
result state is retained on callback failure. -/
def checkScalar [PointerProvenance Prov] {MachineError HookState : Type}
    (layout : ScalarValidityLayout) (scalar : Scalar Prov)
    (scalarMayBeNull : Scalar Prov → HookState →
      EStateM.Result MachineError HookState Bool) :
    EStateM (ValidityError MachineError) HookState Unit := fun state => Id.run do
  let (_, alwaysValid) ← match checkedLayout layout with
    | .ok checked => pure checked
    | .error reason => return .error reason state
  match scalar.tryToScalarInt with
  | .ok (.integer integer) =>
    let bits ← match integer.toBits layout.size with
      | .ok bits => pure bits
      | .error reason => return .error (.scalar (.scalarInt reason)) state
    if layout.validRange.contains bits then
      return .ok () state
    return .error (.failure (.invalidScalarBits bits layout)) state
  | .ok (.erasedPointer _ _) =>
    let max ← match maxValue layout with
      | .ok max => pure max
      | .error reason => return .error (.range reason) state
    if layout.validRange.start.toNat == 1 && layout.validRange.end == max then
      match scalarMayBeNull scalar state with
      | .ok mayBeNull nextState =>
        if mayBeNull then return .error (.failure .maybeNullPointer) nextState
        return .ok () nextState
      | .error reason nextState => return .error (.machine reason) nextState
    if alwaysValid then return .ok () state
    return .error (.failure (.unknownAbsoluteAddress layout)) state
  | .error reason => return .error (.scalar reason) state

/-- Source primitive classification after the memory read. The integer/float
case only requires initialized scalar bytes here; valid-range checking is the
separate `visitScalar` operation used by the higher-level visitor when needed.
Pointer-specific operations remain explicit delegation steps. -/
def checkPrimitive [PointerProvenance Prov] {MachineError HookState : Type}
    (kind : PrimitiveKind) (_layout : ScalarValidityLayout) (scalar : Scalar Prov)
    (_scalarMayBeNull : Scalar Prov → HookState →
      EStateM.Result MachineError HookState Bool) :
    EStateM (ValidityError MachineError) HookState PrimitiveStep := fun state => Id.run do
  match kind with
  | .boolean =>
    match scalar.toBool with
    | .ok _ => return .ok .valid state
    | .error (.scalarInt (.invalidBool value)) =>
      return .error (.failure (.invalidBool value)) state
    | .error .readPointerAsInt =>
      return .error (.failure (.pointerAsInt .boolean none)) state
    | .error reason => return .error (.scalar reason) state
  | .character =>
    match scalar.toChar with
    | .ok _ => return .ok .valid state
    | .error (.scalarInt (.invalidChar value)) =>
      return .error (.failure (.invalidChar value)) state
    | .error .readPointerAsInt =>
      return .error (.failure (.pointerAsInt .character none)) state
    | .error reason => return .error (.scalar reason) state
  | .scalar => return .ok .valid state
  | .never => return .error (.failure .neverValue) state
  | .foreign | .functionDefinition => return .ok .valid state
  | .rawPointer true => return .ok .valid state
  | .rawPointer false => return .ok .rawPointerMetadata state
  | .safeReference => return .ok .safePointer state
  | .box => return .ok .boxPointer state
  | .functionPointer => return .ok .functionPointer state
  | .aggregate => return .ok .recurse state

/-- Execute the stateful portion of `try_visit_primitive`. The caller has
already read the scalar/immediate at the expected type. This preserves the
source order for pointer reset, data-byte tracking, wide-pointer metadata, and
function-pointer validation. Safe references and Box delegate to
`checkSafePointer` through distinct explicit steps. -/
def visitPrimitive [PointerProvenance Prov] {MachineError HookState : Type}
    (hooks : PrimitiveHooks Prov MachineError HookState)
    (kind : PrimitiveKind) (layout : ScalarValidityLayout) (scalar : Scalar Prov)
    (resetProvenanceAndPadding recursiveTracking : Bool)
    (scalarMayBeNull : Scalar Prov → HookState →
      EStateM.Result MachineError HookState Bool) :
    EStateM (ValidityError MachineError) HookState PrimitiveStep := fun initialState => Id.run do
  match kind with
  | .rawPointer pointeeSized =>
    let mut state := initialState
    if resetProvenanceAndPadding then
      match hooks.resetPointerProvenance scalar state with
      | .ok () next => state := next
      | .error reason next => return .error reason next
      match hooks.addDataRange state with
      | .ok () next => state := next
      | .error reason next => return .error reason next
    if !pointeeSized then
      match hooks.checkRawPointerMetadata scalar state with
      | .ok () next => return .ok .valid next
      | .error reason next => return .error reason next
    return .ok .valid state
  | .functionPointer =>
    if recursiveTracking then
      match hooks.checkFunctionPointer scalar initialState with
      | .error reason next => return .error reason next
      | .ok () next =>
        let mut state := next
        if resetProvenanceAndPadding then
          if !scalar.isPointer then
            match hooks.clearProvenance state with
            | .ok () updated => state := updated
            | .error reason updated => return .error reason updated
          match hooks.addDataRange state with
          | .ok () updated => state := updated
          | .error reason updated => return .error reason updated
        return .ok .valid state
    else
      match scalarMayBeNull scalar initialState with
      | .error reason next => return .error (.machine reason) next
      | .ok nullable next =>
        if nullable then
          return .error (.failure (.nullFunctionPointer
            (!PointerProvenance.offsetIsAddr (Prov := Prov) && scalar.isPointer))) next
        let mut state := next
        if resetProvenanceAndPadding then
          if !scalar.isPointer then
            match hooks.clearProvenance state with
            | .ok () updated => state := updated
            | .error reason updated => return .error reason updated
          match hooks.addDataRange state with
          | .ok () updated => state := updated
          | .error reason updated => return .error reason updated
        return .ok .valid state
  | _ =>
    match checkPrimitive kind layout scalar scalarMayBeNull initialState with
    | .error reason next => return .error reason next
    | .ok step next =>
      let mut state := next
      match kind with
      | .boolean | .character | .scalar =>
        if resetProvenanceAndPadding then
          match hooks.clearProvenance state with
          | .ok () updated => state := updated
          | .error reason updated => return .error reason updated
          match hooks.addDataRange state with
          | .ok () updated => state := updated
          | .error reason updated => return .error reason updated
      | _ => pure ()
      return .ok step state

/-- The standard one-byte nonzero niche excludes the null representation. -/
theorem zero_is_outside_byte_nonzero_niche :
    WrappingRange.contains ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 255⟩ 0 = false := by
  decide

/-- Any one-byte value from 1 through 255 satisfies the nonzero niche. -/
theorem byte_nonzero_niche_accepts (value : UInt8) (h : value.toNat != 0) :
    WrappingRange.contains ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 255⟩
      (BitVec.ofNat 128 value.toNat) = true := by
  have hwidth := UInt8.toNat_lt value
  have h128 : value.toNat < 2 ^ 128 := by omega
  have hbits : (BitVec.ofNat 128 value.toNat).toNat = value.toNat := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h128
  simp [WrappingRange.contains, hbits]
  simp at h
  omega

end Validity

end Miri.Memory
