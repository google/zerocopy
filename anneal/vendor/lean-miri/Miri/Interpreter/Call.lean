import Miri.ABI.FnAbi
import Miri.Interpreter.OperandPath
import Miri.Interpreter.ControlFlow
import Miri.Interpreter.Rvalue
import Miri.Interpreter.LocalAccess

/-! Connected call pipeline from pinned `interpret/call.rs` and `step.rs`.
Compiler queries, ABI compatibility, and machine leaves are mandatory effects.
-/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.MIR
open Miri.TreeBorrows.RetagPolicy

inductive FnArg (P : Type) where
  | Copy (op : OpTy P)
  | InPlace (place : MPlaceTy P) (snapshot : Option (OpTy P) := none)
  deriving Repr
namespace FnArg

def layout : FnArg P → LocalLayout
  | .Copy op => op.layout
  | .InPlace place _ => place.layout

def copyFnArg : FnArg P → OpTy P
  | .Copy op => op
  | .InPlace place none => ⟨.indirect place.mplace, place.layout⟩
  | .InPlace _ (some snap) => snap
end FnArg

inductive FnVal (Other : Type) where
  | Instance (fnInstance : CallInstance)
  | Other (value : Other)
  deriving Repr

/-- Function-kind query after signature normalization, before callee resolution. -/
inductive CallFunctionKind where
  | FnPtr
  | FnDef (definition : DefId) (args : Array GenericArg)
  | invalid
  deriving Repr

structure CallRequest (P Other Extern FnABI : Type) where
  callee : FnVal Other
  callerAbi : Extern
  callerFnAbi : Option FnABI
  args : Array (FnArg P)
  withCallerLocation : Bool
  destination : RuntimeStackPlace P
  target : Option BasicBlockId
  unwind : UnwindAction
  tempAllocs : Array (Pointer (Option P)) := #[]

structure EvaluatedCall (P Other Extern FnABI : Type) where
  callee : FnVal Other
  args : Array (FnArg P)
  callerAbi : Extern
  fnAbi : Option FnABI
  withCallerLocation : Bool
  tempAllocs : Array (Pointer (Option P)) := #[]

abbrev CallM (S A : Type) := EStateM StepError S A

/-- `FnABI`, `ArgABI`, `Extern` preserve complete compiler ABI records supplied
by the caller. No reduced pass-mode or calling-convention enum is invented.
`checkArgumentCompat` implements source layout_compat AND its eq_abi assertion.
All memory operations must invoke the canonical memory/provenance hooks. -/
structure CallHooks (P S C E Other Extern FnABI ArgABI : Type) where
  debugAssertions : Bool
  getFrame : CallM S (Frame P LocalLayout E)
  setFrame : Frame P LocalLayout E → CallM S Unit
  frameIndex : CallM S Nat
  evalOperand : C → MIR.Operand → CallM S (OpTy P)
  evalOperandAt : C → OperandPath → MIR.Operand → CallM S (OpTy P) := fun c _ => evalOperand c
  evalPlace : C → MIR.Place → Bool → CallM S (RuntimeStackPlace P)
  placeToOp : C → RuntimeStackPlace P → CallM S (OpTy P)
  forceAllocation : C → RuntimeStackPlace P → CallM S (MPlaceTy P)
  functionSignature : C → LocalLayout → CallM S (Nat × Extern)
  functionKind : TyId → CallM S CallFunctionKind
  readPointer : C → OpTy P → CallM S (Pointer (Option P))
  getPtrFn : C → Pointer (Option P) → CallM S (FnVal Other)
  resolve : C → DefId → Array GenericArg → CallM S CallInstance
  fnAbiOfFnPtr : C → LocalLayout → Array TyId → CallM S FnABI
  fnAbiOfInstance : C → CallInstance → Array TyId → CallM S FnABI
  requiresCallerLocation : CallInstance → CallM S Bool
  callerLocation : CallM S SpanRef
  abiCanUnwind : FnABI → Bool
  abiVariadic : FnABI → Bool
  abiFixedCount : FnABI → Nat
  abiArgs : FnABI → Array ArgABI
  abiReturn : FnABI → ArgABI
  sameConvention : FnABI → FnABI → Bool
  isRustCall : Extern → Bool
  rustAbi : Extern
  argLayout : ArgABI → LocalLayout
  argIsIgnore : ArgABI → Bool
  isOneZst : LocalLayout → Bool
  checkArgumentCompat : C → ArgABI → ArgABI → CallM S Bool
  checkTargetFeatures : C → CallInstance → CallM S Unit
  tupleFields : TyId → CallM S (Array TyId)
  projectFnArg : C → FnArg P → Nat → CallM S (FnArg P)
  localLayout : C → LocalId → CallM S LocalLayout
  localSpan : Body → LocalId → CallM S SpanRef
  storageLiveDyn : C → LocalId → MemPlaceMeta P → CallM S Unit
  copyAllowTransmute : C → OpTy P → RuntimeStackPlace P → CallM S Unit
  protectArgument : C → MPlaceTy P → CallM S Unit
  withRetagMode : {A : Type} → C → RetagMode → CallM S A → CallM S A
  nonCapturingClosure : C → CallInstance → FnABI → CallM S Bool
  allocateStack : C → LocalLayout → CallM S (MPlaceTy P)
  copyToMemory : C → OpTy P → MPlaceTy P → CallM S Unit
  vaListPtr : C → Array (MPlaceTy P) → CallM S (Pointer (Option P))
  writeZeroBytes : C → Pointer (Option P) → Size → CallM S Unit
  vaListKeyField : C → MPlaceTy P → CallM S (MPlaceTy P)
  writePointerToMemory : C → Pointer (Option P) → MPlaceTy P → CallM S Unit
  pushRaw : C → CallInstance → LoadedBody → RuntimeStackPlace P → ReturnContinuation → CallM S Unit
  pushDone : C → CallM S Unit
  popRaw : C → CallM S (Frame P LocalLayout E)
  cleanup : C → Bool → Frame P LocalLayout E → CallM S ReturnAction
  afterFrameInit : C → CallM S Unit
  callExtra : C → Other → FnABI → Array (FnArg P) → RuntimeStackPlace P →
    Option BasicBlockId → UnwindAction → CallM S Unit
  /-- Check intrinsic metadata; fallback must be Item and not must_be_overridden. -/
  callIntrinsic : C → CallInstance → Array (OpTy P) → RuntimeStackPlace P →
    Option BasicBlockId → UnwindAction → CallM S (Option CallInstance)
  callLlvmIntrinsic : C → CallInstance → Array (OpTy P) → RuntimeStackPlace P →
    Option BasicBlockId → CallM S Unit
  findMirOrEvalFn : C → CallInstance → FnABI → Array (FnArg P) → RuntimeStackPlace P →
    Option BasicBlockId → UnwindAction → CallM S (Option (LoadedBody × CallInstance))
  /-- Unwrap DispatchFromDyn newtypes, read pointer without dereferencing, validate
  dyn tail/vtable, select Method, cross-check fnInstance, thin receiver and ABI type.
  Kept required until vtable compiler queries and typed pointer construction port. -/
  resolveVirtual : C → CallInstance → DefId → Nat → FnABI → Array (FnArg P) →
    CallM S (CallInstance × FnABI × Array (FnArg P))
  isDynamic : TyId → CallM S Bool
  unpackDynForDrop : C → MPlaceTy P → CallM S (MPlaceTy P)
  resolveDropGlue : C → TyId → CallM S CallInstance
  mplaceToMutRef : C → MPlaceTy P → CallM S (OpTy P)
  fakeUnitReturn : C → CallM S (RuntimeStackPlace P)
  deinitMovedPlace : Bool := false
  deinitInPlaceArgument : C → MPlaceTy P → CallM S Unit := fun _ _ => pure ()
  markInPlaceMovedUninit : C → MPlaceTy P → CallM S Unit := fun _ _ => pure ()
  restoreInPlaceMovedBytes : C → OpTy P → MPlaceTy P → CallM S Unit := fun _ _ _ => pure ()
  copyRawMPlace : C → MPlaceTy P → MPlaceTy P → CallM S Unit := fun _ _ _ => pure ()
  isForeignItem : CallInstance → CallM S Bool := fun _ => pure false
  deallocateStack : C → Pointer (Option P) → CallM S Unit := fun _ _ => pure ()

namespace Call
variable {P S C E Other Extern FnABI ArgABI : Type}
local notation "Hooks" => CallHooks P S C E Other Extern FnABI ArgABI
local notation "M" => CallM S

private def require (condition : Bool) (message : String) : M Unit :=
  unless condition do throw (.invalidProgram message)

private def at? (values : Array A) (index : Nat) (message : String) : CallM S A :=
  match values[index]? with
  | none => throw (.invalidProgram message)
  | some value => pure value

private def setSpan (h : Hooks) (span : SpanRef) : M Unit := do
  let frame ← h.getFrame
  h.setFrame { frame with location := .unwinding span }

def deallocateTempArgs (h : Hooks) (choice : C)
    (tempAllocs : Array (Pointer (Option P))) : M Unit := do
  for ptr in tempAllocs do
    h.deallocateStack choice ptr

private def cleanupTempArgsOnError (h : Hooks) (choice : C)
    (tempAllocs : Array (Pointer (Option P))) (action : M A) : M A := fun s =>
  match action s with
  | .ok val s' => .ok val s'
  | .error err s' =>
    match deallocateTempArgs h choice tempAllocs s' with
    | .ok () s'' => .error err s''
    | .error _ s'' => .error err s''

def deinitInPlaceArg (h : Hooks) (choice : C) (place : MPlaceTy P)
    (snap? : Option (OpTy P)) : M Unit := do
  if let some snap := snap? then
    h.restoreInPlaceMovedBytes choice snap place
  h.deinitInPlaceArgument choice place

def snapshotInPlaceArg (h : Hooks) (choice : C)
    (place : MPlaceTy P) : M (FnArg P) := do
  if !h.deinitMovedPlace then
    return .InPlace place none
  if !place.layout.layout.isSized then
    throw (.unsupported "unsized in-place move argument deinitialization unsupported")
  let tmpPlace ← h.allocateStack choice place.layout
  cleanupTempArgsOnError h choice #[tmpPlace.mplace.ptr] do
    h.copyRawMPlace choice place tmpPlace
    h.markInPlaceMovedUninit choice place
  return .InPlace place (some ⟨.indirect tmpPlace.mplace, tmpPlace.layout⟩)

def moveDefinitelyDisjoint (args : Array SpannedOperand) (dest : Place) : Bool := Id.run do
  let mut seen : Array LocalId := #[]
  let mut places : Array Place := #[]
  for arg in args do
    if let .Move place := arg.operand then places := places.push place
  places := places.push dest
  for place in places do
    if place.projection[0]? == some .Deref || seen.contains place.localId then return false
    seen := seen.push place.localId
  return true

def evalFnCallArgumentAt (h : Hooks) (choice : C) (operand : MIR.Operand)
    (disjoint : Bool) (path : OperandPath) : M (FnArg P) := do
  match operand with
  | .Copy _ | .Constant _ | .RuntimeChecks _ => return .Copy (← h.evalOperandAt choice path operand)
  | .Move place =>
    let rplace ← h.evalPlace choice place true
    if disjoint then
      if h.deinitMovedPlace && !place.projection.isEmpty then
        let inPlace ← h.forceAllocation choice rplace
        return (← snapshotInPlaceArg h choice inPlace)
      let op ← h.placeToOp choice rplace
      match op.op with
      | .indirect mplace =>
        return (← snapshotInPlaceArg h choice ⟨mplace, op.layout⟩)
      | .immediate _ =>
        if h.deinitMovedPlace then
          let deinitVal : Operand P :=
            if op.layout.layout.isZst then op.op else .immediate .uninit
          let frame ← h.getFrame
          match frame.replaceLocalValue place.localId (.live deinitVal) with
          | .ok frame' => h.setFrame frame'
          | .error e => throw (.stack e)
        return .Copy op
    else
      let inPlace ← h.forceAllocation choice rplace
      return (← snapshotInPlaceArg h choice inPlace)

def evalFnCallArgument (h : Hooks) (choice : C) (operand : MIR.Operand)
    (disjoint : Bool) : M (FnArg P) :=
  evalFnCallArgumentAt h choice operand disjoint #[]

def evalCalleeAndArgs (h : Hooks) (choice : C) (func : MIR.Operand)
    (args : Array SpannedOperand) (dest : Place) : M (EvaluatedCall P Other Extern FnABI) := do
  let isMoveFunc := match func with | .Move _ => h.deinitMovedPlace | _ => false
  let hasMove := h.deinitMovedPlace &&
    (isMoveFunc || args.any (fun a => a.operand matches .Move _))
  let mut tempAllocs : Array (Pointer (Option P)) := #[]
  let mut func ← h.evalOperandAt choice (OperandPath.instruction "function") func
  if hasMove then
    if let .indirect mplace := func.op then
      if !func.layout.layout.isSized then
        throw (.unsupported "unsized indirect callee deinitialization unsupported")
      let tmpFunc ← h.allocateStack choice func.layout
      tempAllocs := tempAllocs.push tmpFunc.mplace.ptr
      cleanupTempArgsOnError h choice tempAllocs do
        h.copyToMemory choice func tmpFunc
        if isMoveFunc then
          h.deinitInPlaceArgument choice ⟨mplace, func.layout⟩
      func := ⟨.indirect tmpFunc.mplace, tmpFunc.layout⟩
  let disjoint := moveDefinitelyDisjoint args dest
  let mut evaluated := #[]
  for index in [:args.size] do
    let some arg := args[index]? |
      cleanupTempArgsOnError h choice tempAllocs
        (throw (.invalidProgram "missing source call argument"))
    let fnArg ← cleanupTempArgsOnError h choice tempAllocs
      (evalFnCallArgumentAt h choice arg.operand disjoint (OperandPath.argument index))
    match fnArg with
    | .InPlace _ (some ⟨.indirect tmpMplace, _⟩) =>
      tempAllocs := tempAllocs.push tmpMplace.ptr
      evaluated := evaluated.push fnArg
    | .InPlace _ _ =>
      evaluated := evaluated.push fnArg
    | .Copy op =>
      if hasMove then
        match op.op with
        | .immediate _ => evaluated := evaluated.push fnArg
        | .indirect _ =>
          if !op.layout.layout.isSized then
            cleanupTempArgsOnError h choice tempAllocs
              (throw (.unsupported "unsized indirect copy argument materialization unsupported"))
          let tmpCopy ← cleanupTempArgsOnError h choice tempAllocs
            (h.allocateStack choice op.layout)
          tempAllocs := tempAllocs.push tmpCopy.mplace.ptr
          cleanupTempArgsOnError h choice tempAllocs
            (h.copyToMemory choice op tmpCopy)
          evaluated := evaluated.push (.Copy ⟨.indirect tmpCopy.mplace, tmpCopy.layout⟩)
      else
        evaluated := evaluated.push fnArg
  cleanupTempArgsOnError h choice tempAllocs do
    let (inputCount, externAbi) ← h.functionSignature choice func.layout
    require (inputCount ≤ evaluated.size) "call has fewer args than normalized signature"
    let extra := (evaluated.extract inputCount evaluated.size).map fun arg => arg.layout.ty
    match ← h.functionKind func.layout.ty with
    | .FnPtr =>
      let fnPtr ← h.readPointer choice func
      let fnVal ← h.getPtrFn choice fnPtr
      let abi ← h.fnAbiOfFnPtr choice func.layout extra
      return ⟨fnVal, evaluated, externAbi, some abi, false, tempAllocs⟩
    | .FnDef definition args =>
      let fnInstance ← h.resolve choice definition args
      let abi ← match fnInstance.kind with
        | .LlvmIntrinsic _ => pure none
        | .Intrinsic definition =>
          pure (some (← h.fnAbiOfInstance choice ⟨.Item definition, fnInstance.args⟩ extra))
        | _ => pure (some (← h.fnAbiOfInstance choice fnInstance extra))
      return ⟨.Instance fnInstance, evaluated, externAbi, abi,
        ← h.requiresCallerLocation fnInstance, tempAllocs⟩
    | .invalid => throw (.invalidProgram "invalid callee type")

/-- Argument copy precedes protection; StorageLive precedes evaluating callee place. -/
def passArgument (h : Hooks) (choice : C) (caller : FnArg P) (callerAbi calleeAbi : ArgABI)
    (calleeIndex : Nat) (dest : Place) (calleeTy : TyId) (alreadyLive : Bool) : M Unit := do
  require (calleeTy == (h.argLayout calleeAbi).ty) "callee type does not match ABI"
  require (caller.layout.layout == (h.argLayout callerAbi).layout) "caller layout does not match ABI"
  unless ← h.checkArgumentCompat choice callerAbi calleeAbi do
    throw (.undefinedBehavior s!"AbiMismatchArgument {calleeIndex}")
  if let .InPlace place (some snap) := caller then
    h.restoreInPlaceMovedBytes choice snap place
  let copied : OpTy P := match caller with
    | .Copy op => op
    | .InPlace place _ => ⟨.indirect place.mplace, place.layout⟩
  if !alreadyLive then
    require dest.projection.isEmpty "nonlocal destination in storage_live_dyn"
    require (!copied.metadata.hasMeta || copied.layout.ty == calleeTy) "argument metadata type mismatch"
    h.storageLiveDyn choice dest.localId copied.metadata
  let dest ← h.evalPlace choice dest false
  h.copyAllowTransmute choice copied dest
  if let .InPlace place _ := caller then
    if h.deinitMovedPlace then
      h.deinitInPlaceArgument choice place
    h.protectArgument choice place

/-- Source stack.rs `allocate_varargs`: static callee ABI checks precede
allocation and copy; no in-place protection is performed for varargs. -/
def allocateVarargs (h : Hooks) (choice : C) (args : Array (FnArg P × ArgABI))
    (calleeAbis : Array ArgABI) : M (Array (MPlaceTy P)) := do
  let mut varargs := #[]
  for idx in [:args.size] do
    let (arg, callerAbi) ← at? args idx "missing variadic caller argument"
    let calleeAbi ← at? calleeAbis idx "missing variadic callee ABI"
    require (← h.checkArgumentCompat choice callerAbi calleeAbi) "variadic ABI compatibility assertion"
    if let .InPlace srcPlace (some snap) := arg then
      h.restoreInPlaceMovedBytes choice snap srcPlace
    let op : OpTy P := match arg with
      | .Copy op => op
      | .InPlace srcPlace _ => ⟨.indirect srcPlace.mplace, srcPlace.layout⟩
    let place ← h.allocateStack choice op.layout
    h.copyToMemory choice op place
    if let .InPlace srcPlace _ := arg then
      if h.deinitMovedPlace then h.deinitInPlaceArgument choice srcPlace
    varargs := varargs.push place
  require (args.size == calleeAbis.size) "excess variadic callee ABI"
  return varargs

/-- Source `init_stack_frame`, including all four argument initialization arms. -/
def initStackFrame (h : Hooks) (choice : C) (fnInstance : CallInstance) (loadedBody : LoadedBody)
    (callerFnAbi : FnABI) (args : Array (FnArg P)) (withCallerLocation : Bool)
    (destination : RuntimeStackPlace P) (cont : ReturnContinuation) : M Unit := do
  let body := loadedBody.body
  let requiresLocation ← h.requiresCallerLocation fnInstance
  if requiresLocation != withCallerLocation then
    throw (.undefinedBehavior "caller/callee #[track_caller] mismatch")
  let callerLocation ← if withCallerLocation then pure (some (← h.callerLocation)) else pure none
  let extra ← if h.abiVariadic callerFnAbi then do
    require (h.abiFixedCount callerFnAbi ≤ args.size) "variadic fixed count outside caller arguments"
    pure ((args.extract (h.abiFixedCount callerFnAbi) args.size).map fun arg => arg.layout.ty)
    else pure #[]
  let calleeFnAbi ← h.fnAbiOfInstance choice fnInstance extra
  unless h.sameConvention callerFnAbi calleeFnAbi do
    throw (.undefinedBehavior "caller/callee calling convention mismatch")
  unless h.abiVariadic callerFnAbi == h.abiVariadic calleeFnAbi do
    throw (.undefinedBehavior "CVariadicMismatch")
  if h.abiVariadic callerFnAbi && h.abiFixedCount callerFnAbi != h.abiFixedCount calleeFnAbi then
    throw (.undefinedBehavior "CVariadicFixedCountMismatch")
  h.checkTargetFeatures choice fnInstance
  let cont := if h.abiCanUnwind calleeFnAbi then cont else
    match cont with
    | .stop _ => cont
    | .goto ret _ => .goto ret .Unreachable
  let destinationOp ← h.placeToOp choice destination
  let destinationMplace := match destinationOp.op with
    | .indirect place => some (MPlaceTy.mk place destinationOp.layout)
    | .immediate _ => none
  h.pushRaw choice fnInstance loadedBody destination cont
  let frame ← h.getFrame
  let preambleSpan ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame { frame with trackCallerArg := callerLocation }
  let vaListArg := if h.abiVariadic calleeFnAbi then some body.argumentCount else none
  let nonCapturing ← h.nonCapturingClosure choice fnInstance calleeFnAbi
  let callerAbis := h.abiArgs callerFnAbi
  let calleeAbis := h.abiArgs calleeFnAbi
  require (args.size + (if withCallerLocation then 1 else 0) == callerAbis.size)
    "mismatch between caller ABI and arguments"
  let (callerIndex, calleeIndex) ← h.withRetagMode choice .FnEntry do
    let mut callerIndex := 0
    let mut calleeIndex := 0
    for zeroIndex in [:body.argumentCount] do
      let localId := zeroIndex + 1
      setSpan h (← h.localSpan body localId)
      let dest : Place := ⟨localId, #[]⟩
      let ty := (← h.localLayout choice localId).ty
      if nonCapturing && localId == 1 then
        require (vaListArg.isNone && body.spreadArgument != some localId) "special closure argument conflict"
        let calleeAbi ← at? calleeAbis calleeIndex "missing closure ABI"
        calleeIndex := calleeIndex + 1
        require (h.isOneZst (h.argLayout calleeAbi) && h.argIsIgnore calleeAbi) "closure self ABI not ignorable 1-ZST"
        h.storageLiveDyn choice localId .none
        if callerAbis.size == calleeAbis.size then
          let _ ← at? args callerIndex "missing closure caller argument"
          let callerAbi ← at? callerAbis callerIndex "missing closure caller ABI"
          callerIndex := callerIndex + 1
          unless h.isOneZst (h.argLayout callerAbi) do
            throw (.undefinedBehavior "AbiMismatchArgument closure self")
          require (h.argIsIgnore callerAbi) "closure caller ABI not ignored"
      else if vaListArg == some localId then
        h.storageLiveDyn choice localId .none
        let dest ← h.evalPlace choice dest false
        let mplace ← h.forceAllocation choice dest
        let mut remaining := #[]
        for idx in [callerIndex:args.size] do
          remaining := remaining.push ((← at? args idx "missing vararg"),
            (← at? callerAbis idx "missing vararg ABI"))
        let varargs ← h.withRetagMode choice .None
          (allocateVarargs h choice remaining (calleeAbis.extract calleeIndex calleeAbis.size))
        callerIndex := args.size
        calleeIndex := calleeAbis.size
        let frame ← h.getFrame
        h.setFrame { frame with vaList := varargs.map fun p => ⟨p.mplace, localMemoryLayout p.layout⟩ }
        let key ← h.vaListPtr choice varargs
        h.writeZeroBytes choice mplace.mplace.ptr mplace.layout.layout.size
        let keyPlace ← h.vaListKeyField choice mplace
        h.writePointerToMemory choice key keyPlace
      else if body.spreadArgument == some localId then
        h.storageLiveDyn choice localId .none
        let fields ← h.tupleFields ty
        for idx in [:fields.size] do
          let fieldTy ← at? fields idx "missing spread field"
          let dest := { dest with projection := #[.Field idx fieldTy] }
          let calleeAbi ← at? calleeAbis calleeIndex "missing spread callee ABI"
          let caller ← match args[callerIndex]? with
            | none => throw (.undefinedBehavior "calling a function with fewer arguments than it requires")
            | some arg => pure arg
          let callerAbi ← at? callerAbis callerIndex "missing spread caller ABI"
          passArgument h choice caller callerAbi calleeAbi calleeIndex dest fieldTy true
          callerIndex := callerIndex + 1
          calleeIndex := calleeIndex + 1
      else
        let calleeAbi ← at? calleeAbis calleeIndex "missing callee ABI"
        let caller ← match args[callerIndex]? with
          | none => throw (.undefinedBehavior "calling a function with fewer arguments than it requires")
          | some arg => pure arg
        let callerAbi ← at? callerAbis callerIndex "missing caller ABI"
        passArgument h choice caller callerAbi calleeAbi calleeIndex dest ty false
        callerIndex := callerIndex + 1
        calleeIndex := calleeIndex + 1
    pure (callerIndex, calleeIndex)
  setSpan h (← h.localSpan body 0)
  unless ← h.checkArgumentCompat choice (h.abiReturn callerFnAbi) (h.abiReturn calleeFnAbi) do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument choice mplace
  setSpan h preambleSpan
  let calleeIndex ← if requiresLocation then do
      let _ ← at? calleeAbis calleeIndex "missing implicit caller location ABI"
      pure (calleeIndex + 1)
    else pure calleeIndex
  require (calleeIndex == calleeAbis.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < args.size then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit choice
  h.pushDone choice

/-- Copy any in-place moved arguments (and any indirect `.Copy` arguments when
an `.InPlace` move is present) into fresh temporary stack allocations and
deinitialize moved caller source places in argument order before a direct call
handler or tail-call frame pop runs, returning the materialized argument list
and the temporary stack pointers to deallocate on call completion. -/
def materializeAndDeinitArgs (h : Hooks) (choice : C)
    (args : Array (FnArg P)) : M (Array (FnArg P) × Array (Pointer (Option P))) := do
  if !h.deinitMovedPlace || !args.any (fun a => a matches .InPlace ..) then
    return (args, #[])
  let mut out := #[]
  let mut tempAllocs : Array (Pointer (Option P)) := #[]
  for arg in args do
    match arg with
    | .Copy op =>
      match op.op with
      | .immediate _ => out := out.push arg
      | .indirect _ =>
        if !op.layout.layout.isSized then
          cleanupTempArgsOnError h choice tempAllocs
            (throw (.unsupported "unsized indirect copy argument materialization unsupported"))
        let tmpPlace ← cleanupTempArgsOnError h choice tempAllocs
          (h.allocateStack choice op.layout)
        tempAllocs := tempAllocs.push tmpPlace.mplace.ptr
        cleanupTempArgsOnError h choice tempAllocs
          (h.copyToMemory choice op tmpPlace)
        out := out.push (.Copy ⟨.indirect tmpPlace.mplace, tmpPlace.layout⟩)
    | .InPlace srcPlace snap? =>
      if let some snap := snap? then
        cleanupTempArgsOnError h choice tempAllocs
          (h.restoreInPlaceMovedBytes choice snap srcPlace)
      if !srcPlace.layout.layout.isSized then
        cleanupTempArgsOnError h choice tempAllocs
          (throw (.unsupported "unsized in-place move argument deinitialization unsupported"))
      let op : OpTy P := ⟨.indirect srcPlace.mplace, srcPlace.layout⟩
      let tmpPlace ← cleanupTempArgsOnError h choice tempAllocs
        (h.allocateStack choice op.layout)
      tempAllocs := tempAllocs.push tmpPlace.mplace.ptr
      cleanupTempArgsOnError h choice tempAllocs do
        h.copyToMemory choice op tmpPlace
        h.deinitInPlaceArgument choice srcPlace
      out := out.push (.Copy ⟨.indirect tmpPlace.mplace, tmpPlace.layout⟩)
  return (out, tempAllocs)

/-- One source dispatch, returning a recursive request for intrinsic fallback
or virtual dispatch. This avoids hiding recursion in opaque machine callbacks. -/
def initFnCallStep (h : Hooks) (choice : C) (request : CallRequest P Other Extern FnABI) :
    M (Option (CallRequest P Other Extern FnABI)) := do
  let request := { request with unwind :=
    if (request.callerFnAbi.any (fun abi => !h.abiCanUnwind abi)) then .Unreachable else request.unwind }
  let needAbi : M FnABI := match request.callerFnAbi with
    | some abi => pure abi
    | none => cleanupTempArgsOnError h choice request.tempAllocs
        (throw (.invalidProgram "FnAbi should have been computed for this call"))
  match request.callee with
  | .Other extra =>
    let abi ← needAbi
    let (args, newTemps) ← cleanupTempArgsOnError h choice request.tempAllocs
      (materializeAndDeinitArgs h choice request.args)
    let allTemps := request.tempAllocs ++ newTemps
    cleanupTempArgsOnError h choice allTemps
      (h.callExtra choice extra abi args request.destination request.target request.unwind)
    deallocateTempArgs h choice allTemps
    pure none
  | .Instance fnInstance =>
    match fnInstance.kind with
    | .Intrinsic _ =>
      cleanupTempArgsOnError h choice request.tempAllocs
        (require (!request.withCallerLocation) "intrinsic received caller location")
      let (args, newTemps) ← cleanupTempArgsOnError h choice request.tempAllocs
        (materializeAndDeinitArgs h choice request.args)
      let allTemps := request.tempAllocs ++ newTemps
      let fallback ← cleanupTempArgsOnError h choice allTemps
        (h.callIntrinsic choice fnInstance (args.map FnArg.copyFnArg)
          request.destination request.target request.unwind)
      match fallback with
      | none =>
        deallocateTempArgs h choice allTemps
        pure none
      | some fallback =>
        cleanupTempArgsOnError h choice allTemps do
          match fallback.kind with
          | .Item _ => pure ()
          | _ => throw (.invalidProgram "intrinsic fallback must be Item")
          return some { request with
            callee := .Instance fallback
            args := args
            withCallerLocation := ← h.requiresCallerLocation fallback
            tempAllocs := allTemps }
    | .LlvmIntrinsic _ =>
      let (args, newTemps) ← cleanupTempArgsOnError h choice request.tempAllocs
        (materializeAndDeinitArgs h choice request.args)
      let allTemps := request.tempAllocs ++ newTemps
      cleanupTempArgsOnError h choice allTemps
        (h.callLlvmIntrinsic choice fnInstance (args.map FnArg.copyFnArg) request.destination request.target)
      deallocateTempArgs h choice allTemps
      pure none
    | .Item _ | .Shim (.VTable _) | .Shim (.Reify ..) | .Shim (.ClosureOnce ..)
    | .Shim (.ConstructCoroutineInClosure ..) | .Shim (.FnPtr ..) | .Shim (.DropGlue ..)
    | .Shim (.Clone ..) | .Shim (.FnPtrAsPtr ..) | .Shim (.FnPtrFromPtr ..)
    | .Shim (.ThreadLocal _) | .Shim (.AsyncDropGlueCtor ..) | .Shim (.AsyncDropGlue ..)
    | .Shim (.FutureDropPoll ..) =>
      let abi ← needAbi
      let (args, newTemps) ← cleanupTempArgsOnError h choice request.tempAllocs do
        if h.deinitMovedPlace then
          if ← h.isForeignItem fnInstance then
            materializeAndDeinitArgs h choice request.args
          else
            pure (request.args, #[])
        else
          pure (request.args, #[])
      let allTemps := request.tempAllocs ++ newTemps
      cleanupTempArgsOnError h choice allTemps do
        let found ← h.findMirOrEvalFn choice fnInstance abi args request.destination request.target request.unwind
        match found with
        | none =>
          if h.deinitMovedPlace then
            for arg in args do
              if let .InPlace place snap? := arg then deinitInPlaceArg h choice place snap?
        | some (body, fnInstance) =>
          let mut args := args
          if h.isRustCall request.callerAbi && !args.isEmpty then
            let last ← at? args (args.size - 1) "missing RustCall tuple"
            args := args.pop
            let fields ← h.tupleFields last.layout.ty
            if fields.isEmpty then
              if h.deinitMovedPlace then
                if let .InPlace place snap? := last then deinitInPlaceArg h choice place snap?
            for idx in [:fields.size] do args := args.push (← h.projectFnArg choice last idx)
          initStackFrame h choice fnInstance body abi args request.withCallerLocation request.destination
            (.goto request.target request.unwind)
      deallocateTempArgs h choice allTemps
      pure none
    | .Virtual definition idx =>
      let abi ← needAbi
      cleanupTempArgsOnError h choice request.tempAllocs do
        require (!request.args.isEmpty) "virtual call missing receiver"
        let (argsForResolve, deinitSizedReceiver?) ← match request.args[0]? with
          | some (FnArg.InPlace receiverPlace (some snap)) =>
            h.restoreInPlaceMovedBytes choice snap receiverPlace
            let restoredArgs :=
              if bound : 0 < request.args.size then
                request.args.set 0 (.InPlace receiverPlace none) bound
              else
                request.args
            pure (restoredArgs, some receiverPlace)
          | _ => pure (request.args, none)
        let (fnInstance, abi, args) ←
          h.resolveVirtual choice fnInstance definition idx abi argsForResolve
        if h.deinitMovedPlace then
          if let some receiverPlace := deinitSizedReceiver? then
            h.deinitInPlaceArgument choice receiverPlace
        return some { request with callee := .Instance fnInstance, callerFnAbi := some abi, args }

/-- Unbounded finite dispatch prefixes. This relation has no runner budget;
resource exhaustion of `initFnCall` says nothing about later UB freedom. -/
inductive DispatchPrefix (h : Hooks) (choice : C) :
    CallRequest P Other Extern FnABI → S → CallRequest P Other Extern FnABI → S → Prop where
  | refl (request) (state) : DispatchPrefix h choice request state request state
  | next {request state nextRequest nextState finalRequest finalState}
      (step : initFnCallStep h choice request state = .ok (some nextRequest) nextState)
      (rest : DispatchPrefix h choice nextRequest nextState finalRequest finalState) :
      DispatchPrefix h choice request state finalRequest finalState

/-- Source recursive dispatch is executable with an explicit resource budget.
Exhaustion is reported, never successful execution or an omitted arm. -/
def initFnCall (h : Hooks) (choice : C) (budget : Nat)
    (request : CallRequest P Other Extern FnABI) : M Unit := do
  match budget with
  | 0 =>
    deallocateTempArgs h choice request.tempAllocs
    throw (.resourceExhaustion "call dispatch budget exhausted")
  | n + 1 =>
    match ← initFnCallStep h choice request with
    | none => pure ()
    | some request => initFnCall h choice n request

def initFnTailCall (h : Hooks) (choice : C) (budget : Nat)
    (evaluated : EvaluatedCall P Other Extern FnABI) : M Unit := do
  let (args, newTemps) ← cleanupTempArgsOnError h choice evaluated.tempAllocs do
    if h.deinitMovedPlace then
      materializeAndDeinitArgs h choice evaluated.args
    else
      pure (evaluated.args.map fun arg => FnArg.Copy arg.copyFnArg, #[])
  let allTemps := evaluated.tempAllocs ++ newTemps
  let (frame, ret, unwind) ← cleanupTempArgsOnError h choice allTemps do
    let frame ← h.popRaw choice
    let (ret, unwind) ← match frame.returnContinuation with
      | .goto ret unwind => pure (ret, unwind)
      | .stop _ => throw (.invalidProgram "cannot tailcall as root of stack")
    pure (frame, ret, unwind)
  initFnCall h choice budget ⟨evaluated.callee, evaluated.callerAbi, evaluated.fnAbi, args,
    evaluated.withCallerLocation, frame.returnPlace, ret, unwind, allTemps⟩
  let action ← h.cleanup choice false frame
  require (action == .normal) "tailcall cleanup must return Normal"

def evalCallTerminator (h : Hooks) (choice : C) (budget : Nat) (terminator : Terminator) : M Unit := do
  match terminator.kind with
  | .Call func args dest target unwind _ _ =>
    let oldIndex ← h.frameIndex
    let oldLoc := (← h.getFrame).location
    let destPlace ← h.evalPlace choice dest false
    let evaluated ← evalCalleeAndArgs h choice func args dest
    initFnCall h choice budget ⟨evaluated.callee, evaluated.callerAbi, evaluated.fnAbi, evaluated.args,
      evaluated.withCallerLocation, destPlace, target,
      if evaluated.fnAbi.any h.abiCanUnwind then unwind else .Unreachable, evaluated.tempAllocs⟩
    if target.isSome then
      if (← h.frameIndex) == oldIndex then
        if (← h.getFrame).location == oldLoc then
          throw (.invalidProgram "evaluating this call made no progress")
  | _ => throw (.invalidProgram "call hook received a non-Call terminator")

def evalTailCallTerminator (h : Hooks) (choice : C) (budget : Nat) (terminator : Terminator) : M Unit := do
  match terminator.kind with
  | .TailCall func args _ =>
    let oldIndex ← h.frameIndex
    let evaluated ← evalCalleeAndArgs h choice func args ⟨0, #[]⟩
    initFnTailCall h choice budget evaluated
    require ((← h.frameIndex) == oldIndex) "evaluating this tail call pushed a new stack frame"
  | _ => throw (.invalidProgram "tailCall hook received a non-TailCall terminator")

def initDropInPlaceCall (h : Hooks) (choice : C) (budget : Nat)
    (place : RuntimeStackPlace P) (originalInstance : CallInstance) (target : BasicBlockId) (unwind : UnwindAction) : M Unit := do
  let place ← h.forceAllocation choice place
  let place ← if ← h.isDynamic place.layout.ty then h.unpackDynForDrop choice place else do
    if h.debugAssertions then
      require (originalInstance == (← h.resolveDropGlue choice place.layout.ty)) "drop glue instance mismatch"
    pure place
  let fnInstance ← h.resolveDropGlue choice place.layout.ty
  let abi ← h.fnAbiOfInstance choice fnInstance #[]
  let arg ← h.mplaceToMutRef choice place
  let ret ← h.fakeUnitReturn choice
  initFnCall h choice budget ⟨.Instance fnInstance, h.rustAbi, some abi, #[.Copy arg], false,
    ret, some target, unwind, #[]⟩

/-- Canonical Stack adapters: callbacks receive the full machine state, and
all stack/machine mutations are installed before returning an error. -/
def liftStackResult (operation : Stack P LocalLayout E → Machine →
    StackRunResult P LocalLayout E Machine A) :
    CallM (StepState P LocalLayout E Machine) A := do
  let state ← get
  let result := operation state.stack state.machine
  set ({ stack := result.stack, machine := result.state } : StepState P LocalLayout E Machine)
  match result.outcome with
  | .ok value => pure value
  | .error error => throw (.stack error)

def pushRawFromStack (hooks : StackLifecycleHooks P LocalLayout E Machine)
    (bodySpan : Body → Except StepError SpanRef)
    (fnInstance : CallInstance) (body : LoadedBody) (destination : RuntimeStackPlace P)
    (cont : ReturnContinuation) : CallM (StepState P LocalLayout E Machine) Unit := do
  let span ← match bodySpan body.body with
    | .ok value => pure value
    | .error error => throw error
  liftStackResult fun stack state => stack.pushStackFrameRaw state hooks body fnInstance cont destination span

def pushDoneFromStack (hooks : StackLifecycleHooks P LocalLayout E Machine) :
    CallM (StepState P LocalLayout E Machine) Unit :=
  liftStackResult fun stack state => stack.pushStackFrameDone state hooks

def popRawFromStack (hooks : StackLifecycleHooks P LocalLayout E Machine) :
    CallM (StepState P LocalLayout E Machine) (Frame P LocalLayout E) :=
  liftStackResult fun stack state => stack.popStackFrameRaw state hooks

def cleanupFromStack (hooks : StackLifecycleHooks P LocalLayout E Machine)
    (unwinding : Bool) (frame : Frame P LocalLayout E) :
    CallM (StepState P LocalLayout E Machine) ReturnAction :=
  liftStackResult fun stack state => stack.cleanupStackFrame state hooks unwinding frame

/-- Adapt to ControlFlow.TerminatorHooks while retaining EStateM error state. -/
def run (computation : CallM S A) (state : S) : StepResult S A :=
  match computation state with
  | .ok value state => (state, .ok value)
  | .error error state => (state, .error error)

end Call
end Miri.Interpreter

namespace Miri.Interpreter.Call
open Miri Miri.ABI Miri.Memory Miri.MIR
set_option autoImplicit false
variable {P S C E Other Extern : Type}
abbrev ZeroHooks (P S C E Other Extern : Type) := CallHooks P S C E Other Extern (FnAbi TyId) (ArgAbi TyId)
 def zeroCore (h : ZeroHooks P S C E Other Extern) (choice : C) (fnInstance : CallInstance) (body : LoadedBody)
    (abi : FnAbi TyId) (destination : MPlaceTy P) (cont : ReturnContinuation) : CallM S Unit := do
  let cont := if h.abiCanUnwind abi then cont else
    match cont with
    | .stop _ => cont
    | .goto ret _ => .goto ret .Unreachable
  h.pushRaw choice fnInstance body (.memory destination) cont
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (_,calleeIndex) ← h.withRetagMode choice .FnEntry (pure (0,0))
  setSpan h (← h.localSpan body.body 0)
  unless ← h.checkArgumentCompat choice abi.ret abi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  h.protectArgument choice destination
  setSpan h preamble
  require (calleeIndex == 0) "mismatch between callee ABI and callee body arguments"
  h.afterFrameInit choice
  h.pushDone choice
 theorem zero_entry_core (h : ZeroHooks P S C E Other Extern) (choice : C) (fnInstance : CallInstance)
    (body : LoadedBody) (abi : FnAbi TyId) (destination : MPlaceTy P) (cont : ReturnContinuation)
    (requires : h.requiresCallerLocation fnInstance = pure false)
    (instanceAbi : h.fnAbiOfInstance choice fnInstance #[] = pure abi)
    (features : h.checkTargetFeatures choice fnInstance = pure ())
    (memory : h.placeToOp choice (.memory destination) = pure ⟨.indirect destination.mplace,destination.layout⟩)
    (closure : h.nonCapturingClosure choice fnInstance abi = pure false)
    (variadic : h.abiVariadic abi = false)
    (convention : h.sameConvention abi abi = true)
    (arguments : h.abiArgs abi = #[])
    (ret : h.abiReturn abi = abi.ret)
    (count : body.body.argumentCount = 0) :
    initStackFrame h choice fnInstance body abi #[] false (.memory destination) cont =
      zeroCore h choice fnInstance body abi destination cont := by
  simp [initStackFrame,zeroCore,requires,instanceAbi,features,memory,closure,variadic,
    convention,arguments,ret,count,require,setSpan,bind_assoc]

/-- Source specialization for a zero-argument call whose actual preflight
operand is immediate. The preflight equation is an internal composition edge. -/
def zeroImmediateCore (h : ZeroHooks P S C E Other Extern) (choice : C)
    (fnInstance : CallInstance) (body : LoadedBody) (abi : FnAbi TyId)
    (destination : RuntimeStackPlace P) (cont : ReturnContinuation) : CallM S Unit := do
  let cont := if h.abiCanUnwind abi then cont else
    match cont with | .stop _ => cont | .goto ret _ => .goto ret .Unreachable
  h.pushRaw choice fnInstance body destination cont
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (_,calleeIndex) ← h.withRetagMode choice .FnEntry (pure (0,0))
  setSpan h (← h.localSpan body.body 0)
  unless ← h.checkArgumentCompat choice abi.ret abi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  setSpan h preamble
  require (calleeIndex == 0) "mismatch between callee ABI and callee body arguments"
  h.afterFrameInit choice
  h.pushDone choice

 theorem zero_entry_immediate (h : ZeroHooks P S C E Other Extern) (choice : C)
    (fnInstance : CallInstance) (body : LoadedBody) (abi : FnAbi TyId)
    (destination : RuntimeStackPlace P) (cont : ReturnContinuation)
    (before cached : S) (value : Immediate P) (layout : LocalLayout)
    (requires : h.requiresCallerLocation fnInstance = pure false)
    (instanceAbi : h.fnAbiOfInstance choice fnInstance #[] = pure abi)
    (features : h.checkTargetFeatures choice fnInstance = pure ())
    (immediate : h.placeToOp choice destination before = .ok ⟨.immediate value,layout⟩ cached)
    (closure : h.nonCapturingClosure choice fnInstance abi = pure false)
    (variadic : h.abiVariadic abi = false) (convention : h.sameConvention abi abi = true)
    (arguments : h.abiArgs abi = #[]) (ret : h.abiReturn abi = abi.ret)
    (count : body.body.argumentCount = 0) :
    initStackFrame h choice fnInstance body abi #[] false destination cont before =
      zeroImmediateCore h choice fnInstance body abi destination cont cached := by
  simp only [initStackFrame,zeroImmediateCore,requires,instanceAbi,features,closure,variadic,
    convention,arguments,ret,count,require,setSpan,bind_assoc,pure_bind]
  simp [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,immediate]
  rfl


def zeroIndirectCore (h : ZeroHooks P S C E Other Extern) (choice : C) (fnInstance : CallInstance) (body : LoadedBody)
    (abi : FnAbi TyId) (destination : RuntimeStackPlace P) (memory : MPlaceTy P) (cont : ReturnContinuation) : CallM S Unit := do
  let cont := if h.abiCanUnwind abi then cont else
    match cont with
    | .stop _ => cont
    | .goto ret _ => .goto ret .Unreachable
  h.pushRaw choice fnInstance body destination cont
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (_,calleeIndex) ← h.withRetagMode choice .FnEntry (pure (0,0))
  setSpan h (← h.localSpan body.body 0)
  unless ← h.checkArgumentCompat choice abi.ret abi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  h.protectArgument choice memory
  setSpan h preamble
  require (calleeIndex == 0) "mismatch between callee ABI and callee body arguments"
  h.afterFrameInit choice
  h.pushDone choice

 theorem zero_entry_indirect (h : ZeroHooks P S C E Other Extern) (choice : C)
    (fnInstance : CallInstance) (body : LoadedBody) (abi : FnAbi TyId)
    (destination : RuntimeStackPlace P) (cont : ReturnContinuation)
    (before cached : S) (memory : MPlaceTy P)
    (requires : h.requiresCallerLocation fnInstance = pure false)
    (instanceAbi : h.fnAbiOfInstance choice fnInstance #[] = pure abi)
    (features : h.checkTargetFeatures choice fnInstance = pure ())
    (indirect : h.placeToOp choice destination before = .ok ⟨.indirect memory.mplace,memory.layout⟩ cached)
    (closure : h.nonCapturingClosure choice fnInstance abi = pure false)
    (variadic : h.abiVariadic abi = false) (convention : h.sameConvention abi abi = true)
    (arguments : h.abiArgs abi = #[]) (ret : h.abiReturn abi = abi.ret)
    (count : body.body.argumentCount = 0) :
    initStackFrame h choice fnInstance body abi #[] false destination cont before =
      zeroIndirectCore h choice fnInstance body abi destination memory cont cached := by
  simp only [initStackFrame,zeroIndirectCore,requires,instanceAbi,features,closure,variadic,
    convention,arguments,ret,count,require,setSpan,bind_assoc,pure_bind]
  simp [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,indirect]
  rfl

end Miri.Interpreter.Call
