import Miri.Interpreter.GlobalConstructors
import Miri.Interpreter.PlaceTypes

/-! Pinned eval.rs::MainThreadState::on_main_stack_empty (309-360), call_main
(481-558), ty/instance.rs::Instance::mono (527-538), rustc_session/config/
sigpipe.rs::DEFAULT. Compiler queries, actual allocation/read/call operations
remain required stateful leaves; source ordering and checks execute here. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.Concurrency

inductive MainEntryType where
  | miriStart
  | rustcMain (declaredSigpipe : UInt8)
inductive MainGenericParameter where
  | lifetime | typeParameter | constParameter
structure MainSignature where
  hasBoundVariables : Bool
  outputHasBoundVariables : Bool
  returnType : MIR.TyId
  /-- Compiler Ty::new_fn_ptr from the same entry signature. -/
  fnPointerType : MIR.TyId
inductive MainThreadStage (P : Type) where
  | globalConstructors (entry : MIR.DefId) (entryType : MainEntryType)
      (argc argv : TlsImmediate P)
  | running
  | exiting (stage : ProgramExitStage) (exitCode : Int32)
structure MainThreadState (P E H : Type) where
  constructors : GlobalCtorState P E H
  stage : MainThreadStage P
  mainReturnPlace : Option (MPlaceTy P)
inductive MainThreadError (Error : Type) where
  | constructor (error : TlsExecutionError Error)
  | programExit (error : ProgramExitError Error)
  | scalar (error : ScalarError)
  | leaf (error : Error)
  | sourceInvariant (message : String)
  | missingStartLangItem
  | unresolvedStartInstance
  | missingMainReturnPlace
  | undefinedBehaviorExitCodeOutOfRange (exitCode : Int64)
  deriving Repr
abbrev MainThreadM (P E H Error A : Type) := EStateM (MainThreadError Error) (MainThreadState P E H) A
structure MainThreadQueries (P E H Error : Type) where
  isizeLayout : TyAndLayout MIR.TyId
  u8Layout : TyAndLayout MIR.TyId
  /-- Includes parent parameters, in compiler GenericArgs::for_item order. -/
  genericParameters : MIR.DefId → MainThreadM P E H Error (Array MainGenericParameter)
  /-- Actual allocate(layout, MiriMemoryKind::Machine), including hooks. -/
  allocate : TyAndLayout MIR.TyId → MemoryKind MiriMemoryKind → MainThreadM P E H Error (MPlaceTy P)
  entrySignature : MIR.DefId → MainThreadM P E H Error MainSignature
  startLangItem : MainThreadM P E H Error (Option MIR.DefId)
  /-- Instance::try_resolve in the actual interpreter typing environment. -/
  resolveInstance : MIR.DefId → Array MIR.GenericArg → MainThreadM P E H Error (Option CallInstance)
  fnPointer : CallInstance → MainThreadM P E H Error (Pointer P)
  layoutOf : MIR.TyId → MainThreadM P E H Error (TyAndLayout MIR.TyId)
  /-- Actual call_function with Rust ABI and Stop{cleanup:true}. -/
  callFunction : CallInstance → Array (OpTy P) → MPlaceTy P → MainThreadM P E H Error Unit
  /-- Actual target-isize memory read, with pointer/initialization/borrow/race
  checks. An arbitrary precomputed integer does not satisfy this leaf. -/
  readTargetIsize : MPlaceTy P → MainThreadM P E H Error Int64

private def mainArgument (value : TlsImmediate P) : OpTy P := ⟨.immediate value.value,value.layout⟩
private def scalarArgument (value : Scalar P) (layout : TyAndLayout MIR.TyId) : OpTy P :=
  ⟨.immediate (.scalar value),layout⟩

/-- Source Instance::mono erases only lifetime parameters; type/const params
are invariant errors, not empty generic argument lists. -/
private def monoMainInstance (queries : MainThreadQueries P E H Error) (entry : MIR.DefId) :
    MainThreadM P E H Error CallInstance := do
  let mut args := #[]
  for parameter in ← queries.genericParameters entry do
    match parameter with
    | .lifetime => args := args.push (.Lifetime .Erased)
    | .typeParameter => throw (.sourceInvariant "Instance::mono: entry has type parameters")
    | .constParameter => throw (.sourceInvariant "Instance::mono: entry has const parameters")
  pure ⟨.Item entry,args⟩

def callMain (target : RuntimeTargetDataLayout) (queries : MainThreadQueries P E H Error)
    (entry : MIR.DefId) (entryType : MainEntryType) (argc argv : TlsImmediate P) : MainThreadM P E H Error Unit := do
  let entryInstance ← monoMainInstance queries entry
  let retPlace ← queries.allocate queries.isizeLayout (.machine .machine)
  let state ← EStateM.get
  EStateM.set { state with mainReturnPlace := some retPlace }
  match entryType with
  | .miriStart => queries.callFunction entryInstance #[mainArgument argc,mainArgument argv] retPlace
  | .rustcMain _ =>
    let signature ← queries.entrySignature entry
    if signature.hasBoundVariables then throw (.sourceInvariant "entry fn_sig has bound variables")
    if signature.outputHasBoundVariables then throw (.sourceInvariant "entry output type has bound variables")
    let some startId ← queries.startLangItem | throw .missingStartLangItem
    let some startInstance ← queries.resolveInstance startId #[.Type signature.returnType]
      | throw .unresolvedStartInstance
    let mainPointer ← queries.fnPointer entryInstance
    let mainPointerLayout ← queries.layoutOf signature.fnPointerType
    let pointerScalar := Scalar.fromPointer target.base mainPointer
    -- Source explicitly ignores declared SIGPIPE and always uses DEFAULT=0.
    let sigpipe ← match Scalar.fromUInt (BitVec.ofNat 128 0) queries.u8Layout.layout.size with
      | .ok scalar => pure scalar
      | .error error => throw (.scalar error)
    queries.callFunction startInstance
      #[scalarArgument pointerScalar mainPointerLayout,mainArgument argc,mainArgument argv,
        scalarArgument sigpipe queries.u8Layout] retPlace

/-- Global ctor callbacks run before main is scheduled. Main's actual return
memory is read only once its stack empties; signed i32 narrowing failure is UB.
ProgramExit's machine-stop outcome propagates without reporting callback Ready. -/
def mainThreadOnStackEmpty [PointerProvenance P] (format : ConstructorBinaryFormat)
    (platform : TlsPlatform) (target : RuntimeTargetDataLayout)
    (constructors : GlobalCtorQueries P E H Error) (main : MainThreadQueries P E H Error)
    (destructors : TlsDestructorQueries P E H Error) (termination : ThreadExitQueries P E H ProvExtra Error)
    : MainThreadM P E H Error ProgramExitPoll := do
  let state ← EStateM.get
  match state.stage with
  | .globalConstructors entry entryType argc argv =>
    let (poll,next) ← match globalConstructorsOnStackEmpty format target constructors state.constructors with
      | .ok poll next => pure (poll,next)
      | .error error next => EStateM.set { state with constructors := next }; throw (.constructor error)
    EStateM.set { state with constructors := next }
    match poll with
    | .Pending => pure .pending
    | .Ready =>
      callMain target main entry entryType argc argv
      let after ← EStateM.get
      EStateM.set { after with stage := .running }
      pure .pending
  | .running =>
    let some retPlace := state.mainReturnPlace | throw .missingMainReturnPlace
    let exitCode ← main.readTargetIsize retPlace
    if exitCode.toInt < -(2^31 : Int) || exitCode.toInt ≥ 2^31 then
      throw (.undefinedBehaviorExitCodeOutOfRange exitCode)
    let after ← EStateM.get
    let handler := ProgramExitState.new after.constructors.execution (Int32.ofInt exitCode.toInt) .mainThreadFinish
    EStateM.set { after with
      constructors := { after.constructors with execution := handler.execution }
      stage := .exiting handler.stage handler.exitCode }
    pure .pending
  | .exiting stage exitCode =>
    let handler : ProgramExitState P E H := ⟨state.constructors.execution,stage,exitCode,.mainThreadFinish⟩
    match programExitOnStackEmpty platform target destructors termination handler with
    | .ok poll next =>
      EStateM.set { state with
        constructors := { state.constructors with execution := next.execution }
        stage := .exiting next.stage next.exitCode }
      pure poll
    | .error error next =>
      EStateM.set { state with
        constructors := { state.constructors with execution := next.execution }
        stage := .exiting next.stage next.exitCode }
      throw (.programExit error)

end Miri.Interpreter
