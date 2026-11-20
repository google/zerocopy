import Miri.Input.EvalCoreMachine
import Miri.Input.CompilerTargetFeatures
import Miri.Input.CompilerArchitectureFacts
import Miri.Interpreter.IntrinsicX86

/-! Physical LLVM architecture dispatch on the same canonical execution state.
Pinned sources: intrinsics/mod.rs, intrinsics/x86/mod.rs and helpers.rs
expect_target_feature_for_intrinsic. Target identity and features are compiler
facts; host architecture and target-triple parsing are never substitutes. -/
namespace Miri.Input.EvalArchitectureMachine
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

private def liftQuery (query : Except String A) : EStateM StepError S A :=
  match query with
  | .ok value => pure value
  | .error error => throw (.unsupported error)

/-- Exact compiler session target.arch, added independently of target triple. -/
def targetArch (prepared : CompilerIntrinsicFacts.Prepared) : Except String String := do
  let session ← prepared.program.input.raw.getObjVal? "compiler_session_queries"
  (← session.getObjVal? "target_arch").getStr?

/-- helpers.rs:940–952: absent enabled ISA feature is UB, whereas absent
compiler evidence is an unresolved input obligation. -/
def expectFeature (prepared : CompilerIntrinsicFacts.Prepared)
    (intrinsic feature : String) : EStateM StepError S Unit := do
  unless ← liftQuery (CompilerTargetFeatures.available prepared feature) do
    throw (.undefinedBehavior s!"attempted to call intrinsic `{intrinsic}` that requires missing target feature {feature}")

/-- Install concrete SIMD projection/transmutes, all x86 families and shared
choice-tape float perturbations. Only compiler type construction, signature
checks, host sqrt and source numerical settings remain in the x86 leaf record.
The scheduler yield updates the canonical ThreadManager directly. -/
def dispatcher [DecidableEq K]
    (prepared : CompilerIntrinsicFacts.Prepared)
    (access : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (choices : ExecutionChoices.Access (ValidityMachine.State K U))
    (simd : IntrinsicSimdHooks Provenance (ValidityMachine.State K U) C (RuntimePlace Provenance))
    (u128Layout : LocalLayout)
    (x86 : IntrinsicX86.Hooks Provenance (ValidityMachine.State K U) C (RuntimePlace Provenance))
    (base : IntrinsicArchitecture.DispatchHooks Provenance (ValidityMachine.State K U) C (RuntimePlace Provenance)) :
    Except String (IntrinsicArchitecture.DispatchHooks Provenance (ValidityMachine.State K U) C (RuntimePlace Provenance)) := do
  let arch ← targetArch prepared
  let sse2 ← CompilerTargetFeatures.available prepared "sse2"
  let architecture := IntrinsicVectorMachine.bindArchitecture
    {base.architecture with expectFeature := fun _ intrinsic feature => expectFeature prepared intrinsic feature}
    simd projection u128Layout
  let x86 := IntrinsicVectorMachine.bindX86
    {x86 with x86_64 := arch == "x86_64",sse2Enabled := sse2
              yieldThread := fun _ => modify fun state =>
                {state with machine := {state.machine with threads := state.machine.threads.yield}}}
    architecture access projection pointers
  let x86 := ExecutionChoiceBindings.x86Hooks choices x86
  pure (IntrinsicX86.architectureDispatch x86 {base with architecture := x86.architecture,targetArch := arch})

/-- Apply after EvalCoreMachine.config, so LLVM operations share its physical
SIMD, access, projection, and scalar dictionaries. This does not reconstruct or
capture an older fallback call chain. Existing core files need no modification. -/
def bind
    (prepared : CompilerIntrinsicFacts.Prepared)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D O Aff B Host)))
    (u128Layout : LocalLayout)
    (x86 : IntrinsicX86.Hooks Provenance (EvalCoreMachine.State Os R P H D O Aff B Host) C (RuntimePlace Provenance))
    (base : ExecutionMachine.Config MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host) C O X ClockHost) :
    Except String (ExecutionMachine.Config MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host) C O X ClockHost) :=
  pure {base with calls := {base.calls with llvm := fun callee => do
    let original ← base.calls.llvm callee
    match dispatcher prepared base.access base.projection pointers EvalCoreMachine.tape
        (base.intrinsics callee).simdHooks u128Layout x86 original with
    | .ok llvm => pure llvm
    | .error reason => throw (.unsupported reason)}}

/-- Compiler-closed production entry: no caller-provided x86 implementation or
layout-constructor callbacks. Signature symbol-clash and host math are the
same source policies used by the enclosing foreign/intrinsic factory. -/
def compilerDispatcher
    (context : CompilerFacts.Context) (prepared : CompilerIntrinsicFacts.Prepared)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D O Aff B Host)))
    (checkSymbolClash : String → RvalueM (EvalCoreMachine.State Os R P H D O Aff B Host) Unit)
    (math : Math.Hooks Provenance (EvalCoreMachine.State Os R P H D O Aff B Host) C (RuntimePlace Provenance))
    (access : PlaceMachine.AccessConfig MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host))
    (projection : PlaceProjectionHooks Provenance (EvalCoreMachine.State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (simdBase : IntrinsicSimdHooks Provenance (EvalCoreMachine.State Os R P H D O Aff B Host) C (RuntimePlace Provenance))
    (unsupportedForeignItem : String → String → StepError) :
    Except String (IntrinsicArchitecture.DispatchHooks Provenance (EvalCoreMachine.State Os R P H D O Aff B Host) C (RuntimePlace Provenance)) := do
  unless context.runtime.source.raw == prepared.program.input.raw do
    throw "architecture runtime/compiler facts are from different documents"
  let boolLayout ← context.primitiveLayout "bool"
  let u8Layout ← context.primitiveLayout "u8"
  match context.primitiveLayout "u128", targetArch prepared,
      CompilerTargetFeatures.available prepared "sse2" with
  | .error error, _, _ => .error error
  | _, .error error, _ => .error error
  | _, _, .error error => .error error
  | .ok u128Layout, .ok arch, .ok sse2 =>
    let simd := CompilerArchitectureFacts.simdHooks context
      {simdBase with target := context.runtime.target.base,boolTy := boolLayout.ty,u8Ty := u8Layout.ty}
    let simd := {simd with mathLane := Math.simdMathLane math}
    let architecture : ArchitectureHooks Provenance (EvalCoreMachine.State Os R P H D O Aff B Host) C (RuntimePlace Provenance) :=
      {simd
       checkSignature := fun _ name _ => checkSymbolClash name
       expectFeature := fun _ name feature => expectFeature prepared name feature
       transmuteDestU128 := fun choice dest => IntrinsicVectorMachine.transmuteWrite projection choice dest u128Layout}
    let x86 : IntrinsicX86.Hooks Provenance (EvalCoreMachine.State Os R P H D O Aff B Host) C (RuntimePlace Provenance) :=
      {architecture
       x86_64 := arch == "x86_64"
       sse2Enabled := sse2
       yieldThread := fun _ => modify fun state =>
         {state with machine := {state.machine with threads := state.machine.threads.yield}}
       arrayLayout := fun _ element count => RuntimeArrayQueries.arrayLayout EvalProjectionMachine.arrays element count
       integerLayout := fun _ bits signed => liftQuery (CompilerArchitectureFacts.integerLayoutContext context bits signed)
       transmuteRead := fun choice source target => do
         match source.transmute (← projection.place.projection choice) target with
         | .ok value => pure value
         | .error error => throw (IntrinsicVectorMachine.projectionError error)
       transmuteWrite := IntrinsicVectorMachine.transmuteWrite projection
       twiceWideLayout := fun _ id => liftQuery (CompilerArchitectureFacts.twiceWideLayoutContext context id)
       sqrt := fun _ value => Math.engine (Math.sqrt value)
       floatNondet := math.floatOps.floatNondeterministic
       roundingError := match math.errorMode with | .none => .none | .random => .random | .max => .max
       errorMagnitude := math.relativeMagnitude
       errorNegative := math.relativeNegative
       memCopy := fun _ source dest size nonoverlapping =>
         GlobalMemoryCopyMachine.copy access pointers.arithmetic source dest size 1 nonoverlapping}
    dispatcher prepared access projection pointers EvalCoreMachine.tape simd u128Layout x86
      {architecture,targetArch := arch,x86 := IntrinsicX86.eval x86,unsupportedForeignItem}

/-- Install the same direct constructor in an already assembled configuration. -/
def bindCompiler
    (context : CompilerFacts.Context) (prepared : CompilerIntrinsicFacts.Prepared)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D O Aff B Host)))
    (checkSymbolClash : String → RvalueM (EvalCoreMachine.State Os R P H D O Aff B Host) Unit)
    (math : Math.Hooks Provenance (EvalCoreMachine.State Os R P H D O Aff B Host) C (RuntimePlace Provenance))
    (base : ExecutionMachine.Config MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host) C O X ClockHost) :
    Except String (ExecutionMachine.Config MiriMemoryKind (EvalCoreMachine.User Os R P H D O Aff B Host) C O X ClockHost) :=
  pure {base with calls := {base.calls with llvm := fun callee => do
    let original ← base.calls.llvm callee
    match compilerDispatcher context prepared pointers checkSymbolClash math base.access base.projection
        (base.intrinsics callee).simdHooks original.unsupportedForeignItem with
    | .ok llvm => pure llvm
    | .error reason => throw (.unsupported reason)}}

end Miri.Input.EvalArchitectureMachine
