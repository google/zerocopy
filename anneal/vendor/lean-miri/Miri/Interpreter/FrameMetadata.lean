import Miri.Interpreter.FrameRelevance
import Miri.Interpreter.Backtrace
import Miri.Interpreter.VirtualCalls

/-! Source helpers.rs frame_in_std/user_relevance and thread.rs relevance cache.
Compiler crate identity, inline scopes and caller attributes remain required queries. -/
namespace Miri.Interpreter.FrameMetadata
open Miri.MIR Miri.Concurrency
open MachineHooks

structure CompilerHooks (K User : Type) where
  requiresCallerLocation : CallInstance → M K User Bool
  isLocalDefinition : CallInstance → M K User Bool
  definitionCrate : CallInstance → M K User Nat
  userRelevantCrate : Nat → M K User Bool
  crateName : Nat → M K User String
  sourceScope : BodyIdentity → CallInstance → Body → Nat → M K User VirtualCalls.CallerScope

def userRelevance (h : CompilerHooks K User) (frame : Frame P LocalLayout E) : M K User UInt8 := do
  if ← h.requiresCallerLocation frame.functionInstance then return 0
  if ← h.isLocalDefinition frame.functionInstance then return 255
  if ← h.userRelevantCrate (← h.definitionCrate frame.functionInstance) then return 255
  return 1

private def sourceInfo (frame : Frame P LocalLayout E) : Except StepError (Option SourceInfo) := do
  match frame.location with
  | .unwinding _ => return none
  | .mir location =>
    let some block := frame.body.basicBlocks[location.block]?
      | throw (.invalidProgram "frame source block missing")
    if location.statementIndex == block.statements.size then return some block.terminator.sourceInfo
    let some statement := block.statements[location.statementIndex]?
      | throw (.invalidProgram "frame source statement missing")
    return some statement.sourceInfo

private def lift (result : Except StepError A) : M K User A :=
  match result with | .ok value => pure value | .error error => throw error

def frameInStd (h : CompilerHooks K User) : M K User Bool := do
  let frame ← currentFrame
  let mut calleeInstance := frame.functionInstance
  if let some info ← lift (sourceInfo frame) then
    let scope ← h.sourceScope frame.bodyIdentity frame.functionInstance frame.body info.scope
    if let some parent := scope.inlinedParentScope then
      let parent ← h.sourceScope frame.bodyIdentity frame.functionInstance frame.body parent
      let some (callee, _) := parent.inlined
        | throw (.invalidProgram "inlined_parent_scope points to scope without inline info")
      calleeInstance := callee
  return (← h.crateName (← h.definitionCrate calleeInstance)) == "std"


end Miri.Interpreter.FrameMetadata
