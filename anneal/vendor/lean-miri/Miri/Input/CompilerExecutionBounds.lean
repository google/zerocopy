import Miri.Input.RuntimeMetadata
import Miri.Interpreter.Step
import Miri.Memory.Pointer

/-! Interpreter allocation/dynamic-value bounds come from the actual target
pointer storage width. They are not an independently configurable memory
policy and are not the LLVM ABI's smaller obj_size_bound on 64-bit targets.
Source: rustc_middle/mir/interpret/pointer.rs:13–40. -/
namespace Miri.Input.CompilerExecutionBounds
open Miri.ABI Miri.Memory Miri.Interpreter

def maximum (runtime : RuntimeTargetDataLayout) : Except StepError Size :=
  (PointerArithmetic.maxSizeOfVal ⟨runtime.pointerSize⟩).mapError fun error =>
    .invalidProgram s!"compiler target max_size_of_val: {reprStr error}"
end Miri.Input.CompilerExecutionBounds
