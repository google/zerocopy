import Miri.Interpreter.FrameMetadata
import Miri.Interpreter.UnixMemory

/-! Actual std-only mmap policy consumes the source frame predicate. -/
namespace Miri.Interpreter.FrameMetadataBindings
open Miri.Memory

def unixMemory (compiler : FrameMetadata.CompilerHooks K User)
    (base : UnixMemory.Hooks Provenance (MachineHooks.State K User) D MD B I) :
    UnixMemory.Hooks Provenance (MachineHooks.State K User) D MD B I :=
  { base with frameInStd := FrameMetadata.frameInStd compiler }

end Miri.Interpreter.FrameMetadataBindings
