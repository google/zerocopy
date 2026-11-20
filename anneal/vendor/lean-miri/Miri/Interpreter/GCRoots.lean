import Miri.Interpreter.MemoryExtras
import Miri.Interpreter.ProvenanceGC
import Miri.Interpreter.ThreadTls
import Miri.Interpreter.ThreadLocal
import Miri.Interpreter.EnvVars
import Miri.Interpreter.ExternStatic
import Miri.Interpreter.MainThread

/-! Concrete ghost visitors for source state embeddings. No dereference,
callback invocation or dropped missing typed tokens. Remaining OS-owned state
requires its own actual visitor before a complete interpreter is available. -/
namespace Miri.Interpreter.ProvenanceGC.Roots
open Miri.Memory Miri.Concurrency

/-- The active stack is visited by the GC driver, not duplicated here. -/
def inactiveStacks (roots : Roots) (manager : ThreadManager) (registry : ThreadStacks.Registry) :
    Except StepError Roots := do
  ThreadStacks.validate registry manager
  let mut roots := roots
  for saved in registry.inactive do roots ← roots.stack saved.stack
  return roots

def threadTls (roots : Roots) (data : ThreadTlsData Provenance) : Except StepError Roots := do
  let mut roots := roots
  for entry in data.provenanceRoots do
    match entry with
    | .pointer pointer => roots := roots.pointer pointer
    | .scalar scalar => roots ← roots.scalar scalar
  return roots

/-- Match the authoritative manager entries against actual typed pointers. -/
def threadLocalAllocations (roots : Roots) (manager : ThreadManager)
    (entries : Array (ThreadLocalEntry Provenance)) : Except StepError Roots := do
  let mut roots := roots
  for entry in manager.threadLocalAllocs do
    let found := entries.filter (fun pointer => pointer.runtimeId.value.toNat == entry.pointerToken)
    let some pointer := found[0]? | throw (.invalidProgram "GC: TLS pointer token missing")
    if found.size != 1 then throw (.invalidProgram "GC: TLS pointer token ambiguous")
    if pointer.definition != entry.definitionToken || pointer.thread != entry.thread then
      throw (.invalidProgram "GC: TLS pointer identity mismatch")
    roots := roots.strictPointer pointer.pointer
  return roots

def envVars (roots : Roots) (env : EnvVars.State (Option Provenance) Os) : Roots :=
  (EnvVars.provenanceRoots env).foldl Roots.pointer roots

def externStatics (roots : Roots) (state : ExternStatic.State) : Roots :=
  (ExternStatic.provenanceRoots state).foldl Roots.strictPointer roots

/-- Main's saved return place remains a root even when its stack is empty. -/
def mainReturnPlace (roots : Roots) (state : MainThreadState Provenance E H) : Except StepError Roots :=
  match state.mainReturnPlace with
  | none => .ok roots
  | some place => roots.memPlace place.mplace

/-- Source allocation race-handler visitor traces every retained weak-buffer
value. Sync objects are intentionally omitted by source AllocExtra::visit.
Their captured representation metadata must not create extra strong roots. -/
def weakMemory (roots : Roots) (registry : MemoryExtras.Registry Payload) : Except StepError Roots := do
  let mut roots := roots
  for value in MemoryExtras.weakValues registry do roots ← roots.scalar value
  return roots

end Miri.Interpreter.ProvenanceGC.Roots
