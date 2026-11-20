import Std

/-! Exact Miri machine allocation kinds and leak policy from the pinned
`machine.rs`. Leak permission classifies allocation ownership; it is not a
claim that an access is valid or a program is UB-free. -/
namespace Miri.Memory

inductive MiriMemoryKind where
  | rust | miri | c | winHeap | winLocal | machine | runtime
  | global | externStatic | tls | mmap | socketAddress
  deriving DecidableEq, Repr

namespace MiriMemoryKind

def mayLeak : MiriMemoryKind → Bool
  | .rust | .miri | .c | .winHeap | .winLocal | .runtime => false
  | .machine | .global | .externStatic | .tls | .mmap | .socketAddress => true

/-- Source allocation-span selection, retained independently of leak policy. -/
def shouldSaveAllocationSpan : MiriMemoryKind → Bool
  | .rust | .miri | .c | .winHeap | .winLocal | .mmap => true
  | .machine | .global | .externStatic | .tls | .runtime | .socketAddress => false

end MiriMemoryKind
end Miri.Memory
