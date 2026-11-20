import Miri.ABI.Align

namespace Miri.Memory
open Miri.ABI
/-- Owned source MiriAllocBytes backing. Pointer zero is excluded by the
native lifecycle constructor; mode selects the allocator used at destruction.
This is storage identity, not a Rust provenance or an AllocId. -/
structure NativeBufferOwnership where
  pointer : Nat
  isolated : Bool
  layoutSize : Nat
  layoutAlign : Nat
  deriving DecidableEq, Repr

/-- Source native prepared_alloc_bytes entry, allocated once when a global
address is first assigned, then transferred into its materialized Allocation. -/
structure PreparedGlobalBytes where
  owner : NativeBufferOwnership
  size : Size
  align : Align
  deriving Repr

end Miri.Memory
