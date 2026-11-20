import Miri.Concurrency.WeakMemory

namespace Miri.Concurrency.WeakMemoryVerification

/-- Every store transition retains the pinned implementation's capacity bound. -/
theorem store_impl_preserves_limit (buffer : StoreBuffer Nat) (value : Nat)
    (index : VectorIdx) (clock : VClock) (isSeqCst : Bool) (syncClock : VClock) :
    (StoreBuffer.storeImpl buffer value index clock isSeqCst syncClock).newer.length <
      STORE_BUFFER_LIMIT := by
  exact (StoreBuffer.storeImpl buffer value index clock isSeqCst syncClock).bounded

/-- The source choice relation never gets stuck: the initial/latest entry is
included even when it is the first element that closes the inclusive prefix. -/
theorem source_fetch_has_candidate (buffer : StoreBuffer Nat) (isSeqCst : Bool)
    (clocks : ThreadClockSet) : StoreBuffer.fetchChoices buffer isSeqCst clocks ≠ [] :=
  StoreBuffer.fetchChoices_nonempty buffer isSeqCst clocks

#print axioms source_fetch_has_candidate

end Miri.Concurrency.WeakMemoryVerification
