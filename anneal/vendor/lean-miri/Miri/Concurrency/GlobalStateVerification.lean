import Miri.Concurrency.GlobalState

namespace Miri.Concurrency.GlobalStateVerification

/-- When Miri has not enabled multithreaded tracking, its synchronization
wrapper skips the fence operation and leaves all clocks and SC state intact. -/
theorem single_thread_fence_is_noop (state : GlobalState) (threads : ThreadManager)
    (ordering : AtomicFenceOrd) (h : state.multiThreaded = false) :
    state.atomicFence threads ordering = .ok state := by
  simp [GlobalState.atomicFence, h]
  rfl

/-- The source synchronized-operation hook skips both its callback and clock
updates when Miri has not entered multithreaded mode. -/
theorem single_thread_sync_operation_is_skipped {External Error Value : Type}
    (state : GlobalState) (threads : ThreadManager) (external : External)
    (body : VectorIdx → ThreadClockSet → External →
      SyncOperationBodyResult External Error Value)
    (h : state.multiThreaded = false) :
    let result := state.maybePerformSyncOperation threads external body
    result.global = state ∧ result.external = external ∧ result.outcome = .ok none := by
  simp [GlobalState.maybePerformSyncOperation, h]

#print axioms single_thread_fence_is_noop
#print axioms single_thread_sync_operation_is_skipped

end Miri.Concurrency.GlobalStateVerification
