import Miri.Concurrency.DataRace

namespace Miri.Concurrency.Verification

/-- The release-fence transition copies the current clock and preserves the
remaining per-thread synchronization metadata. -/
theorem release_fence_preserves_metadata (before : ThreadClockSet) :
    let after := ThreadClockSet.applyReleaseFence before
    after.fenceRelease = before.clock ∧ after.clock = before.clock ∧
      after.fenceAcquire = before.fenceAcquire ∧
      after.writeSeqCst = before.writeSeqCst ∧ after.readSeqCst = before.readSeqCst := by
  simp [ThreadClockSet.applyReleaseFence]

/-- The acquire-fence transition joins its pending clock and preserves the
other synchronization metadata. -/
theorem acquire_fence_preserves_metadata (before : ThreadClockSet) :
    let after := ThreadClockSet.applyAcquireFence before
    after.clock = before.clock.join before.fenceAcquire ∧
      after.fenceAcquire = before.fenceAcquire ∧ after.fenceRelease = before.fenceRelease := by
  simp [ThreadClockSet.applyAcquireFence]

/-- Incompatible concurrent atomic sizes reject a write access. -/
theorem atomic_access_rejects_incompatible_write
    (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (oldAtomic : AtomicMemoryCellClocks) (newSize : ByteSize)
    (hOldSize : oldAtomic.size ≠ some newSize)
    (hReads : oldAtomic.readVector.le thread.clock = false)
    (hWrites : oldAtomic.writeVector.le thread.clock = false)
    (hCell : cell.atomicOps = some oldAtomic) :
    cell.atomicAccess thread newSize true = .error .race := by
  simp [MemoryCellClocks.atomicAccess, hCell, hOldSize, hReads, hWrites]

end Miri.Concurrency.Verification
