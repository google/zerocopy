import Miri.Concurrency.Sync

open Miri.Concurrency

/-- The WriterLock source operation, with the no-race-handler clock hook,
establishes writer ownership for the active thread. -/
theorem rwlock_writer_lock_none_contract (global : GlobalState)
    (threads : ThreadManager) :
    let result := RwLockState.writerLock {} global threads .none
    result.syncState.writer = some threads.activeThread ∧
      result.syncState.readers = [] ∧ result.outcomeIsOk := by
  unfold RwLockState.writerLock
  simp [RwLockState.isLocked, SyncTransition.outcomeIsOk]

/-- The mutex callback bridge is a pending source action until callback
completion; a transition with that action cannot satisfy the local completed
predicate. -/
theorem mutex_callback_is_pending (state : MutexState) (global : GlobalState)
    (threads : ThreadManager) (request : SyncCallbackRequest)
    (hcallback : (MutexState.unlock state global threads .none).callback = some request) :
    (MutexState.unlock state global threads .none).hasPendingWork = true := by
  simp [SyncTransition.hasPendingWork, hcallback]

#print axioms rwlock_writer_lock_none_contract
#print axioms mutex_callback_is_pending
