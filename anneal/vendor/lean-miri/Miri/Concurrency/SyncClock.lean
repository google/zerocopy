import Miri.Concurrency.GlobalState

/-! The actual clock-state boundary used by source synchronization operations.
Legacy pure transitions retain GlobalState; canonical runtime transitions carry
Option GlobalState. No absent-state implementation constructs a clock.
release_clock exposes its source callback point before incrementing the clock.
-/
namespace Miri.Concurrency
inductive SyncClockError where
  | missingGlobal
  | global (error : GlobalStateError)
  deriving Repr

class SyncClockState (G : Type) where
  acquire : G → ThreadManager → VClock → Except SyncClockError G
  /-- First failure is before the source callback; the nested result is after
  the callback and retains its effects when clock increment fails. -/
  prepareRelease : G → ThreadManager → Except SyncClockError (VClock × Except SyncClockError G)

private def acquireGlobal (g : GlobalState) (threads : ThreadManager) (clock : VClock) :
    Except SyncClockError GlobalState :=
  g.acquireClock threads clock |>.mapError .global
private def releaseGlobal (g : GlobalState) (threads : ThreadManager) :
    Except SyncClockError (VClock × Except SyncClockError GlobalState) := do
  let (_,current) ← g.activeThreadState threads |>.mapError .global
  let finish := (g.releaseClock threads).map Prod.fst |>.mapError .global
  pure (current.clock,finish)

instance : SyncClockState GlobalState where
  acquire := acquireGlobal
  prepareRelease := releaseGlobal

instance : SyncClockState (Option GlobalState) where
  acquire := fun g threads clock => do
    let some g := g | throw .missingGlobal
    some <$> acquireGlobal g threads clock
  prepareRelease := fun g threads => do
    let some g := g | throw .missingGlobal
    let (snapshot,finish) ← releaseGlobal g threads
    pure (snapshot,some <$> finish)

/-- An absent clock is a representation error if a VClock operation is
requested. Source None-mode skips the operation before reaching this boundary. -/
theorem absent_acquire (threads : ThreadManager) (clock : VClock) :
    SyncClockState.acquire (none : Option GlobalState) threads clock = .error .missingGlobal := rfl

theorem absent_release (threads : ThreadManager) :
    SyncClockState.prepareRelease (none : Option GlobalState) threads = .error .missingGlobal := rfl
end Miri.Concurrency
