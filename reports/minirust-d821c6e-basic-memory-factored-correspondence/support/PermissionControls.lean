import AnnealResearch.MemoryPermissions
import AnnealResearch.PermissionCleanup

/-!
Additional owned controls for the joint memory/permission/cleanup experiment.
The admitted fragment-bearing read and one-past failure use actual memory
kernels, rather than only the decoder. Disjoint-byte cleanup contrasts with
same-byte permission interference.

The mutant discards permission changes ONLY on successful reads. For the same
command and input state, it retains the exact reply/fault/result category and
raw-memory residual; writes are literally unchanged. This pointwise projection
does not assert equality of whole execution observations or completed outputs.
Indeed the full same-byte cleanup has permission UB under the original runner
but reaches its finish policy safely under the mutant. No edge follows UB.

These are controls of the owned flat-tag wrapper. StateWF witnesses concern the
pinned BasicMemory memory domain, not reachability of the permission fixtures
from a Rust program or a complete Tree Borrows initialization algorithm.
-/

namespace AnnealResearch.PermissionControls

open Execution MemoryPermissions PermissionCleanup
open MemoryPermissions.Fixtures

namespace AdmittedInputs

def mintedFragment : MiniRustReference.Frag := ⟨0, 19⟩

def fragmentByte (value : Fin 256) : MiniRustReference.Byte :=
  .init value (some mintedFragment)

def fragmentState (value : Fin 256) : Coupled :=
  ⟨liveMemory (fragmentByte value) (byte value), allCell⟩

def fragmentAfterRead (value : Fin 256) : Coupled :=
  ⟨(fragmentState value).memory,
    BorrowFrame.update allCell (access0 0 .read) .Cell⟩

/-- A real raw load preserves the minted fragment at noncanonical position 19. -/
theorem fragment_raw_read (value : Fin 256) :
    runCoupled (.readRaw pointer0 0 1) (fragmentState value) =
      .ok (.raw [fragmentByte value]) (fragmentAfterRead value) := rfl

/-- A real initialized-u8 load accepts the initialized fragment-bearing cell. -/
theorem fragment_initialized_read (value : Fin 256) :
    runCoupled (.readU8 pointer0 0 1) (fragmentState value) =
      .ok (.number value) (fragmentAfterRead value) := rfl

theorem fragment_memory_WF (value : Fin 256) :
    MiniRustReference.StateWF (fragmentState value).memory := by
  change MiniRustReference.StateWF (liveMemory (fragmentByte value) (byte value))
  apply liveMemory_WF
  · change 0 < 1
    decide
  · exact True.intro

theorem fragment_pointer_WF (value : Fin 256) :
    MiniRustReference.PtrWF (fragmentState value).memory pointer0 :=
  pointer0_WF (fragmentByte value) (byte value)

/-- Static pointer admission allows one-past pointers; a positive-size access
still needs the dynamic bounds check. -/
def onePast : MiniRustReference.Ptr := ⟨18, some 0⟩

theorem onePast_pointer_WF (first second : MiniRustReference.Byte) :
    MiniRustReference.PtrWF (liveMemory first second) onePast := by
  change 18 < MiniRustReference.addressLimit ∧ 0 < 1
  exact ⟨by decide, by decide⟩

/-- Bounds wins over disabled permissions and uninitialized-value checking. -/
theorem onePast_bounds_before_permission :
    runCoupled (.readU8 onePast 0 1) disabledState =
      .ub (.basic .bounds) disabledState := rfl

theorem onePast_admitted_but_access_fails :
    MiniRustReference.StateWF disabledState.memory ∧
    MiniRustReference.PtrWF disabledState.memory onePast ∧
    runCoupled (.readU8 onePast 0 1) disabledState =
      .ub (.basic .bounds) disabledState :=
  ⟨uninit_WF, onePast_pointer_WF .uninit .uninit, onePast_bounds_before_permission⟩

end AdmittedInputs

namespace DisjointCleanup

def access1 (tag : Nat) (kind : BorrowFrame.AccessKind) : BorrowFrame.Access :=
  ⟨⟨0, 1⟩, tag, kind⟩

def program (finish : Finish) : Program :=
  ⟨pointer0, pointer1, pointer1, 1, finish⟩

def afterPayloadRead (value : Fin 256) : Coupled :=
  ⟨(aliasRead0 value).memory,
    BorrowFrame.update (aliasRead0 value).permissions (access1 1 .read) .Unique⟩

def writtenMemory1 (value : Fin 256) : MiniRustReference.State :=
  let bytes : List MiniRustReference.Byte := [byte value]
  let allocation := block (byte value) (byte value)
  let writtenData : Nat → MiniRustReference.Byte := fun index =>
    if 1 ≤ index ∧ index < 1 + bytes.length then
      bytes.getD (index - 1) .uninit
    else allocation.data index
  MiniRustReference.replace (liveMemory (byte value) (byte value)) 0
    { allocation with data := writtenData }

def afterPayloadWrite (value : Fin 256) : Coupled :=
  ⟨writtenMemory1 value,
    BorrowFrame.update (afterPayloadRead value).permissions (access1 1 .write) .Unique⟩

theorem body_freezes_its_byte_only (value : Fin 256) :
    (aliasRead0 value).permissions ⟨0, 0⟩ 1 = .Frozen ∧
    (aliasRead0 value).permissions ⟨0, 1⟩ 1 = .Unique := ⟨rfl, rfl⟩

theorem payload_read (value : Fin 256) :
    runCoupled (.readU8 pointer1 1 1) (aliasRead0 value) =
      .ok (.number value) (afterPayloadRead value) := rfl

theorem payload_write (value : Fin 256) :
    runCoupled (.writeRaw pointer1 1 1 (byte value)) (afterPayloadRead value) =
      .ok .unit (afterPayloadWrite value) := rfl

theorem actual_payload_after_write (value : Fin 256) :
    MiniRustReference.load (afterPayloadWrite value).memory pointer1 1 1 =
      .ok ([byte value], (afterPayloadWrite value).memory) := rfl

/-- All finish policies reach their actual seven-edge finish configuration. -/
theorem cleanup_run (value : Fin 256) (finish : Finish) :
    run runCoupled (program finish) 7 (initial (aliasing value)) =
      some (finished (program finish) (afterPayloadWrite value) [byte value] value) :=
  run_good runCoupled (program finish) (alias_raw_read value)
    (payload_read value) (payload_write value)

theorem cleanup_safe (value : Fin 256) (finish : Finish) :
    NoUB (SourceStep (program finish)) Bad (initial (aliasing value)) :=
  good_cleanup_safe runCoupled (program finish) (alias_raw_read value)
    (payload_read value) (payload_write value)

theorem cleanup_reaches_finish (value : Fin 256) (finish : Finish) :
    Reach (SourceStep (program finish)) (initial (aliasing value))
      (finished (program finish) (afterPayloadWrite value) [byte value] value) ∧
    (finished (program finish) (afterPayloadWrite value) [byte value] value).owed = false ∧
    (finished (program finish) (afterPayloadWrite value) [byte value] value).cost = 7 :=
  ⟨run_reach runCoupled (program finish) (cleanup_run value finish), rfl, rfl⟩

theorem cleanup_has_actual_infinite_continuation (value : Fin 256) :
    ∃ states : Nat → Config Coupled,
      states 0 = finished (program .spin) (afterPayloadWrite value) [byte value] value ∧
      ∀ n, SourceStep (program .spin) (states n) (states (n + 1)) :=
  actual_infinite_continuation runCoupled (program .spin)
    (finished (program .spin) (afterPayloadWrite value) [byte value] value) rfl

end DisjointCleanup

namespace ReadMutation

/-- Deliberately wrong: discard only successful read permission changes.
Failure residuals, including post-read initialization failure, remain untouched. -/
def discardSuccessfulReadPermissions (before : Coupled) : Result Reply Coupled → Result Reply Coupled
  | .ok reply after => .ok reply { after with permissions := before.permissions }
  | .ub fault after => .ub fault after
  | .unsupported after => .unsupported after
  | .noChoice after => .noChoice after

def runner (command : Command) (state : Coupled) : Result Reply Coupled :=
  match command with
  | .readRaw _ _ _ => discardSuccessfulReadPermissions state (runCoupled command state)
  | .readU8 _ _ _ => discardSuccessfulReadPermissions state (runCoupled command state)
  | .writeRaw _ _ _ _ => runCoupled command state

/-- This projection retains reply bytes/numbers, all result/fault categories,
and raw memory, while intentionally omitting the permission component. -/
theorem discarded_read_memory_projection (before : Coupled) (answer : Result Reply Coupled) :
    resultMap (fun state : Coupled => state.memory)
        (discardSuccessfulReadPermissions before answer) =
      resultMap (fun state : Coupled => state.memory) answer := by
  cases answer <;> rfl

/-- A same-input command equation, NOT whole-program output equivalence. -/
theorem same_command_memory_and_result (command : Command) (state : Coupled) :
    resultMap (fun after : Coupled => after.memory) (runner command state) =
      resultMap (fun after : Coupled => after.memory) (runCoupled command state) := by
  cases command with
  | readRaw pointer tag align =>
      exact discarded_read_memory_projection state (runCoupled (.readRaw pointer tag align) state)
  | readU8 pointer tag align =>
      exact discarded_read_memory_projection state (runCoupled (.readU8 pointer tag align) state)
  | writeRaw pointer tag align value => rfl

theorem failure_residual_is_not_discarded (before after : Coupled) (fault : Fault) :
    discardSuccessfulReadPermissions before (.ub fault after) = .ub fault after := rfl

theorem writes_are_unchanged (state : Coupled) (pointer : MiniRustReference.Ptr)
    (tag align : Nat) (value : MiniRustReference.Byte) :
    runner (.writeRaw pointer tag align value) state =
      runCoupled (.writeRaw pointer tag align value) state := rfl

def program (finish : Finish) : Program :=
  ⟨pointer0, pointer0, pointer0, 1, finish⟩

def afterWrite (value : Fin 256) : Coupled :=
  ⟨writtenMemory value value,
    BorrowFrame.update aliasPermissions (access0 1 .write) .Unique⟩

theorem body_read_discards_freezing (value : Fin 256) :
    runner (.readRaw pointer0 0 1) (aliasing value) =
      .ok (.raw [byte value]) (aliasing value) := rfl

theorem payload_read_discards_freezing (value : Fin 256) :
    runner (.readU8 pointer0 1 1) (aliasing value) =
      .ok (.number value) (aliasing value) := rfl

theorem payload_write_succeeds (value : Fin 256) :
    runner (.writeRaw pointer0 1 1 (byte value)) (aliasing value) =
      .ok .unit (afterWrite value) := rfl

theorem original_cleanup_fails (value : Fin 256) (finish : Finish) :
    run runCoupled (program finish) 6 (initial (aliasing value)) =
      some (writeFailed (aliasRead1 value) [byte value] value (.permission .localWriteFrozen)) ∧
    ¬ NoUB (Step runCoupled (program finish)) Bad (initial (aliasing value)) :=
  ⟨run_write_failure runCoupled (program finish) (alias_raw_read value)
      (alias_typed_read value) (alias_write_fails value value),
    write_failure_not_safe runCoupled (program finish) (alias_raw_read value)
      (alias_typed_read value) (alias_write_fails value value)⟩

theorem original_bad_has_no_continuation (value : Fin 256) (finish : Finish) :
    next runCoupled (program finish)
      (writeFailed (aliasRead1 value) [byte value] value (.permission .localWriteFrozen)) = none := rfl

theorem mutant_cleanup_run (value : Fin 256) (finish : Finish) :
    run runner (program finish) 7 (initial (aliasing value)) =
      some (finished (program finish) (afterWrite value) [byte value] value) :=
  run_good runner (program finish) (body_read_discards_freezing value)
    (payload_read_discards_freezing value) (payload_write_succeeds value)

theorem mutant_cleanup_safe (value : Fin 256) (finish : Finish) :
    NoUB (Step runner (program finish)) Bad (initial (aliasing value)) :=
  good_cleanup_safe runner (program finish) (body_read_discards_freezing value)
    (payload_read_discards_freezing value) (payload_write_succeeds value)

/-- The mutation invalidates the source-safety inference for the complete
cleanup client, despite preserving the same-input per-command memory projection. -/
theorem mutation_invalidates_cleanup_safety (value : Fin 256) (finish : Finish) :
    ¬ NoUB (Step runCoupled (program finish)) Bad (initial (aliasing value)) ∧
    NoUB (Step runner (program finish)) Bad (initial (aliasing value)) ∧
    Reach (Step runner (program finish)) (initial (aliasing value))
      (finished (program finish) (afterWrite value) [byte value] value) ∧
    (finished (program finish) (afterWrite value) [byte value] value).cost = 7 :=
  ⟨(original_cleanup_fails value finish).2, mutant_cleanup_safe value finish,
    run_reach runner (program finish) (mutant_cleanup_run value finish), rfl⟩

theorem mutant_has_actual_infinite_continuation (value : Fin 256) :
    ∃ states : Nat → Config Coupled,
      states 0 = finished (program .spin) (afterWrite value) [byte value] value ∧
      ∀ n, Step runner (program .spin) (states n) (states (n + 1)) :=
  actual_infinite_continuation runner (program .spin)
    (finished (program .spin) (afterWrite value) [byte value] value) rfl

end ReadMutation

#print axioms AdmittedInputs.fragment_raw_read
#print axioms AdmittedInputs.fragment_initialized_read
#print axioms AdmittedInputs.fragment_memory_WF
#print axioms AdmittedInputs.fragment_pointer_WF
#print axioms AdmittedInputs.onePast_pointer_WF
#print axioms AdmittedInputs.onePast_bounds_before_permission
#print axioms AdmittedInputs.onePast_admitted_but_access_fails
#print axioms DisjointCleanup.body_freezes_its_byte_only
#print axioms DisjointCleanup.payload_read
#print axioms DisjointCleanup.payload_write
#print axioms DisjointCleanup.actual_payload_after_write
#print axioms DisjointCleanup.cleanup_run
#print axioms DisjointCleanup.cleanup_safe
#print axioms DisjointCleanup.cleanup_reaches_finish
#print axioms DisjointCleanup.cleanup_has_actual_infinite_continuation
#print axioms ReadMutation.discarded_read_memory_projection
#print axioms ReadMutation.same_command_memory_and_result
#print axioms ReadMutation.failure_residual_is_not_discarded
#print axioms ReadMutation.writes_are_unchanged
#print axioms ReadMutation.body_read_discards_freezing
#print axioms ReadMutation.payload_read_discards_freezing
#print axioms ReadMutation.payload_write_succeeds
#print axioms ReadMutation.original_cleanup_fails
#print axioms ReadMutation.original_bad_has_no_continuation
#print axioms ReadMutation.mutant_cleanup_run
#print axioms ReadMutation.mutant_cleanup_safe
#print axioms ReadMutation.mutation_invalidates_cleanup_safety
#print axioms ReadMutation.mutant_has_actual_infinite_continuation

end AnnealResearch.PermissionControls
