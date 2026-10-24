import AnnealResearch.ReferenceInvariants
import AnnealResearch.MemoryPermissions
import AnnealResearch.PermissionCleanup

/-!
Noncircular structural admission for the owned joint kernel and cleanup wrapper.
MemoryWF is exactly the existing reference memory's StateWF. The flat permission
store is a total function into its enum, so this file invents no additional
joint borrowing invariant. No claim about full Tree Borrows or Rust follows.

All result categories retain a residual state. Preservation covers success, UB,
unsupported, and noChoice rather than filtering failed accesses. The premises
contain no NoUB, access success, live/in-bounds operand, or correctly aligned
access assumption. A written provenance-bearing byte must refer to a minted ID;
numeric bytes without fragments and uninitialized bytes satisfy that structural
condition automatically. Initialization and permission safety remain separate.
-/

namespace AnnealResearch.MemoryPermissionInvariants

open MemoryPermissions

def MemoryWF (state : Coupled) : Prop := MiniRustReference.StateWF state.memory

def FactoredMemoryWF (state : Factored) : Prop := MemoryWF (reify state)

def residual {Value State : Type} : Result Value State → State
  | .ok _ state => state
  | .ub _ state => state
  | .unsupported state => state
  | .noChoice state => state

def ResidualHolds {Value State : Type} (property : State → Prop)
    (answer : Result Value State) : Prop := property (residual answer)

theorem residual_map {Value S T : Type} (f : S → T) (answer : Result Value S) :
    residual (resultMap f answer) = f (residual answer) := by
  cases answer <;> rfl

/-- This is a representation-only admission predicate. It puts no restrictions
on a pointer, access alignment, live allocation, initialized read, or permission. -/
def CommandWF (state : Coupled) : Command → Prop
  | .readRaw _ _ _ | .readU8 _ _ _ => True
  | .writeRaw _ _ _ byte => MiniRustReference.ByteWF state.memory byte

theorem singleton_bytesWF {memory : MiniRustReference.State} {byte : MiniRustReference.Byte}
    (known : MiniRustReference.ByteWF memory byte) :
    MiniRustReference.BytesWF memory [byte] := by
  intro index inside
  have zero : index = 0 := by
    simp only [List.length_singleton] at inside
    omega
  subst index
  exact known

/-- A raw BasicMemory load does not change memory even when its requested
access would require additional permission effects in the joint kernel. -/
theorem load_success_memory {memory after : MiniRustReference.State}
    {pointer : MiniRustReference.Ptr} {bytes : List MiniRustReference.Byte}
    {length alignment : Nat}
    (success : MiniRustReference.load memory pointer length alignment = .ok (bytes, after)) :
    after = memory := by
  by_cases zeroAlign : alignment = 0
  · simp [MiniRustReference.load, zeroAlign] at success
  · by_cases misaligned : pointer.addr % alignment ≠ 0
    · simp [MiniRustReference.load, zeroAlign, misaligned] at success
    · simp only [MiniRustReference.load, ite_eq_right zeroAlign,
        ite_eq_right misaligned] at success
      cases checked : MiniRustReference.checkPtr memory pointer length with
      | ub reason => simp [checked] at success
      | unsupported => simp [checked] at success
      | noChoice => simp [checked] at success
      | ok span =>
        cases span with
        | none =>
          simp only [checked] at success
          exact (congrArg Prod.snd (MiniRustReference.Result.ok.inj success)).symm
        | some span =>
          simp only [checked] at success
          exact (congrArg Prod.snd (MiniRustReference.Result.ok.inj success)).symm

/-- The permission store may change, including on later initialized-value UB;
the underlying memory of every raw-read residual remains exactly the input. -/
theorem read_residual_memory (state : Coupled) (pointer : MiniRustReference.Ptr)
    (tag alignment : Nat) :
    (residual (readCoupled state pointer tag alignment)).memory = state.memory := by
  unfold readCoupled
  cases loaded : MiniRustReference.load state.memory pointer 1 alignment with
  | ub reason => rfl
  | unsupported => rfl
  | noChoice => rfl
  | ok pair =>
    rcases pair with ⟨bytes, memory⟩
    have unchanged : memory = state.memory := load_success_memory loaded
    subst memory
    cases checked : MiniRustReference.checkPtr state.memory pointer 1 with
    | ub reason => rfl
    | unsupported => rfl
    | noChoice => rfl
    | ok span =>
      cases span with
      | none => rfl
      | some span =>
        cases permitted : permissionStep state.permissions span.id span.offset tag .read <;>
          simp only [permitted, residual]

theorem read_preserves_MemoryWF (state : Coupled) (pointer : MiniRustReference.Ptr)
    (tag alignment : Nat) (wf : MemoryWF state) :
    ResidualHolds MemoryWF (readCoupled state pointer tag alignment) := by
  change MiniRustReference.StateWF (residual (readCoupled state pointer tag alignment)).memory
  rw [read_residual_memory]
  exact wf

theorem decode_preserves_residual {S : Type} (answer : Result Reply S) :
    residual (decodeInitialized answer) = residual answer := by
  cases answer with
  | ok reply state =>
    cases reply with
    | raw bytes =>
      cases bytes with
      | nil => rfl
      | cons first rest =>
        cases rest with
        | nil => cases first <;> rfl
        | cons second rest => cases first <;> rfl
    | number value => rfl
    | unit => rfl
  | ub fault state => rfl
  | unsupported state => rfl
  | noChoice state => rfl

theorem decode_preserves_property {S : Type} (property : S → Prop)
    (answer : Result Reply S) (known : ResidualHolds property answer) :
    ResidualHolds property (decodeInitialized answer) := by
  unfold ResidualHolds
  rw [decode_preserves_residual]
  exact known

theorem write_preserves_MemoryWF (state : Coupled) (pointer : MiniRustReference.Ptr)
    (tag alignment : Nat) (byte : MiniRustReference.Byte)
    (wf : MemoryWF state) (byteWF : MiniRustReference.ByteWF state.memory byte) :
    ResidualHolds MemoryWF (writeCoupled state pointer tag alignment byte) := by
  unfold ResidualHolds writeCoupled
  cases stored : MiniRustReference.store state.memory pointer [byte] alignment with
  | ub reason => exact wf
  | unsupported => exact wf
  | noChoice => exact wf
  | ok memory =>
    have afterWF : MiniRustReference.StateWF memory :=
      MiniRustReference.store_preserves_StateWF wf (singleton_bytesWF byteWF) stored
    cases checked : MiniRustReference.checkPtr state.memory pointer 1 with
    | ub reason => exact wf
    | unsupported => exact wf
    | noChoice => exact wf
    | ok span =>
      cases span with
      | none => exact wf
      | some span =>
        cases permitted : permissionStep state.permissions span.id span.offset tag .write with
        | error reason => simpa only [permitted, residual, MemoryWF] using wf
        | ok permissions => simpa only [permitted, residual, MemoryWF] using afterWF

/-- The written-byte premise is the entire CommandWF condition; it is not an
assumption that the command succeeds or is safe. -/
theorem runCoupled_preserves_MemoryWF (state : Coupled) (command : Command)
    (wf : MemoryWF state) (admitted : CommandWF state command) :
    ResidualHolds MemoryWF (runCoupled command state) := by
  cases command with
  | readRaw pointer tag alignment => exact read_preserves_MemoryWF state pointer tag alignment wf
  | readU8 pointer tag alignment =>
    exact decode_preserves_property MemoryWF _
      (read_preserves_MemoryWF state pointer tag alignment wf)
  | writeRaw pointer tag alignment byte =>
    exact write_preserves_MemoryWF state pointer tag alignment byte wf admitted

theorem runFactored_preserves_MemoryWF (state : Factored) (command : Command)
    (wf : FactoredMemoryWF state) (admitted : CommandWF (reify state) command) :
    ResidualHolds FactoredMemoryWF (runFactored command state) := by
  have known := runCoupled_preserves_MemoryWF (reify state) command wf admitted
  rw [run_reify] at known
  simpa only [ResidualHolds, residual_map, FactoredMemoryWF] using known

open PermissionCleanup Execution

/-- Generic wrapper result handling keeps the actual residual memory property
on both success and errors. noChoice supplies no wrapper successor. -/
theorem handle_preserves_property {S : Type} (property : S → Prop)
    (before : Config S) (continuation : Reply → Phase × PermissionCleanup.Event)
    (answer : Result Reply S) (after : Config S)
    (known : ResidualHolds property answer)
    (handled : handle before continuation answer = some after) : property after.memory := by
  cases answer with
  | ok reply memory =>
    have same : tickWith before memory (continuation reply).1 (continuation reply).2 = after :=
      Option.some.inj handled
    rw [← same]
    exact known
  | ub fault memory =>
    have same : tickWith before memory (.bad fault) (.failed fault) = after :=
      Option.some.inj handled
    rw [← same]
    exact known
  | unsupported memory =>
    have same : tickWith before memory .unsupported .unsupported = after := Option.some.inj handled
    rw [← same]
    exact known
  | noChoice memory => simp [handle] at handled

/-- No pointer/liveness/access-success premise is used. The wrapper writes only
the numeric, no-fragment byte returned by its typed read, so ByteWF is automatic. -/
theorem cleanup_step_preserves_MemoryWF (program : Program) {before after : Config Coupled}
    (wf : MemoryWF before.memory) (edge : SourceStep program before after) :
    MemoryWF after.memory := by
  change next runCoupled program before = some after at edge
  cases phase : before.phase with
  | body =>
    exact handle_preserves_property MemoryWF before bodyContinuation
      (runCoupled (.readRaw program.bodyPointer 0 program.alignment) before.memory) after
      (runCoupled_preserves_MemoryWF before.memory _ wf True.intro)
      (by simpa only [next, phase] using edge)
  | test =>
    have same : tick before (if before.owed then .consume else .finish) (.tested before.owed) = after :=
      Option.some.inj (by simpa only [next, phase] using edge)
    rw [← same]
    exact wf
  | consume =>
    have same : ({ tick before .invoke .consumed with owed := false } : Config Coupled) = after :=
      Option.some.inj (by simpa only [next, phase] using edge)
    rw [← same]
    exact wf
  | invoke =>
    have same : tick before .readPayload .called = after :=
      Option.some.inj (by simpa only [next, phase] using edge)
    rw [← same]
    exact wf
  | readPayload =>
    exact handle_preserves_property MemoryWF before readContinuation
      (runCoupled (.readU8 program.payloadPointer 1 program.alignment) before.memory) after
      (runCoupled_preserves_MemoryWF before.memory _ wf True.intro)
      (by simpa only [next, phase] using edge)
  | writePayload value =>
    exact handle_preserves_property MemoryWF before (writeContinuation value)
      (runCoupled (.writeRaw program.writePointer 1 program.alignment (.init value none)) before.memory) after
      (runCoupled_preserves_MemoryWF before.memory _ wf True.intro)
      (by simpa only [next, phase] using edge)
  | finish =>
    have same : tick before (finishControl program.finish).1 (finishControl program.finish).2 = after :=
      Option.some.inj (by simpa only [next, phase] using edge)
    rw [← same]
    exact wf
  | spin =>
    have same : tick before .spin .spinning = after :=
      Option.some.inj (by simpa only [next, phase] using edge)
    rw [← same]
    exact wf
  | done => simp [next, phase] at edge
  | unwound => simp [next, phase] at edge
  | bad fault => simp [next, phase] at edge
  | unsupported => simp [next, phase] at edge

theorem cleanup_reachable_MemoryWF (program : Program) {before after : Config Coupled}
    (wf : MemoryWF before.memory) (path : Reach (SourceStep program) before after) :
    MemoryWF after.memory :=
  invariant_reachable (Step := SourceStep program)
    (Invariant := fun cfg : Config Coupled => MemoryWF cfg.memory) wf
    (fun {s t} known edge =>
      cleanup_step_preserves_MemoryWF program (before := s) (after := t) known edge) path

theorem factored_cleanup_reachable_MemoryWF (program : Program) {before after : Config Factored}
    (wf : FactoredMemoryWF before.memory) (path : Reach (TargetStep program) before after) :
    FactoredMemoryWF after.memory := by
  have sourcePath := PermissionCleanup.map_reach reify runCoupled runFactored run_reify program path
  exact cleanup_reachable_MemoryWF program
    (before := mapCfg reify before) (after := mapCfg reify after) wf sourcePath

/-- Structural admission is compatible with an actual permission-UB prefix. -/
theorem admitted_aliasing_cleanup_is_unsafe (value : Fin 256) :
    MemoryWF (Fixtures.aliasing value) ∧
    ¬ NoUB (SourceStep (PermissionCleanup.Concrete.program .normal)) Bad
      (initial (Fixtures.aliasing value)) :=
  ⟨Fixtures.aliasing_WF value, (PermissionCleanup.Concrete.permission_only_write_failure value).2⟩

/-- StateWF admits uninitialized bytes; owed=true does not establish validity. -/
theorem admitted_uninitialized_cleanup_is_unsafe :
    MemoryWF Fixtures.uninitState ∧
    ¬ NoUB (SourceStep (PermissionCleanup.Concrete.program .normal)) Bad (initial Fixtures.uninitState) :=
  ⟨Fixtures.uninit_WF, PermissionCleanup.Concrete.uninitialized_cleanup_failure.2⟩

/-- Preservation does not remove the unsafe state: the actual reached UB
configuration still satisfies the same structural invariant. -/
theorem aliasing_bad_residual_is_MemoryWF (value : Fin 256) :
    MemoryWF (writeFailed (Fixtures.aliasRead1 value) [Fixtures.byte value] value
      (.permission .localWriteFrozen)).memory :=
  cleanup_reachable_MemoryWF (PermissionCleanup.Concrete.program .normal)
    (before := initial (Fixtures.aliasing value))
    (after := writeFailed (Fixtures.aliasRead1 value) [Fixtures.byte value] value
      (.permission .localWriteFrozen))
    (Fixtures.aliasing_WF value)
    (run_reach runCoupled (PermissionCleanup.Concrete.program .normal)
      (PermissionCleanup.Concrete.permission_only_write_failure value).1)

/- Optional exclusion of unsupported needs separate pointer/alignment admission.
This bounded module deliberately proves structural residual preservation for
every pointer/alignment instead. It does not identify unsupported with UB or an
accepted stop, and its invariant is not a type/initialization/permission theorem.
-/

#print axioms load_success_memory
#print axioms read_residual_memory
#print axioms read_preserves_MemoryWF
#print axioms decode_preserves_residual
#print axioms write_preserves_MemoryWF
#print axioms runCoupled_preserves_MemoryWF
#print axioms runFactored_preserves_MemoryWF
#print axioms handle_preserves_property
#print axioms cleanup_step_preserves_MemoryWF
#print axioms cleanup_reachable_MemoryWF
#print axioms factored_cleanup_reachable_MemoryWF
#print axioms admitted_aliasing_cleanup_is_unsafe
#print axioms admitted_uninitialized_cleanup_is_unsafe
#print axioms aliasing_bad_residual_is_MemoryWF

end AnnealResearch.MemoryPermissionInvariants
