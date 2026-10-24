import AnnealResearch.MemoryPermissions
import AnnealResearch.PrefixTransfer

/-!
Owned single-obligation cleanup over the joint memory/permission kernel.
The coupled and factored subjects share this explicit wrapper/control syntax;
the correspondence is kernel composition/congruence, not independent Rust drop
lowering. The bytes read by the destructor are actual kernel bytes. `owed` is
only a cleanup obligation and never a premise that those bytes are initialized.

Every wrapper edge costs one logical unit, including testing, consuming, call
entry, a failing kernel call, and completion. This is neither elapsed time nor
an instruction count. Failure events retain the kernel's residual joint state,
the current obligation bit, and every prior event. noChoice has no successor;
unsupported is separate from UB. These are bounded owned-model statements, not
full Drop, full Tree Borrows, MiniRust-machine, or Rust adequacy claims.
-/

namespace AnnealResearch.PermissionCleanup

open MemoryPermissions Execution PrefixTransfer

inductive Finish where
  | normal | unwind | spin

structure Program where
  bodyPointer : MiniRustReference.Ptr
  payloadPointer : MiniRustReference.Ptr
  writePointer : MiniRustReference.Ptr
  alignment : Nat := 1
  finish : Finish := .normal

inductive Phase where
  | body | test | consume | invoke | readPayload
  | writePayload (value : Fin 256)
  | finish | spin | done | unwound
  | bad (fault : Fault)
  | unsupported

inductive Event where
  | bodyRead (bytes : List MiniRustReference.Byte)
  | tested (owed : Bool)
  | consumed | called
  | payloadRead (value : Fin 256)
  | payloadWritten (value : Fin 256)
  | normal | unwind | enteredSpin | spinning
  | failed (fault : Fault)
  | unsupported | unexpectedReply

structure Config (S : Type) where
  memory : S
  owed : Bool
  phase : Phase
  events : List Event
  cost : Nat

def initial {S : Type} (memory : S) : Config S := ⟨memory, true, .body, [], 0⟩

def tickWith {S : Type} (cfg : Config S) (memory : S) (phase : Phase)
    (event : Event) : Config S :=
  ⟨memory, cfg.owed, phase, cfg.events ++ [event], cfg.cost + 1⟩

def tick {S : Type} (cfg : Config S) (phase : Phase) (event : Event) : Config S :=
  tickWith cfg cfg.memory phase event

def bodyContinuation : Reply → Phase × Event
  | .raw bytes => (.test, .bodyRead bytes)
  | _ => (.unsupported, .unexpectedReply)

def readContinuation : Reply → Phase × Event
  | .number value => (.writePayload value, .payloadRead value)
  | _ => (.unsupported, .unexpectedReply)

def writeContinuation (value : Fin 256) : Reply → Phase × Event
  | .unit => (.finish, .payloadWritten value)
  | _ => (.unsupported, .unexpectedReply)

def handle {S : Type} (cfg : Config S) (continuation : Reply → Phase × Event) :
    Result Reply S → Option (Config S)
  | .ok reply memory =>
      some (tickWith cfg memory (continuation reply).1 (continuation reply).2)
  | .ub fault memory => some (tickWith cfg memory (.bad fault) (.failed fault))
  | .unsupported memory => some (tickWith cfg memory .unsupported .unsupported)
  | .noChoice _ => none

def finishControl : Finish → Phase × Event
  | .normal => (.done, .normal)
  | .unwind => (.unwound, .unwind)
  | .spin => (.spin, .enteredSpin)

/-- Tag 0 performs the raw body read; tag 1 performs the destructor's typed read
and write. Clearing the cleanup obligation leaves memory unchanged. -/
def next {S : Type} (runner : Command → S → Result Reply S)
    (program : Program) (cfg : Config S) : Option (Config S) :=
  match cfg.phase with
  | .body => handle cfg bodyContinuation
      (runner (.readRaw program.bodyPointer 0 program.alignment) cfg.memory)
  | .test => some (tick cfg (if cfg.owed then .consume else .finish) (.tested cfg.owed))
  | .consume => some { tick cfg .invoke .consumed with owed := false }
  | .invoke => some (tick cfg .readPayload .called)
  | .readPayload => handle cfg readContinuation
      (runner (.readU8 program.payloadPointer 1 program.alignment) cfg.memory)
  | .writePayload value => handle cfg (writeContinuation value)
      (runner (.writeRaw program.writePointer 1 program.alignment
        (.init value none)) cfg.memory)
  | .finish => some (tick cfg (finishControl program.finish).1 (finishControl program.finish).2)
  | .spin => some (tick cfg .spin .spinning)
  | .done | .unwound | .bad _ | .unsupported => none

def Step {S : Type} (runner : Command → S → Result Reply S)
    (program : Program) (before after : Config S) : Prop :=
  next runner program before = some after

def Bad {S : Type} (cfg : Config S) : Prop :=
  match cfg.phase with | .bad _ => True | _ => False

def mapCfg {S T : Type} (f : T → S) (cfg : Config T) : Config S :=
  ⟨f cfg.memory, cfg.owed, cfg.phase, cfg.events, cfg.cost⟩

theorem map_observations {S T : Type} (f : T → S) (cfg : Config T) :
    (mapCfg f cfg).owed = cfg.owed ∧ (mapCfg f cfg).phase = cfg.phase ∧
    (mapCfg f cfg).events = cfg.events ∧ (mapCfg f cfg).cost = cfg.cost :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem handle_commutes {S T : Type} (f : T → S) (cfg : Config T)
    (continuation : Reply → Phase × Event) (answer : Result Reply T) :
    handle (mapCfg f cfg) continuation (resultMap f answer) =
      (handle cfg continuation answer).map (mapCfg f) := by
  cases answer <;> rfl

section Correspondence

variable {S T : Type} (f : T → S)
variable (sourceRunner : Command → S → Result Reply S)
variable (targetRunner : Command → T → Result Reply T)
variable (commutes : ∀ command memory,
  sourceRunner command (f memory) = resultMap f (targetRunner command memory))
variable (program : Program)
include commutes

theorem next_commutes (cfg : Config T) :
    next sourceRunner program (mapCfg f cfg) =
      (next targetRunner program cfg).map (mapCfg f) := by
  cases cfg with
  | mk memory owed phase events cost =>
    cases phase with
    | body =>
      simp only [next, mapCfg]
      rw [commutes]
      simpa only [mapCfg] using
        handle_commutes f (⟨memory, owed, .body, events, cost⟩ : Config T)
          bodyContinuation
          (targetRunner (.readRaw program.bodyPointer 0 program.alignment) memory)
    | test => cases owed <;> rfl
    | consume => rfl
    | invoke => rfl
    | readPayload =>
      simp only [next, mapCfg]
      rw [commutes]
      simpa only [mapCfg] using
        handle_commutes f (⟨memory, owed, .readPayload, events, cost⟩ : Config T)
          readContinuation
          (targetRunner (.readU8 program.payloadPointer 1 program.alignment) memory)
    | writePayload value =>
      simp only [next, mapCfg]
      rw [commutes]
      simpa only [mapCfg] using
        handle_commutes f (⟨memory, owed, .writePayload value, events, cost⟩ : Config T)
          (writeContinuation value)
          (targetRunner (.writeRaw program.writePointer 1 program.alignment
            (.init value none)) memory)
    | finish => rfl
    | spin => rfl
    | done => rfl
    | unwound => rfl
    | bad fault => rfl
    | unsupported => rfl

theorem map_step {before after : Config T}
    (edge : Step targetRunner program before after) :
    Step sourceRunner program (mapCfg f before) (mapCfg f after) := by
  unfold Step at *
  rw [next_commutes f sourceRunner targetRunner commutes program, edge]
  rfl

theorem lift_step {before : Config T} {after : Config S}
    (edge : Step sourceRunner program (mapCfg f before) after) :
    ∃ targetAfter, Step targetRunner program before targetAfter ∧ mapCfg f targetAfter = after := by
  unfold Step at edge
  rw [next_commutes f sourceRunner targetRunner commutes program] at edge
  cases result : next targetRunner program before with
  | none => simp [result] at edge
  | some targetAfter =>
    have same : mapCfg f targetAfter = after := by
      simpa only [result, Option.map_some, Option.some.injEq] using edge
    exact ⟨targetAfter, result, same⟩

omit commutes in
theorem bad_map (cfg : Config T) : Bad (mapCfg f cfg) ↔ Bad cfg := Iff.rfl

theorem source_simulation :
    StutteringSimulation (Step sourceRunner program) (Step targetRunner program) Bad Bad
      (fun source target => source = mapCfg f target) := by
  constructor
  · intro source sourceAfter target related edge
    subst source
    obtain ⟨targetAfter, targetEdge, same⟩ :=
      lift_step f sourceRunner targetRunner commutes program edge
    exact ⟨targetAfter, Reach.tail (Reach.refl _) targetEdge, same.symm⟩
  · intro source target related bad
    subst source
    exact (bad_map f target).mp bad

theorem target_simulation :
    StutteringSimulation (Step targetRunner program) (Step sourceRunner program) Bad Bad
      (fun target source => source = mapCfg f target) := by
  constructor
  · intro target targetAfter source related edge
    subst source
    exact ⟨mapCfg f targetAfter, Reach.tail (Reach.refl _)
      (map_step f sourceRunner targetRunner commutes program edge), rfl⟩
  · intro target source related bad
    subst source
    exact (bad_map f target).mpr bad

theorem map_reach {before after : Config T}
    (path : Reach (Step targetRunner program) before after) :
    Reach (Step sourceRunner program) (mapCfg f before) (mapCfg f after) := by
  induction path with
  | refl => exact Reach.refl _
  | tail _ edge ih =>
    exact Reach.tail ih (map_step f sourceRunner targetRunner commutes program edge)

/-- Exact configuration coverage includes every failure prefix, residual joint
state, obligation bit, event, and logical cost. Each edge is matched by one edge. -/
theorem prefix_iff (before : Config T) (after : Config S) :
    Reach (Step sourceRunner program) (mapCfg f before) after ↔
      ∃ targetAfter, Reach (Step targetRunner program) before targetAfter ∧
        mapCfg f targetAfter = after := by
  constructor
  · intro path
    obtain ⟨targetAfter, targetPath, related⟩ := PrefixTransfer.reachable_coverage
      (source_simulation f sourceRunner targetRunner commutes program) rfl path
    exact ⟨targetAfter, targetPath, related.symm⟩
  · rintro ⟨targetAfter, targetPath, rfl⟩
    exact map_reach f sourceRunner targetRunner commutes program targetPath

theorem noUB_iff (before : Config T) :
    NoUB (Step sourceRunner program) Bad (mapCfg f before) ↔
      NoUB (Step targetRunner program) Bad before := by
  constructor
  · exact PrefixTransfer.sourceSafety
      (target_simulation f sourceRunner targetRunner commutes program) rfl
  · exact PrefixTransfer.sourceSafety
      (source_simulation f sourceRunner targetRunner commutes program) rfl

end Correspondence

abbrev SourceStep (program : Program) := Step runCoupled program
abbrev TargetStep (program : Program) := Step runFactored program

theorem cleanup_prefix_iff (program : Program) (before : Config Factored) (after : Config Coupled) :
    Reach (SourceStep program) (mapCfg reify before) after ↔
      ∃ targetAfter, Reach (TargetStep program) before targetAfter ∧ mapCfg reify targetAfter = after :=
  prefix_iff reify runCoupled runFactored run_reify program before after

theorem cleanup_noUB_iff (program : Program) (before : Config Factored) :
    NoUB (SourceStep program) Bad (mapCfg reify before) ↔
      NoUB (TargetStep program) Bad before :=
  noUB_iff reify runCoupled runFactored run_reify program before

theorem reify_encode_config (cfg : Config Coupled) :
    mapCfg reify (mapCfg encode cfg) = cfg := by
  cases cfg
  simp [mapCfg, MemoryPermissions.reify_encode]

theorem encoded_cleanup_prefix_iff (program : Program) (before after : Config Coupled) :
    Reach (SourceStep program) before after ↔
      ∃ targetAfter, Reach (TargetStep program) (mapCfg encode before) targetAfter ∧
        mapCfg reify targetAfter = after := by
  simpa only [reify_encode_config] using
    cleanup_prefix_iff program (mapCfg encode before) after

theorem encoded_cleanup_noUB_iff (program : Program) (before : Config Coupled) :
    NoUB (SourceStep program) Bad before ↔
      NoUB (TargetStep program) Bad (mapCfg encode before) := by
  simpa only [reify_encode_config] using
    cleanup_noUB_iff program (mapCfg encode before)

def run {S : Type} (runner : Command → S → Result Reply S) (program : Program) :
    Nat → Config S → Option (Config S)
  | 0, cfg => some cfg
  | n + 1, cfg => (next runner program cfg).bind (run runner program n)

theorem run_reach {S : Type} (runner : Command → S → Result Reply S) (program : Program)
    {count : Nat} {before after : Config S}
    (executed : run runner program count before = some after) :
    Reach (Step runner program) before after := by
  induction count generalizing before with
  | zero =>
    have same : before = after := Option.some.inj executed
    subst after
    exact Reach.refl _
  | succ count ih =>
    cases edge : next runner program before with
    | none => simp [run, edge] at executed
    | some middle =>
      have rest : run runner program count middle = some after := by
        simpa [run, edge] using executed
      have step : Step runner program before middle := edge
      have first : Reach (Step runner program) before middle :=
        Reach.tail (Reach.refl before) step
      exact first.trans (ih rest)

def beforeReadEvents (bytes : List MiniRustReference.Byte) : List Event :=
  [.bodyRead bytes, .tested true, .consumed, .called]

def beforeRead {S : Type} (memory : S) (bytes : List MiniRustReference.Byte) : Config S :=
  ⟨memory, false, .readPayload, beforeReadEvents bytes, 4⟩

def finished {S : Type} (program : Program) (memory : S)
    (bytes : List MiniRustReference.Byte) (value : Fin 256) : Config S :=
  ⟨memory, false, (finishControl program.finish).1,
    beforeReadEvents bytes ++ [.payloadRead value, .payloadWritten value,
      (finishControl program.finish).2], 7⟩

def readFailed {S : Type} (memory : S) (bytes : List MiniRustReference.Byte)
    (fault : Fault) : Config S :=
  ⟨memory, false, .bad fault, beforeReadEvents bytes ++ [.failed fault], 5⟩

def writeFailed {S : Type} (memory : S) (bytes : List MiniRustReference.Byte)
    (value : Fin 256) (fault : Fault) : Config S :=
  ⟨memory, false, .bad fault,
    beforeReadEvents bytes ++ [.payloadRead value, .failed fault], 6⟩

section Executions

variable {S : Type} (runner : Command → S → Result Reply S) (program : Program)
variable {m0 m1 m2 m3 : S} {bytes : List MiniRustReference.Byte} {value : Fin 256}

theorem run_to_read
    (bodyOK : runner (.readRaw program.bodyPointer 0 program.alignment) m0 = .ok (.raw bytes) m1) :
    run runner program 4 (initial m0) = some (beforeRead m1 bytes) := by
  simp [run, initial, next, handle, bodyContinuation, bodyOK, tick, tickWith,
    beforeRead, beforeReadEvents]

theorem run_good
    (bodyOK : runner (.readRaw program.bodyPointer 0 program.alignment) m0 = .ok (.raw bytes) m1)
    (readOK : runner (.readU8 program.payloadPointer 1 program.alignment) m1 = .ok (.number value) m2)
    (writeOK : runner (.writeRaw program.writePointer 1 program.alignment (.init value none)) m2 =
      .ok .unit m3) :
    run runner program 7 (initial m0) = some (finished program m3 bytes value) := by
  cases mode : program.finish <;>
    simp [run, initial, next, handle, bodyContinuation, readContinuation,
      writeContinuation, bodyOK, readOK, writeOK, tick, tickWith, finished,
      finishControl, beforeReadEvents, mode]

theorem run_read_failure {fault : Fault}
    (bodyOK : runner (.readRaw program.bodyPointer 0 program.alignment) m0 = .ok (.raw bytes) m1)
    (readUB : runner (.readU8 program.payloadPointer 1 program.alignment) m1 = .ub fault m2) :
    run runner program 5 (initial m0) = some (readFailed m2 bytes fault) := by
  simp [run, initial, next, handle, bodyContinuation, bodyOK, readUB, tick, tickWith,
    readFailed, beforeReadEvents]

theorem run_write_failure {fault : Fault}
    (bodyOK : runner (.readRaw program.bodyPointer 0 program.alignment) m0 = .ok (.raw bytes) m1)
    (readOK : runner (.readU8 program.payloadPointer 1 program.alignment) m1 = .ok (.number value) m2)
    (writeUB : runner (.writeRaw program.writePointer 1 program.alignment (.init value none)) m2 =
      .ub fault m3) :
    run runner program 6 (initial m0) = some (writeFailed m3 bytes value fault) := by
  simp [run, initial, next, handle, bodyContinuation, readContinuation, bodyOK,
    readOK, writeUB, tick, tickWith, writeFailed, beforeReadEvents]

theorem read_failure_not_safe {fault : Fault}
    (bodyOK : runner (.readRaw program.bodyPointer 0 program.alignment) m0 = .ok (.raw bytes) m1)
    (readUB : runner (.readU8 program.payloadPointer 1 program.alignment) m1 = .ub fault m2) :
    ¬ NoUB (Step runner program) Bad (initial m0) :=
  bad_prefix_not_noUB (run_reach runner program (run_read_failure runner program bodyOK readUB))
    True.intro

theorem write_failure_not_safe {fault : Fault}
    (bodyOK : runner (.readRaw program.bodyPointer 0 program.alignment) m0 = .ok (.raw bytes) m1)
    (readOK : runner (.readU8 program.payloadPointer 1 program.alignment) m1 = .ok (.number value) m2)
    (writeUB : runner (.writeRaw program.writePointer 1 program.alignment (.init value none)) m2 =
      .ub fault m3) :
    ¬ NoUB (Step runner program) Bad (initial m0) :=
  bad_prefix_not_noUB
    (run_reach runner program (run_write_failure runner program bodyOK readOK writeUB)) True.intro

end Executions

/-- This clears only the obligation. The actual joint memory is still m. -/
theorem consumed_obligation_retains_payload_state {S : Type}
    (memory : S) (bytes : List MiniRustReference.Byte) :
    (beforeRead memory bytes).owed = false ∧
    (beforeRead memory bytes).memory = memory ∧
    (beforeRead memory bytes).cost = 4 := ⟨rfl, rfl, rfl⟩

theorem kernel_failure_retains_state {S : Type} (cfg : Config S)
    (continuation : Reply → Phase × Event) (fault : Fault) (residual : S) :
    handle cfg continuation (.ub fault residual) =
      some ⟨residual, cfg.owed, .bad fault, cfg.events ++ [.failed fault], cfg.cost + 1⟩ := rfl

theorem unsupported_is_separate {S : Type} (cfg : Config S)
    (continuation : Reply → Phase × Event) (residual : S) :
    handle cfg continuation (.unsupported residual) =
      some ⟨residual, cfg.owed, .unsupported, cfg.events ++ [.unsupported], cfg.cost + 1⟩ := rfl

theorem noChoice_has_no_successor {S : Type} (cfg : Config S)
    (continuation : Reply → Phase × Event) (residual : S) :
    handle cfg continuation (.noChoice residual) = none := rfl

section SafetyAndInfiniteContinuation

variable {S : Type} (runner : Command → S → Result Reply S) (program : Program)

theorem bad_has_no_successor (cfg : Config S) (bad : Bad cfg) :
    next runner program cfg = none := by
  cases phase : cfg.phase <;> simp_all [Bad, next]

theorem terminal_safe (cfg : Config S) (notBad : ¬ Bad cfg)
    (stopped : next runner program cfg = none) :
    NoUB (Step runner program) Bad cfg := by
  apply invariant_noUB (Invariant := fun reached => reached = cfg) rfl
  · intro before after same edge
    subst before
    change next runner program cfg = some after at edge
    rw [stopped] at edge
    cases edge
  · intro reached same
    subst reached
    exact notBad

theorem noUB_before_step {before after : Config S}
    (edge : next runner program before = some after)
    (notBad : ¬ Bad before) (safe : NoUB (Step runner program) Bad after) :
    NoUB (Step runner program) Bad before := by
  apply invariant_noUB
    (Invariant := fun reached => reached = before ∨ Reach (Step runner program) after reached)
    (Or.inl rfl)
  · intro current successor member step
    cases member with
    | inl same =>
      subst current
      change next runner program before = some successor at step
      have same : after = successor := Option.some.inj (edge.symm.trans step)
      subst successor
      exact Or.inr (Reach.refl _)
    | inr path => exact Or.inr (Reach.tail path step)
  · intro reached member
    cases member with
    | inl same => subst reached; exact notBad
    | inr path => exact safe reached path

theorem noUB_of_run {count : Nat} {before after : Config S}
    (executed : run runner program count before = some after)
    (safe : NoUB (Step runner program) Bad after) :
    NoUB (Step runner program) Bad before := by
  induction count generalizing before with
  | zero =>
    have same : before = after := Option.some.inj executed
    subst before
    exact safe
  | succ count ih =>
    cases edge : next runner program before with
    | none => simp [run, edge] at executed
    | some middle =>
      have rest : run runner program count middle = some after := by
        simpa [run, edge] using executed
      apply noUB_before_step runner program edge
      · intro bad
        have stopped := bad_has_no_successor runner program before bad
        rw [stopped] at edge
        cases edge
      · exact ih rest

theorem spin_safe (cfg : Config S) (spinning : cfg.phase = .spin) :
    NoUB (Step runner program) Bad cfg := by
  apply invariant_noUB (Invariant := fun reached => reached.phase = .spin) spinning
  · intro before after phase edge
    change next runner program before = some after at edge
    have nextSpin : next runner program before = some (tick before .spin .spinning) := by
      simp [next, phase]
    have same : tick before .spin .spinning = after :=
      Option.some.inj (nextSpin.symm.trans edge)
    subst after
    rfl
  · intro reached phase
    simp [Bad, phase]

theorem finished_safe (memory : S) (bytes : List MiniRustReference.Byte) (value : Fin 256) :
    NoUB (Step runner program) Bad (finished program memory bytes value) := by
  cases mode : program.finish with
  | normal =>
    apply terminal_safe runner program
    · simp [Bad, finished, finishControl, mode]
    · simp [next, finished, finishControl, mode]
  | unwind =>
    apply terminal_safe runner program
    · simp [Bad, finished, finishControl, mode]
    · simp [next, finished, finishControl, mode]
  | spin =>
    apply spin_safe runner program
    simp [finished, finishControl, mode]

theorem good_cleanup_safe {m0 m1 m2 m3 : S} {bytes : List MiniRustReference.Byte} {value : Fin 256}
    (bodyOK : runner (.readRaw program.bodyPointer 0 program.alignment) m0 = .ok (.raw bytes) m1)
    (readOK : runner (.readU8 program.payloadPointer 1 program.alignment) m1 = .ok (.number value) m2)
    (writeOK : runner (.writeRaw program.writePointer 1 program.alignment (.init value none)) m2 =
      .ok .unit m3) :
    NoUB (Step runner program) Bad (initial m0) :=
  noUB_of_run runner program (run_good runner program bodyOK readOK writeOK)
    (finished_safe runner program m3 bytes value)

def spinChain (cfg : Config S) : Nat → Config S
  | 0 => cfg
  | n + 1 => tick (spinChain cfg n) .spin .spinning

theorem spinChain_phase (cfg : Config S) (spinning : cfg.phase = .spin) (n : Nat) :
    (spinChain cfg n).phase = .spin := by
  cases n with
  | zero => exact spinning
  | succ n => rfl

/-- A concrete Nat-indexed infinite sequence of enabled steps, not merely the
absence of a bad outcome. No scheduler/fairness claim is involved. -/
theorem actual_infinite_continuation (cfg : Config S) (spinning : cfg.phase = .spin) :
    ∃ states : Nat → Config S, states 0 = cfg ∧
      ∀ n, Step runner program (states n) (states (n + 1)) := by
  refine ⟨spinChain cfg, rfl, ?_⟩
  intro n
  change next runner program (spinChain cfg n) =
    some (tick (spinChain cfg n) .spin .spinning)
  simp [next, spinChain_phase cfg spinning n]

end SafetyAndInfiniteContinuation

namespace Concrete

open MemoryPermissions.Fixtures

def program (finish : Finish) : Program := ⟨pointer0, pointer0, pointer0, 1, finish⟩

theorem initialized_cleanup_run (value : Fin 256) (finish : Finish) :
    run runCoupled (program finish) 7 (initial (stable value)) =
      some (finished (program finish) (stableWritten value value) [byte value] value) :=
  run_good runCoupled (program finish) (stable_raw_read value)
    (stable_typed_read value) (stable_write value value)

theorem initialized_cleanup_safe (value : Fin 256) (finish : Finish) :
    NoUB (SourceStep (program finish)) Bad (initial (stable value)) :=
  good_cleanup_safe runCoupled (program finish) (stable_raw_read value)
    (stable_typed_read value) (stable_write value value)

/-- The consumed obligation has not deinitialized the actual payload. -/
theorem consumed_payload_still_readable (value : Fin 256) :
    run runCoupled (program .normal) 4 (initial (stable value)) =
      some (beforeRead (stableRead0 value) [byte value]) ∧
    (beforeRead (stableRead0 value) [byte value]).owed = false ∧
    runCoupled (.readU8 pointer0 1 1) (beforeRead (stableRead0 value) [byte value]).memory =
      .ok (.number value) (stableRead1 value) :=
  ⟨run_to_read runCoupled (program .normal) (stable_raw_read value), rfl, stable_typed_read value⟩

theorem actual_written_payload (value : Fin 256) :
    MiniRustReference.load (stableWritten value value).memory pointer0 1 1 =
      .ok ([byte value], (stableWritten value value).memory) := rfl

/-- Stable Cell permissions permit the complete same-byte cleanup, whereas
the alias fixture's Unique foreign permission is frozen by the body read. -/
theorem permission_only_write_failure (value : Fin 256) :
    run runCoupled (program .normal) 6 (initial (aliasing value)) =
      some (writeFailed (aliasRead1 value) [byte value] value (.permission .localWriteFrozen)) ∧
    ¬ NoUB (SourceStep (program .normal)) Bad (initial (aliasing value)) :=
  ⟨run_write_failure runCoupled (program .normal) (alias_raw_read value)
      (alias_typed_read value) (alias_write_fails value value),
    write_failure_not_safe runCoupled (program .normal) (alias_raw_read value)
      (alias_typed_read value) (alias_write_fails value value)⟩

def uninitAfterRead1 : Coupled :=
  ⟨uninitAfterRead0.memory,
    BorrowFrame.update uninitAfterRead0.permissions (access0 1 .read) .Frozen⟩

theorem uninit_raw_body :
    runCoupled (.readRaw pointer0 0 1) uninitState =
      .ok (.raw [.uninit]) uninitAfterRead0 := rfl

theorem uninit_cleanup_read :
    runCoupled (.readU8 pointer0 1 1) uninitAfterRead0 =
      .ub .uninitialized uninitAfterRead1 := rfl

theorem uninitialized_cleanup_failure :
    run runCoupled (program .normal) 5 (initial uninitState) =
      some (readFailed uninitAfterRead1 [.uninit] .uninitialized) ∧
    ¬ NoUB (SourceStep (program .normal)) Bad (initial uninitState) :=
  ⟨run_read_failure runCoupled (program .normal) uninit_raw_body uninit_cleanup_read,
    read_failure_not_safe runCoupled (program .normal) uninit_raw_body uninit_cleanup_read⟩

/-- The syntactic spin policy cannot hide the preceding permission UB. -/
theorem bad_before_would_be_spin (value : Fin 256) :
    run runCoupled (program .spin) 6 (initial (aliasing value)) =
      some (writeFailed (aliasRead1 value) [byte value] value (.permission .localWriteFrozen)) ∧
    ¬ NoUB (SourceStep (program .spin)) Bad (initial (aliasing value)) ∧
    next runCoupled (program .spin)
      (writeFailed (aliasRead1 value) [byte value] value (.permission .localWriteFrozen)) = none :=
  ⟨run_write_failure runCoupled (program .spin) (alias_raw_read value)
      (alias_typed_read value) (alias_write_fails value value),
    write_failure_not_safe runCoupled (program .spin) (alias_raw_read value)
      (alias_typed_read value) (alias_write_fails value value), rfl⟩

theorem initialized_cleanup_has_safe_infinite_continuation (value : Fin 256) :
    Reach (SourceStep (program .spin)) (initial (stable value))
      (finished (program .spin) (stableWritten value value) [byte value] value) ∧
    NoUB (SourceStep (program .spin)) Bad (initial (stable value)) ∧
    ∃ states : Nat → Config Coupled,
      states 0 = finished (program .spin) (stableWritten value value) [byte value] value ∧
      ∀ n, SourceStep (program .spin) (states n) (states (n + 1)) :=
  ⟨run_reach runCoupled (program .spin) (initialized_cleanup_run value .spin),
    initialized_cleanup_safe value .spin,
    actual_infinite_continuation runCoupled (program .spin)
      (finished (program .spin) (stableWritten value value) [byte value] value) rfl⟩

end Concrete

#print axioms cleanup_prefix_iff
#print axioms cleanup_noUB_iff
#print axioms encoded_cleanup_prefix_iff
#print axioms encoded_cleanup_noUB_iff
#print axioms map_observations
#print axioms run_to_read
#print axioms run_good
#print axioms run_read_failure
#print axioms run_write_failure
#print axioms read_failure_not_safe
#print axioms write_failure_not_safe
#print axioms consumed_obligation_retains_payload_state
#print axioms kernel_failure_retains_state
#print axioms unsupported_is_separate
#print axioms noChoice_has_no_successor
#print axioms good_cleanup_safe
#print axioms actual_infinite_continuation
#print axioms Concrete.initialized_cleanup_run
#print axioms Concrete.initialized_cleanup_safe
#print axioms Concrete.consumed_payload_still_readable
#print axioms Concrete.actual_written_payload
#print axioms Concrete.permission_only_write_failure
#print axioms Concrete.uninitialized_cleanup_failure
#print axioms Concrete.bad_before_would_be_spin
#print axioms Concrete.initialized_cleanup_has_safe_infinite_continuation

end AnnealResearch.PermissionCleanup
