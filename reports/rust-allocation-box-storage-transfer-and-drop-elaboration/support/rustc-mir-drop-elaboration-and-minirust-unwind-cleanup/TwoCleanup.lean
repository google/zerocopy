import AnnealResearch.EffectfulDestructor
import AnnealResearch.PrefixTransfer

/-!
Independent bounded cleanup controllers, sharing only the disclosed destructor
engine. The high controller traverses the four possible remaining-obligation
lists for two constructed fields. The low controller interprets a CFG with
literal normal/unwind continuation labels and a flag for the second field only.
There is no first-field flag: its consumption is represented by CFG progress.

The owned policy fixes the second destructor to return. This is not inferred
from a Rust panic flag or a claim that its library calls cannot unwind. A second
unwind while already unwinding is explicitly rejected, outside the admitted
positive family. Constructor temporaries, moving/suppressing ownership before
this entry point, drop glue, Rust lowering, and full Tree Borrows remain outside
the theorem. Every engine prefix, including intermediate UB, remains visible.

Related boundaries retain exact memory, events, and engineCost. Extra low-level
flag-test/clear steps are excluded from that partial engine metric. No equality
of total controller costs or deployed performance bound is asserted.
-/

namespace AnnealResearch.TwoCleanup

open EffectfulDestructor MemoryPermissions Execution PrefixTransfer

structure Plan where
  pointer : Field → MiniRustReference.Ptr
  firstExit : Exit

def outcome (plan : Plan) : Field → Exit
  | .first => plan.firstExit
  | .second => .returned

/-- Names for [], [first], [second], and [first,second], rather than CFG labels. -/
inductive Todo where | empty | firstOnly | secondOnly | both

def remaining (secondOwed : Bool) : Todo := if secondOwed then .secondOnly else .empty

inductive HighControl where
  | clean (todo : Todo) (mode : Mode)
  | first (phase : Phase) (secondOwed : Bool) (mode : Mode)
  | second (phase : Phase) (mode : Mode)
  | done (mode : Mode)
  | rejected (secondOwed : Bool)

structure HighState (S : Type) where
  control : HighControl
  data : Data S

inductive HighStep {S : Type} (runner : Command → S → Result Reply S) (plan : Plan) :
    HighState S → HighState S → Prop where
  | enterBoth (data mode) :
      HighStep runner plan ⟨.clean .both mode, data⟩
        ⟨.first .read true mode, data.record (.entered .first)⟩
  | enterFirst (data mode) :
      HighStep runner plan ⟨.clean .firstOnly mode, data⟩
        ⟨.first .read false mode, data.record (.entered .first)⟩
  | enterSecond (data mode) :
      HighStep runner plan ⟨.clean .secondOnly mode, data⟩
        ⟨.second .read mode, data.record (.entered .second)⟩
  | engineFirst (data after phase nextPhase owed mode)
      (edge : EffectfulDestructor.Step runner (plan.pointer .first) .first plan.firstExit
        ⟨phase, data⟩ ⟨nextPhase, after⟩) :
      HighStep runner plan ⟨.first phase owed mode, data⟩ ⟨.first nextPhase owed mode, after⟩
  | engineSecond (data after phase nextPhase mode)
      (edge : EffectfulDestructor.Step runner (plan.pointer .second) .second .returned
        ⟨phase, data⟩ ⟨nextPhase, after⟩) :
      HighStep runner plan ⟨.second phase mode, data⟩ ⟨.second nextPhase mode, after⟩
  | returnedFirst (data owed mode) :
      HighStep runner plan ⟨.first .returned owed mode, data⟩ ⟨.clean (remaining owed) mode, data⟩
  | unwoundFirst (data owed) :
      HighStep runner plan ⟨.first .unwound owed .normal, data⟩
        ⟨.clean (remaining owed) .unwinding, data⟩
  | rejectedFirst (data owed) :
      HighStep runner plan ⟨.first .unwound owed .unwinding, data⟩
        ⟨.rejected owed, data.record .rejectedDoubleUnwind⟩
  | returnedSecond (data mode) :
      HighStep runner plan ⟨.second .returned mode, data⟩ ⟨.clean .empty mode, data⟩
  | unwoundSecond (data) :
      HighStep runner plan ⟨.second .unwound .normal, data⟩ ⟨.clean .empty .unwinding, data⟩
  | rejectedSecond (data) :
      HighStep runner plan ⟨.second .unwound .unwinding, data⟩
        ⟨.rejected false, data.record .rejectedDoubleUnwind⟩
  | finish (data mode) :
      HighStep runner plan ⟨.clean .empty mode, data⟩
        ⟨.done mode, data.record (.finished mode)⟩

inductive PC where
  | callFirst (mode : Mode) | testSecond (mode : Mode) | clearSecond (mode : Mode)
  | callSecond (mode : Mode) | exit (mode : Mode) | reject

inductive Instruction where
  | call (field : Field) (normal unwind : PC)
  | test (yes no : PC) | clear (next : PC) | exit (mode : Mode) | reject

def firstUnwind : Mode → PC
  | .normal => .testSecond .unwinding | .unwinding => .reject
def secondUnwind : Mode → PC
  | .normal => .exit .unwinding | .unwinding => .reject

/-- Independent CFG lookup; no high transition is used to execute it. -/
def program : PC → Instruction
  | .callFirst mode => .call .first (.testSecond mode) (firstUnwind mode)
  | .testSecond mode => .test (.clearSecond mode) (.exit mode)
  | .clearSecond mode => .clear (.callSecond mode)
  | .callSecond mode => .call .second (.exit mode) (secondUnwind mode)
  | .exit mode => .exit mode
  | .reject => .reject

inductive LowControl where
  | at (pc : PC)
  | running (field : Field) (phase : Phase) (normal unwind : PC)
  | done (mode : Mode) | rejected

structure LowState (S : Type) where
  control : LowControl
  data : Data S
  secondOwed : Bool

inductive LowStep {S : Type} (runner : Command → S → Result Reply S) (plan : Plan) :
    LowState S → LowState S → Prop where
  | testTrue {data pc yes no} (ins : program pc = .test yes no) :
      LowStep runner plan ⟨.at pc, data, true⟩ ⟨.at yes, data, true⟩
  | testFalse {data pc yes no} (ins : program pc = .test yes no) :
      LowStep runner plan ⟨.at pc, data, false⟩ ⟨.at no, data, false⟩
  | clear {data pc next owed} (ins : program pc = .clear next) :
      LowStep runner plan ⟨.at pc, data, owed⟩ ⟨.at next, data, false⟩
  | invoke {data pc field normal unwind owed} (ins : program pc = .call field normal unwind) :
      LowStep runner plan ⟨.at pc, data, owed⟩
        ⟨.running field .read normal unwind, data.record (.entered field), owed⟩
  | engine {data after field phase nextPhase normal unwind owed}
      (edge : EffectfulDestructor.Step runner (plan.pointer field) field (outcome plan field)
        ⟨phase, data⟩ ⟨nextPhase, after⟩) :
      LowStep runner plan ⟨.running field phase normal unwind, data, owed⟩
        ⟨.running field nextPhase normal unwind, after, owed⟩
  | returned {data field normal unwind owed} :
      LowStep runner plan ⟨.running field .returned normal unwind, data, owed⟩ ⟨.at normal, data, owed⟩
  | unwound {data field normal unwind owed} :
      LowStep runner plan ⟨.running field .unwound normal unwind, data, owed⟩ ⟨.at unwind, data, owed⟩
  | finish {data pc mode owed} (ins : program pc = .exit mode) :
      LowStep runner plan ⟨.at pc, data, owed⟩ ⟨.done mode, data.record (.finished mode), owed⟩
  | reject {data pc owed} (ins : program pc = .reject) :
      LowStep runner plan ⟨.at pc, data, owed⟩ ⟨.rejected, data.record .rejectedDoubleUnwind, owed⟩

/-- A functional characterization of the existing low interpreter, used only
to establish determinism. It does not define or execute the high controller. -/
def lowNext {S : Type} (runner : Command → S → Result Reply S) (plan : Plan)
    (state : LowState S) : Option (LowState S) :=
  match state.control with
  | .at pc =>
    match program pc with
    | .test yes no => some ⟨.at (if state.secondOwed then yes else no), state.data, state.secondOwed⟩
    | .clear next => some ⟨.at next, state.data, false⟩
    | .call field normal unwind =>
        some ⟨.running field .read normal unwind, state.data.record (.entered field), state.secondOwed⟩
    | .exit mode => some ⟨.done mode, state.data.record (.finished mode), state.secondOwed⟩
    | .reject => some ⟨.rejected, state.data.record .rejectedDoubleUnwind, state.secondOwed⟩
  | .running field phase normal unwind =>
    match phase with
    | .returned => some ⟨.at normal, state.data, state.secondOwed⟩
    | .unwound => some ⟨.at unwind, state.data, state.secondOwed⟩
    | _ =>
      (EffectfulDestructor.next runner (plan.pointer field) field (outcome plan field)
        ⟨phase, state.data⟩).map (fun after =>
          ⟨.running field after.phase normal unwind, after.data, state.secondOwed⟩)
  | .done _ | .rejected => none

theorem low_step_equation {S : Type} (runner : Command → S → Result Reply S) (plan : Plan)
    {before after : LowState S} (edge : LowStep runner plan before after) :
    lowNext runner plan before = some after := by
  cases edge with
  | testTrue ins => simp [lowNext, ins]
  | testFalse ins => simp [lowNext, ins]
  | clear ins => simp [lowNext, ins]
  | invoke ins => simp [lowNext, ins]
  | @engine data after field phase nextPhase normal unwind owed edge =>
    change EffectfulDestructor.next runner (plan.pointer field) field (outcome plan field)
      ⟨phase, data⟩ = some ⟨nextPhase, after⟩ at edge
    cases phase with
    | read => simp [lowNext, edge]
    | compute value => simp [lowNext, edge]
    | write value => simp [lowNext, edge]
    | decide => simp [lowNext, edge]
    | returned => simp [EffectfulDestructor.next] at edge
    | unwound => simp [EffectfulDestructor.next] at edge
    | bad fault => simp [EffectfulDestructor.next] at edge
    | unsupported => simp [EffectfulDestructor.next] at edge
  | returned => rfl
  | unwound => rfl
  | finish ins => simp [lowNext, ins]
  | reject ins => simp [lowNext, ins]

theorem low_step_deterministic {S : Type} (runner : Command → S → Result Reply S) (plan : Plan)
    {before first second : LowState S}
    (firstEdge : LowStep runner plan before first) (secondEdge : LowStep runner plan before second) :
    first = second :=
  Option.some.inj ((low_step_equation runner plan firstEdge).symm.trans
    (low_step_equation runner plan secondEdge))

def compile {S : Type} (source : HighState S) : LowState S :=
  match source.control with
  | .clean .both mode => ⟨.at (.callFirst mode), source.data, true⟩
  | .clean .firstOnly mode => ⟨.at (.callFirst mode), source.data, false⟩
  | .clean .secondOnly mode => ⟨.at (.testSecond mode), source.data, true⟩
  | .clean .empty mode => ⟨.at (.exit mode), source.data, false⟩
  | .first phase owed mode =>
      ⟨.running .first phase (.testSecond mode) (firstUnwind mode), source.data, owed⟩
  | .second phase mode =>
      ⟨.running .second phase (.exit mode) (secondUnwind mode), source.data, false⟩
  | .done mode => ⟨.done mode, source.data, false⟩
  | .rejected owed => ⟨.rejected, source.data, owed⟩

def HighBad {S : Type} (source : HighState S) : Prop :=
  match source.control with
  | .first (.bad _) _ _ | .second (.bad _) _ => True
  | _ => False

def LowBad {S : Type} (target : LowState S) : Prop :=
  match target.control with | .running _ (.bad _) _ _ => True | _ => False

def Related {S : Type} (source : HighState S) (target : LowState S) : Prop := target = compile source

private theorem one {S : Type} {relation : S → S → Prop} {before after : S}
    (edge : relation before after) : Reach relation before after := Reach.tail (Reach.refl _) edge

/-- Conditional on the explicitly supplied kernel/body semantics, controller
lowering covers every high engine prefix, rather than only completed calls. -/
theorem simulation {S : Type} (runner : Command → S → Result Reply S) (plan : Plan) :
    StutteringSimulation (HighStep runner plan) (LowStep runner plan) HighBad LowBad Related := by
  constructor
  · intro source sourceAfter target related edge
    rcases related with rfl
    refine ⟨compile sourceAfter, ?_, rfl⟩
    cases edge with
    | enterBoth data mode => exact one (LowStep.invoke rfl)
    | enterFirst data mode => exact one (LowStep.invoke rfl)
    | enterSecond data mode =>
      exact Reach.tail (Reach.tail (one (LowStep.testTrue rfl))
        (LowStep.clear rfl)) (LowStep.invoke rfl)
    | engineFirst data after phase nextPhase owed mode edge => exact one (LowStep.engine edge)
    | engineSecond data after phase nextPhase mode edge => exact one (LowStep.engine edge)
    | returnedFirst data owed mode =>
      cases owed with
      | false => exact Reach.tail (one LowStep.returned) (LowStep.testFalse rfl)
      | true => exact one LowStep.returned
    | unwoundFirst data owed =>
      cases owed with
      | false => exact Reach.tail (one LowStep.unwound) (LowStep.testFalse rfl)
      | true => exact one LowStep.unwound
    | rejectedFirst data owed => exact Reach.tail (one LowStep.unwound) (LowStep.reject rfl)
    | returnedSecond data mode => exact one LowStep.returned
    | unwoundSecond data => exact one LowStep.unwound
    | rejectedSecond data => exact Reach.tail (one LowStep.unwound) (LowStep.reject rfl)
    | finish data mode => exact one (LowStep.finish rfl)
  · intro source target related bad
    rcases related with rfl
    cases source with
    | mk control data =>
      cases control with
      | clean todo mode => exact False.elim bad
      | first phase owed mode => cases phase <;> simp_all [HighBad, LowBad, compile]
      | second phase mode => cases phase <;> simp_all [HighBad, LowBad, compile]
      | done mode => exact False.elim bad
      | rejected owed => exact False.elim bad

theorem safety_transfer {S : Type} (runner : Command → S → Result Reply S) (plan : Plan)
    (source : HighState S) (safe : NoUB (LowStep runner plan) LowBad (compile source)) :
    NoUB (HighStep runner plan) HighBad source :=
  PrefixTransfer.sourceSafety (simulation runner plan) rfl safe

theorem compiled_reachable {S : Type} (runner : Command → S → Result Reply S) (plan : Plan)
    {before after : HighState S} (path : Reach (HighStep runner plan) before after) :
    Reach (LowStep runner plan) (compile before) (compile after) := by
  obtain ⟨target, reached, related⟩ := PrefixTransfer.reachable_coverage
    (simulation runner plan) rfl path
  change target = compile after at related
  rw [related] at reached
  exact reached

theorem boundary_data {S : Type} (source : HighState S) :
    (compile source).data = source.data := by
  cases source with
  | mk control data =>
    cases control with
    | clean todo mode => cases todo <;> rfl
    | first phase owed mode => rfl
    | second phase mode => rfl
    | done mode => rfl
    | rejected owed => rfl

theorem first_engine_path {S : Type} (runner : Command → S → Result Reply S) (plan : Plan)
    (owed : Bool) (mode : Mode) {before after : EffectfulDestructor.State S}
    (path : Reach (EffectfulDestructor.Step runner (plan.pointer .first) .first plan.firstExit) before after) :
    Reach (HighStep runner plan) ⟨.first before.phase owed mode, before.data⟩
      ⟨.first after.phase owed mode, after.data⟩ := by
  induction path with
  | refl => exact Reach.refl _
  | tail _ edge ih => exact Reach.tail ih (HighStep.engineFirst _ _ _ _ _ _ edge)

theorem second_engine_path {S : Type} (runner : Command → S → Result Reply S) (plan : Plan)
    (mode : Mode) {before after : EffectfulDestructor.State S}
    (path : Reach (EffectfulDestructor.Step runner (plan.pointer .second) .second .returned) before after) :
    Reach (HighStep runner plan) ⟨.second before.phase mode, before.data⟩
      ⟨.second after.phase mode, after.data⟩ := by
  induction path with
  | refl => exact Reach.refl _
  | tail _ edge ih => exact Reach.tail ih (HighStep.engineSecond _ _ _ _ _ edge)

def initialHigh {S : Type} (memory : S) (owed : Bool) : HighState S :=
  ⟨.clean (if owed then .both else .firstOnly) .normal, ⟨memory, [], 0⟩⟩

def initialLow {S : Type} (memory : S) (owed : Bool) : LowState S :=
  ⟨.at (.callFirst .normal), ⟨memory, [], 0⟩, owed⟩

theorem initial_relation {S : Type} (memory : S) (owed : Bool) :
    initialLow memory owed = compile (initialHigh memory owed) := by
  cases owed <;> rfl

theorem low_bad_no_next {S : Type} (runner : Command → S → Result Reply S) (plan : Plan)
    (state : LowState S) (bad : LowBad state) : lowNext runner plan state = none := by
  cases state with
  | mk control data owed =>
    cases control with
    | «at» pc => exact False.elim bad
    | done mode => exact False.elim bad
    | rejected => exact False.elim bad
    | running field phase normal unwind =>
      cases phase <;> simp_all [LowBad, lowNext, EffectfulDestructor.next]

theorem low_bad_terminal {S : Type} (runner : Command → S → Result Reply S) (plan : Plan)
    {before after : LowState S} (bad : LowBad before) (edge : LowStep runner plan before after) : False := by
  have successor := low_step_equation runner plan edge
  rw [low_bad_no_next runner plan before bad] at successor
  cases successor

private theorem safe_before_deterministic_edge {X : Type} (relation : X → X → Prop) (bad : X → Prop)
    (deterministic : ∀ {before first second}, relation before first → relation before second → first = second)
    (badTerminal : ∀ {before after}, bad before → relation before after → False)
    {before after : X} (edge : relation before after) (safe : NoUB relation bad after) :
    NoUB relation bad before := by
  apply invariant_noUB (Invariant := fun reached => reached = before ∨ Reach relation after reached) (Or.inl rfl)
  · intro current successor member step
    cases member with
    | inl same =>
      subst current
      have same : after = successor := deterministic edge step
      subst successor
      exact Or.inr (Reach.refl _)
    | inr path => exact Or.inr (Reach.tail path step)
  · intro reached member
    cases member with
    | inl same => subst reached; exact fun invalid => badTerminal invalid edge
    | inr path => exact safe reached path

/-- A terminating witness proves safety here because determinism rules out a
different bad branch and badness is terminal. Without these premises, a single
successful path would not justify universal finite-prefix safety. -/
theorem completed_path_safe {X : Type} (relation : X → X → Prop) (bad : X → Prop)
    (deterministic : ∀ {before first second}, relation before first → relation before second → first = second)
    (badTerminal : ∀ {before after}, bad before → relation before after → False)
    {before after : X} (path : Reach relation before after) :
    NoUB relation bad after → NoUB relation bad before := by
  induction path with
  | refl => intro safe; exact safe
  | tail path edge ih =>
    intro safe
    exact ih (safe_before_deterministic_edge relation bad deterministic badTerminal edge safe)

theorem low_done_safe {S : Type} (runner : Command → S → Result Reply S) (plan : Plan)
    (mode : Mode) (data : Data S) (owed : Bool) :
    NoUB (LowStep runner plan) LowBad ⟨.done mode, data, owed⟩ := by
  apply invariant_noUB (Invariant := fun state : LowState S => state.control = .done mode) rfl
  · intro before after control edge
    have stopped : lowNext runner plan before = none := by simp [lowNext, control]
    have successor := low_step_equation runner plan edge
    rw [stopped] at successor
    cases successor
  · intro reached control
    simp [LowBad, control]

namespace Concrete

open EffectfulDestructor.Concrete MemoryPermissions.Fixtures

def plan (firstExit : Exit) : Plan :=
  ⟨(fun field => match field with | .first => pointer0 | .second => pointer1), firstExit⟩

def finalMode : Exit → Mode | .returned => .normal | .unwound => .unwinding

def startData (first second : Fin 256) : Data Coupled := ⟨pair first second, [], 0⟩

def firstData (first second : Fin 256) (firstExit : Exit) : Data Coupled :=
  completedData ((startData first second).record (.entered .first))
    (pair first second) (firstWritten first second) .first first firstExit

def secondEntryData (first second : Fin 256) (firstExit : Exit) : Data Coupled :=
  (firstData first second firstExit).record (.entered .second)

def bothData (first second : Fin 256) (firstExit : Exit) : Data Coupled :=
  completedData (secondEntryData first second firstExit) (firstWritten first second)
    (bothWritten first second) .second second .returned

theorem first_completed_high (first second : Fin 256) (firstExit : Exit) (owed : Bool) :
    Reach (HighStep runCoupled (plan firstExit)) (initialHigh (pair first second) owed)
      ⟨.first (exitPhase firstExit) owed .normal, firstData first second firstExit⟩ := by
  have entered : Reach (HighStep runCoupled (plan firstExit)) (initialHigh (pair first second) owed)
      ⟨.first .read owed .normal, (startData first second).record (.entered .first)⟩ := by
    cases owed with
    | false => exact one (HighStep.enterFirst _ _)
    | true => exact one (HighStep.enterBoth _ _)
  exact entered.trans (first_engine_path runCoupled (plan firstExit) owed .normal
    (effectful_call runCoupled pointer0 .first firstExit
      ((startData first second).record (.entered .first))
      (pair first second) (firstWritten first second) first
      (first_read first second) (first_write first second)))

theorem second_entry_high (first second : Fin 256) (firstExit : Exit) :
    Reach (HighStep runCoupled (plan firstExit)) (initialHigh (pair first second) true)
      ⟨.second .read (finalMode firstExit), secondEntryData first second firstExit⟩ := by
  have completed := first_completed_high first second firstExit true
  cases firstExit with
  | returned =>
    exact completed.trans ((one (HighStep.returnedFirst _ _ _)).trans
      (one (HighStep.enterSecond _ _)))
  | unwound =>
    exact completed.trans ((one (HighStep.unwoundFirst _ _)).trans
      (one (HighStep.enterSecond _ _)))

/-- Both first outcomes enter the second destructor with the same updated
first memory; unwind does not roll back a write performed before panic. -/
theorem second_entry_low (first second : Fin 256) (firstExit : Exit) :
    Reach (LowStep runCoupled (plan firstExit)) (initialLow (pair first second) true)
      (compile ⟨.second .read (finalMode firstExit), secondEntryData first second firstExit⟩) :=
  compiled_reachable runCoupled (plan firstExit) (second_entry_high first second firstExit)

theorem second_entry_preserves_first_write (first second : Fin 256) (firstExit : Exit) :
    (compile (⟨.second .read (finalMode firstExit), secondEntryData first second firstExit⟩ : HighState Coupled)).data.memory =
      firstWritten first second ∧
    (secondEntryData first second firstExit).engineCost = 4 ∧
    MiniRustReference.load (secondEntryData first second firstExit).memory.memory pointer0 1 1 =
      .ok ([byte (increment first)], (firstWritten first second).memory) := by
  refine ⟨rfl, ?_, first_write_still_present_at_second_entry first second⟩
  simp [secondEntryData, firstData, startData, completedData, Data.record, Data.emit, Data.emitWith]

theorem pair_completed_high (first second : Fin 256) (firstExit : Exit) :
    Reach (HighStep runCoupled (plan firstExit)) (initialHigh (pair first second) true)
      ⟨.done (finalMode firstExit), (bothData first second firstExit).record (.finished (finalMode firstExit))⟩ := by
  have secondCall := second_engine_path runCoupled (plan firstExit) (finalMode firstExit)
    (effectful_call runCoupled pointer1 .second .returned (secondEntryData first second firstExit)
      (firstWritten first second) (bothWritten first second) second
      (second_read first second) (second_write first second))
  exact (second_entry_high first second firstExit).trans
    (secondCall.trans ((one (HighStep.returnedSecond _ _)).trans (one (HighStep.finish _ _))))

theorem pair_completed_low (first second : Fin 256) (firstExit : Exit) :
    Reach (LowStep runCoupled (plan firstExit)) (initialLow (pair first second) true)
      ⟨.done (finalMode firstExit), (bothData first second firstExit).record (.finished (finalMode firstExit)), false⟩ :=
  compiled_reachable runCoupled (plan firstExit) (pair_completed_high first second firstExit)

theorem final_payloads_and_engineCost (first second : Fin 256) (firstExit : Exit) :
    (bothData first second firstExit).memory = bothWritten first second ∧
    (bothData first second firstExit).engineCost = 8 ∧
    MiniRustReference.load (bothData first second firstExit).memory.memory pointer0 1 1 =
      .ok ([byte (increment first)], (bothWritten first second).memory) ∧
    MiniRustReference.load (bothData first second firstExit).memory.memory pointer1 1 1 =
      .ok ([byte (increment second)], (bothWritten first second).memory) := by
  refine ⟨rfl, ?_, (both_payloads_updated first second).1, (both_payloads_updated first second).2⟩
  simp [bothData, secondEntryData, firstData, startData, completedData,
    Data.record, Data.emit, Data.emitWith]

theorem suppressed_second_completed_high (first second : Fin 256) (firstExit : Exit) :
    Reach (HighStep runCoupled (plan firstExit)) (initialHigh (pair first second) false)
      ⟨.done (finalMode firstExit), (firstData first second firstExit).record (.finished (finalMode firstExit))⟩ := by
  have completed := first_completed_high first second firstExit false
  cases firstExit with
  | returned =>
    exact completed.trans ((one (HighStep.returnedFirst _ _ _)).trans (one (HighStep.finish _ _)))
  | unwound =>
    exact completed.trans ((one (HighStep.unwoundFirst _ _)).trans (one (HighStep.finish _ _)))

theorem suppressed_second_completed_low (first second : Fin 256) (firstExit : Exit) :
    Reach (LowStep runCoupled (plan firstExit)) (initialLow (pair first second) false)
      ⟨.done (finalMode firstExit), (firstData first second firstExit).record (.finished (finalMode firstExit)), false⟩ :=
  compiled_reachable runCoupled (plan firstExit) (suppressed_second_completed_high first second firstExit)

theorem suppressed_second_unchanged (first second : Fin 256) (firstExit : Exit) :
    MiniRustReference.load (firstData first second firstExit).memory.memory pointer1 1 1 =
      .ok ([byte second], (firstWritten first second).memory) := rfl

/-- An explicit two-distinct-byte normal/unwind discriminator, alongside the
parametric families above. It is not an experiment over every Rust program. -/
theorem distinct_payload_normal_and_unwind :
    (21 : Fin 256) ≠ (41 : Fin 256) ∧
    Reach (LowStep runCoupled (plan .returned)) (initialLow (pair 21 41) true)
      ⟨.done .normal, (bothData 21 41 .returned).record (.finished .normal), false⟩ ∧
    Reach (LowStep runCoupled (plan .unwound)) (initialLow (pair 21 41) true)
      ⟨.done .unwinding, (bothData 21 41 .unwound).record (.finished .unwinding), false⟩ :=
  ⟨by decide, pair_completed_low 21 41 .returned, pair_completed_low 21 41 .unwound⟩

theorem pair_low_safe (first second : Fin 256) (firstExit : Exit) :
    NoUB (LowStep runCoupled (plan firstExit)) LowBad (initialLow (pair first second) true) :=
  completed_path_safe (LowStep runCoupled (plan firstExit)) LowBad
    (low_step_deterministic runCoupled (plan firstExit))
    (low_bad_terminal runCoupled (plan firstExit)) (pair_completed_low first second firstExit)
    (low_done_safe runCoupled (plan firstExit) (finalMode firstExit)
      ((bothData first second firstExit).record (.finished (finalMode firstExit))) false)

theorem pair_high_safe (first second : Fin 256) (firstExit : Exit) :
    NoUB (HighStep runCoupled (plan firstExit)) HighBad (initialHigh (pair first second) true) :=
  safety_transfer runCoupled (plan firstExit) (initialHigh (pair first second) true)
    (pair_low_safe first second firstExit)

theorem suppressed_second_low_safe (first second : Fin 256) (firstExit : Exit) :
    NoUB (LowStep runCoupled (plan firstExit)) LowBad (initialLow (pair first second) false) :=
  completed_path_safe (LowStep runCoupled (plan firstExit)) LowBad
    (low_step_deterministic runCoupled (plan firstExit))
    (low_bad_terminal runCoupled (plan firstExit)) (suppressed_second_completed_low first second firstExit)
    (low_done_safe runCoupled (plan firstExit) (finalMode firstExit)
      ((firstData first second firstExit).record (.finished (finalMode firstExit))) false)

end Concrete

/-- Mutant relations add the indicated erroneous handler edge to ordinary CFG
steps. A witnessed mutant path suffices to refute the boundary relation; these
definitions do not claim that ordinary unwinding performs either behavior. -/
inductive RollbackStep {S : Type} (runner : Command → S → Result Reply S) (plan : Plan) (saved : S) :
    LowState S → LowState S → Prop where
  | ordinary {before after} (edge : LowStep runner plan before after) :
      RollbackStep runner plan saved before after
  | rollback {data normal unwind owed} :
      RollbackStep runner plan saved ⟨.running .first .unwound normal unwind, data, owed⟩
        ⟨.at unwind, { data with memory := saved }, owed⟩

inductive RetryStep {S : Type} (runner : Command → S → Result Reply S) (plan : Plan) :
    LowState S → LowState S → Prop where
  | ordinary {before after} (edge : LowStep runner plan before after) : RetryStep runner plan before after
  | retry {data normal unwind owed} :
      RetryStep runner plan ⟨.running .first .unwound normal unwind, data, owed⟩
        ⟨.at (.callFirst .unwinding), data, owed⟩

private theorem reach_map {S : Type} {first second : S → S → Prop}
    (embed : ∀ {before after}, first before after → second before after)
    {before after : S} (path : Reach first before after) : Reach second before after := by
  induction path with
  | refl => exact Reach.refl _
  | tail _ edge ih => exact Reach.tail ih (embed edge)

namespace Negative

open EffectfulDestructor.Concrete MemoryPermissions.Fixtures TwoCleanup.Concrete

def rolledBack : Data Coupled :=
  { firstData 21 41 .unwound with memory := pair 21 41 }

theorem rollback_reaches_second :
    Reach (RollbackStep runCoupled (plan .unwound) (pair 21 41)) (initialLow (pair 21 41) true)
      ⟨.running .second .read (.exit .unwinding) .reject,
        rolledBack.record (.entered .second), false⟩ := by
  have ordinary : Reach (LowStep runCoupled (plan .unwound)) (initialLow (pair 21 41) true)
      (compile ⟨.first .unwound true .normal, firstData 21 41 .unwound⟩) :=
    compiled_reachable runCoupled (plan .unwound) (first_completed_high 21 41 .unwound true)
  have start : Reach (RollbackStep runCoupled (plan .unwound) (pair 21 41))
      (initialLow (pair 21 41) true)
      (compile ⟨.first .unwound true .normal, firstData 21 41 .unwound⟩) :=
    reach_map (fun edge => RollbackStep.ordinary edge) ordinary
  exact start.trans (Reach.tail (Reach.tail (Reach.tail (one RollbackStep.rollback)
    (RollbackStep.ordinary (LowStep.testTrue rfl)))
    (RollbackStep.ordinary (LowStep.clear rfl))) (RollbackStep.ordinary (LowStep.invoke rfl)))

def peekFirst (memory : Coupled) : MiniRustReference.Byte :=
  match memory.memory.allocations 0 with | none => .uninit | some allocation => allocation.data 0

/-- This refutes the selected exact modeled-state relation. The Rust fixture's
second destructor reads only its own payload; this query is not an actual Rust
runtime observation or a theorem permitting access to an object after Drop.
No claim that rollback is an invalid Rust optimization of that fixture follows. -/
theorem rollback_changes_second_entry :
    (rolledBack.record (.entered .second)).memory ≠ (secondEntryData 21 41 .unwound).memory := by
  intro same
  have different : peekFirst (rolledBack.record (.entered .second)).memory ≠
      peekFirst (secondEntryData 21 41 .unwound).memory := by decide
  exact different (congrArg peekFirst same)

theorem retry_reenters_first :
    Reach (RetryStep runCoupled (plan .unwound)) (initialLow (pair 21 41) true)
      ⟨.running .first .read (.testSecond .unwinding) .reject,
        (firstData 21 41 .unwound).record (.entered .first), true⟩ := by
  have ordinary : Reach (LowStep runCoupled (plan .unwound)) (initialLow (pair 21 41) true)
      (compile ⟨.first .unwound true .normal, firstData 21 41 .unwound⟩) :=
    compiled_reachable runCoupled (plan .unwound) (first_completed_high 21 41 .unwound true)
  have start : Reach (RetryStep runCoupled (plan .unwound))
      (initialLow (pair 21 41) true)
      (compile ⟨.first .unwound true .normal, firstData 21 41 .unwound⟩) :=
    reach_map (fun edge => RetryStep.ordinary edge) ordinary
  exact start.trans (Reach.tail (one RetryStep.retry) (RetryStep.ordinary (LowStep.invoke rfl)))

def firstEntries : List Event → Nat
  | [] => 0
  | .entered .first :: rest => firstEntries rest + 1
  | _ :: rest => firstEntries rest

theorem retry_duplicates_entry_event :
    firstEntries ((firstData 21 41 .unwound).record (.entered .first)).events = 2 ∧
    firstEntries (secondEntryData 21 41 .unwound).events = 1 := ⟨rfl, rfl⟩

end Negative

#print axioms simulation
#print axioms safety_transfer
#print axioms compiled_reachable
#print axioms boundary_data
#print axioms low_step_deterministic
#print axioms low_bad_terminal
#print axioms completed_path_safe
#print axioms Concrete.second_entry_high
#print axioms Concrete.second_entry_low
#print axioms Concrete.second_entry_preserves_first_write
#print axioms Concrete.pair_completed_high
#print axioms Concrete.pair_completed_low
#print axioms Concrete.final_payloads_and_engineCost
#print axioms Concrete.suppressed_second_completed_low
#print axioms Concrete.suppressed_second_unchanged
#print axioms Concrete.distinct_payload_normal_and_unwind
#print axioms Concrete.pair_low_safe
#print axioms Concrete.pair_high_safe
#print axioms Concrete.suppressed_second_low_safe
#print axioms Negative.rollback_reaches_second
#print axioms Negative.rollback_changes_second_entry
#print axioms Negative.retry_reenters_first
#print axioms Negative.retry_duplicates_entry_event

end AnnealResearch.TwoCleanup
