import Miri.Interpreter.TerminatorMachine

/-! Persistent source before_terminator counters/configuration without a second
monotonic clock. The clock-bearing Control is a transient view assembled from
these fields and the single actual runtime clock. -/
namespace Miri.Interpreter.TerminatorControl
structure Configuration where
  gcInterval : UInt32
  preemptionRateBits : UInt64
  checkedArithmetic : Bool
structure Counters where
  basicBlockCount : UInt64
  sinceGc : UInt32
  configuration : Configuration

def initial (config : Configuration) : Counters := ⟨0,0,config⟩
def view (counters : Counters) (clock : Clock.Monotonic Host) : TerminatorMachine.Control Host :=
  ⟨counters.basicBlockCount,counters.sinceGc,counters.configuration.gcInterval,clock,
    counters.configuration.preemptionRateBits,counters.configuration.checkedArithmetic⟩
def fromView (control : TerminatorMachine.Control Host) : Counters :=
  ⟨control.basicBlockCount,control.sinceGc,
    ⟨control.gcInterval,control.preemptionRateBits,control.checkedArithmetic⟩⟩
@[simp] theorem view_fromView (control : TerminatorMachine.Control Host) :
    view (fromView control) control.monotonic = control := by cases control; rfl
@[simp] theorem fromView_view (counters : Counters) (clock : Clock.Monotonic Host) :
    fromView (view counters clock) = counters := by cases counters; rfl
end Miri.Interpreter.TerminatorControl
