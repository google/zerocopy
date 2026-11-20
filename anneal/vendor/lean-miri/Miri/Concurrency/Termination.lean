

/-!
# Miri termination and reporting categories

This is the pinned `diagnostics.rs::TerminationInfo` classification boundary.
It distinguishes program exit, abnormal termination, user interruption,
unsupported operations, UB reports and deadlock
reports. `report_result` labels only DataRace, StackedBorrowsUb, and
TreeBorrowsUb as UB among these machine-stop variants. This is a reporting
taxonomy, not a proof that a program is safe or a model of all interpreter
errors.
-/
namespace Miri.Concurrency

/-- The machine-stop variants in pinned Miri's `TerminationInfo`.
Diagnostic-only payloads are retained as strings; pointer/span/history fields
do not affect the `report_result` category. -/
inductive TerminationInfo where
  | exit (exitCode : Int) (leakCheck : Bool)
  | abort (message : String)
  | interrupted
  | unsupportedInIsolation (message : String)
  | stackedBorrowsUb (message : String)
  | treeBorrowsUb (title : String)
  | int2PtrWithStrictProvenance
  | globalDeadlock
  | localDeadlock
  | multipleSymbolDefinitions (linkName : String)
  | symbolShimClashing (linkName : String)
  | dataRace (involvesNonAtomic : Bool)
  | unsupportedForeignItem (item : String)
  deriving DecidableEq, Repr

/-- Observable category used by `report_result`; diagnostic rendering details
and spans are deliberately outside this classification. -/
inductive TerminationReport where
  | regularExit (exitCode : Int) (leakCheck : Bool)
  | abnormalTermination
  | interrupted
  | unsupportedOperation
  | undefinedBehavior
  | globalDeadlock
  | localDeadlock
  | otherMachineStop
  deriving DecidableEq, Repr

namespace TerminationInfo

/-- Classification from the pinned `diagnostics.rs::report_result` match. -/
def report : TerminationInfo → TerminationReport
  | .exit code leaks => .regularExit code leaks
  | .abort _ => .abnormalTermination
  | .interrupted => .interrupted
  | .unsupportedInIsolation _ | .int2PtrWithStrictProvenance
  | .unsupportedForeignItem _ => .unsupportedOperation
  | .stackedBorrowsUb _ | .treeBorrowsUb _ | .dataRace _ => .undefinedBehavior
  | .globalDeadlock => .globalDeadlock
  | .localDeadlock => .localDeadlock
  | .multipleSymbolDefinitions _ | .symbolShimClashing _ => .otherMachineStop

/-- Only actual borrow-checker UB and data-race termination variants receive
the `Undefined Behavior` report label in `report_result`. -/
def isUbReport (info : TerminationInfo) : Bool :=
  info.report == .undefinedBehavior

@[simp] theorem deadlocks_are_not_ub (info : TerminationInfo)
    (h : info = .globalDeadlock ∨ info = .localDeadlock) :
    info.isUbReport = false := by
  rcases h with h | h <;> simp [isUbReport, report, h]

@[simp] theorem abort_is_not_ub (message : String) :
    (TerminationInfo.abort message).isUbReport = false := by
  rfl

@[simp] theorem unsupported_is_not_ub (message : String) :
    (TerminationInfo.unsupportedInIsolation message).isUbReport = false := by
  rfl

end TerminationInfo

end Miri.Concurrency
