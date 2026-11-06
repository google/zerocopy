module
public import Lean.Elab.Tactic
public meta import Lean.Elab.Tactic
open Lean Meta Elab Tactic

public structure DiagnosticCell where
  value : Nat

/- Diagnostic-only reproduction. This does not patch or import a replacement for
   Kraken's tactic. A goal retains its local declaration after withLocalDecl exits. -/
elab "probe_message_context" : tactic => do
  let goal ← withLocalDeclD `detached_x (mkConst ``DiagnosticCell) fun x => do
    let value ← mkAppM ``DiagnosticCell.value #[x]
    let proposition ← mkEq value value
    return (← mkFreshExprMVar proposition).mvarId!
  let proposition ← goal.getType
  logInfo m!"Outside goal context: {proposition}"
  goal.withContext do
    logInfo m!"Inside goal context: {proposition}"

theorem diagnostic_only : True := by
  probe_message_context
  trivial

#print axioms diagnostic_only
