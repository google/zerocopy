import Lean
import ToyCoalesce.Staging

/-! Evaluation tactics for concrete programs over a symbolic layout (proof automation; no definitions). -/

namespace Toy.Coalesce

open Lean Meta Elab Tactic in
/-- Case-split on the condition of the first closed `if` in the goal. -/
elab "case_ite" : tactic => do
  let g ← instantiateMVars (← getMainTarget)
  let cond? := g.find? fun t => t.isAppOfArity ``ite 5 && !(t.getArg! 1).hasLooseBVars &&
    ((t.getArg! 1).find? (fun u => u.isAppOfArity ``ite 5)).isNone
  match cond? with
  | some t =>
    let c ← Term.exprToSyntax (t.getArg! 1)
    evalTactic (← `(tactic| by_cases hcase : $c))
  | none => throwError "case_ite: no closed if-then-else in the goal"

/-- Unfold the interpreter on a concrete program, then split on the remaining layout-dependent
conditions. -/
macro "run_eval" : tactic => `(tactic| (
  simp [outcome, run, Prog.code, execTop, execStmt, execBasic, allocate, liveOthers, layoutOK, Prog.nloc,
    Prog.size, St.init, writeCells, writeCellsK, resetCells, St.wr, St.logAcc, resolvePlace,
    evalOp, readCells, St.fail, St.emit, List.range, List.range.loop, List.filter, cmpOp, Val.addr?, Val.obs,
    evalOps, Disj, Operand.len, deallocate, writeInOrder, execCallee, Prog.fn] at *
  repeat (case_ite <;> (try simp_all) <;> (try omega))
  all_goals (try omega)))

/-- Evaluate the access log of a concrete program (layout independent) and decide a predicate on
it. -/
macro "log_eval" : tactic => `(tactic| (
  simp [run, Prog.code, execTop, execStmt, execBasic, allocate, liveOthers, Prog.nloc,
    Prog.size, St.init, writeCells, writeCellsK, resetCells, St.wr, St.logAcc, resolvePlace,
    evalOp, readCells, St.fail, St.emit, List.range, List.range.loop, List.filter, cmpOp,
    Val.addr?, Val.obs, evalOps, Operand.len, deallocate, writeInOrder, execCallee, Prog.fn]
  all_goals decide))

/-- Unfold coalescing and staging of a concrete program. -/
macro "coalesce_simp" : tactic => `(tactic| simp [coalesce, single, Forest.roots, nubNat,
  Forest.root, Forest.resolve, Forest.resolveF, Forest.parentOf, Forest.coalesceStmt,
  Forest.inClass, Stmt.mapPlaces, Operand.mapPlaces, Forest.mapPlace, Forest.offset, stage,
  stageList, NeedsStaging, Operand.mayOverlap, WindowsDisjoint, Prog.nloc, calleeNoStaging,
  NeedsStagingParam, Operand.mayOverlapParam, Place.paramSplit] at *)

end Toy.Coalesce
