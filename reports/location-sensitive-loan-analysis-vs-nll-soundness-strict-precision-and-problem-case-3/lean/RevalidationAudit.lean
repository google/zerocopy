import Lean
import ToyLoanFlow

/-!
# Standalone revalidation audit (`ToyLoanFlow`)

Run from `lean/` after `lake build`:

    lake env lean RevalidationAudit.lean

Prints `LEANLIB_REVAL_JSON {...}` containing:
1. `decls`: every non-internal declaration in the `ToyLoanFlow` library together with the axioms
   reported by `Lean.collectAxioms`;
2. `stmts`: for each of the 112 declarations referenced in `results.json` and recorded in
   `audit/statements.json`, the `repr` of its kernel type (`type_repr`) and the sorted definition
   closure (`closure`, excluding theorem proof terms).
-/

open Lean Elab Command

private def revalRoots : List Name := [`ToyLoanFlow]

private def revalWanted : List Name := [
  `Toy.LoanFlow.Acc,
  `Toy.LoanFlow.Acyclic,
  `Toy.LoanFlow.Conflicts,
  `Toy.LoanFlow.Edges,
  `Toy.LoanFlow.Incl.holds_of_liveHolds,
  `Toy.LoanFlow.Incl.liveHolds_of_holds,
  `Toy.LoanFlow.Incl.liveHolds_to_nll,
  `Toy.LoanFlow.IsWalk,
  `Toy.LoanFlow.KillMode,
  `Toy.LoanFlow.LS.Accepts,
  `Toy.LoanFlow.LS.Holds,
  `Toy.LoanFlow.LS.LiveAccepts,
  `Toy.LoanFlow.LS.LiveHolds,
  `Toy.LoanFlow.LS.LiveLoanLive,
  `Toy.LoanFlow.LS.LoanLive,
  `Toy.LoanFlow.LS.SubAt,
  `Toy.LoanFlow.LSAccepts,
  `Toy.LoanFlow.LiveAt,
  `Toy.LoanFlow.Mutbl,
  `Toy.LoanFlow.NLL.Accepts,
  `Toy.LoanFlow.NLL.InRegion,
  `Toy.LoanFlow.NLL.InScope,
  `Toy.LoanFlow.NLLAccepts,
  `Toy.LoanFlow.Origin,
  `Toy.LoanFlow.Outcome,
  `Toy.LoanFlow.Outcome.isUB,
  `Toy.LoanFlow.Prog,
  `Toy.LoanFlow.RState,
  `Toy.LoanFlow.RState.get,
  `Toy.LoanFlow.RState.init,
  `Toy.LoanFlow.RState.set,
  `Toy.LoanFlow.Reach,
  `Toy.LoanFlow.ReachesUB,
  `Toy.LoanFlow.Rec,
  `Toy.LoanFlow.Safe,
  `Toy.LoanFlow.Sound.Inv,
  `Toy.LoanFlow.Sound.Uniq,
  `Toy.LoanFlow.Sound.WF,
  `Toy.LoanFlow.Sound.exec_ne_ub,
  `Toy.LoanFlow.Sound.inv_init,
  `Toy.LoanFlow.Sound.run_not_ub,
  `Toy.LoanFlow.Sound.step_inv,
  `Toy.LoanFlow.Stmt,
  `Toy.LoanFlow.Stmt.accesses,
  `Toy.LoanFlow.Stmt.defs,
  `Toy.LoanFlow.Stmt.uses,
  `Toy.LoanFlow.StmtWellTyped,
  `Toy.LoanFlow.VarMode,
  `Toy.LoanFlow.WellTyped,
  `Toy.LoanFlow.exec,
  `Toy.LoanFlow.gen,
  `Toy.LoanFlow.invalidate,
  `Toy.LoanFlow.invariantAt,
  `Toy.LoanFlow.killsAt,
  `Toy.LoanFlow.liveAccepts_of_wellTyped_of_nllAccepts,
  `Toy.LoanFlow.loanDst,
  `Toy.LoanFlow.loanOf,
  `Toy.LoanFlow.lsAccepts_not_safe_without_wellTyped,
  `Toy.LoanFlow.lsAccepts_of_lsNoKillAccepts,
  `Toy.LoanFlow.lsAccepts_of_nllAccepts_fails_without_wellTyped,
  `Toy.LoanFlow.lsAccepts_of_reachWellTyped_of_nllAccepts_fails,
  `Toy.LoanFlow.lsAccepts_of_wellTyped_of_nllAccepts,
  `Toy.LoanFlow.lsAccepts_of_wellTyped_of_nllAccepts_nonvacuous,
  `Toy.LoanFlow.lsAccepts_overwrite_iff_liveAccepts,
  `Toy.LoanFlow.lsAccepts_overwrite_iff_liveAccepts_nonvacuous,
  `Toy.LoanFlow.lsLoanLive_overwrite_iff_liveLoanLive,
  `Toy.LoanFlow.lsNoKillAccepts_of_wellTyped_of_nllAccepts_fails,
  `Toy.LoanFlow.nllAccepts_not_safe_without_wellTyped,
  `Toy.LoanFlow.pCopyThenUse,
  `Toy.LoanFlow.pCopyThenUseShr,
  `Toy.LoanFlow.pCopyThenUseShr_lsCopySrcKill_accepts,
  `Toy.LoanFlow.pCopyThenUseShr_not_lsAccepts,
  `Toy.LoanFlow.pCopyThenUseShr_wellTyped_lsCopySrcKillAccepts_not_safe,
  `Toy.LoanFlow.pCopyThenUse_lsCopySrcKill_accepts,
  `Toy.LoanFlow.pCopyThenUse_not_lsAccepts,
  `Toy.LoanFlow.pCopyThenUse_wellTyped_lsCopySrcKillAccepts_not_safe,
  `Toy.LoanFlow.pReassign,
  `Toy.LoanFlow.pReassign_r_dead_at_2,
  `Toy.LoanFlow.pReassign_wellTyped_safe_nllAccepts_lsAccepts_not_lsNoKillAccepts,
  `Toy.LoanFlow.pStoreSafe,
  `Toy.LoanFlow.pUnreachUntyped,
  `Toy.LoanFlow.pUntypedHolder,
  `Toy.LoanFlow.pUntypedStore,
  `Toy.LoanFlow.pVariance,
  `Toy.LoanFlow.pVariance_lsCov_accepts,
  `Toy.LoanFlow.pVariance_not_lsAccepts,
  `Toy.LoanFlow.pVariance_not_nllAccepts,
  `Toy.LoanFlow.pVariance_wellTyped_covAccepts_not_safe,
  `Toy.LoanFlow.pc3,
  `Toy.LoanFlow.pc3Loop,
  `Toy.LoanFlow.pc3Loop_safe,
  `Toy.LoanFlow.pc3Loop_wellTyped_safe_lsAccepts_not_nllAccepts,
  `Toy.LoanFlow.pc3NoReturn,
  `Toy.LoanFlow.pc3NoReturn_wellTyped_safe_nllAccepts_lsAccepts,
  `Toy.LoanFlow.pc3_loan0_at_insertion,
  `Toy.LoanFlow.pc3_wellTyped_safe_lsAccepts_not_nllAccepts,
  `Toy.LoanFlow.placeRead,
  `Toy.LoanFlow.placeWrite,
  `Toy.LoanFlow.refuted_result2_needs_kills,
  `Toy.LoanFlow.relate,
  `Toy.LoanFlow.run,
  `Toy.LoanFlow.safe_of_wellTyped_of_lsAccepts,
  `Toy.LoanFlow.safe_of_wellTyped_of_lsAccepts_nonvacuous,
  `Toy.LoanFlow.safe_of_wellTyped_of_lsCopySrcKillAccepts_fails,
  `Toy.LoanFlow.safe_of_wellTyped_of_lsCovAccepts_fails,
  `Toy.LoanFlow.safe_of_wellTyped_of_nllAccepts,
  `Toy.LoanFlow.safe_of_wellTyped_of_nllAccepts_nonvacuous,
  `Toy.LoanFlow.safe_of_wellTyped_of_nllCovAccepts_fails,
  `Toy.LoanFlow.thruRead,
  `Toy.LoanFlow.thruWrite,
  `Toy.LoanFlow.wellTyped_acyclic_not_safe,
  `Toy.LoanFlow.wellTyped_not_lsAccepts
]

private def revalInPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => revalRoots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

private partial def revalClosure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !revalInPkg env n then revalClosure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => revalClosure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      revalClosure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for (n, _) in env.constants.toList do
    if revalInPkg env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [
        ("name", toJson n.toString),
        ("axioms", toJson (axs.map Name.toString))
      ])
  let mut stmts : Array Json := #[]
  for n in revalWanted do
    match env.find? n with
    | none =>
      stmts := stmts.push (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)])
    | some ci =>
      let cl := revalClosure env (ci.type.getUsedConstants.toList) {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      stmts := stmts.push (Json.mkObj [
        ("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))
      ])
  IO.println ("LEANLIB_REVAL_JSON " ++
    (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
