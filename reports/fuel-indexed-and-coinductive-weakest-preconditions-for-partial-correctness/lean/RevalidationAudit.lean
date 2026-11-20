/-
# Revalidation audit (not part of the `ToyFuelWP` library target)

Run from the `lean/` directory after `lake build`:

    lake env lean RevalidationAudit.lean

For every declaration of the library it prints one line
`AXIOMS <name> <axioms>` (Lean's `collectAxioms`, the data behind
`#print axioms`). For every Lean name referenced by `results.json` it prints
one line `STATEMENT <json>` with the `repr` of the declaration's type and the
sorted closure: for every library constant reachable from that type, its
name, the `repr` of its type and, unless it is a theorem, the `repr` of its
value. The SHA-256 of the type `repr` is the statement hash, and the SHA-256
of the closure lines joined by newlines is the closure hash, as recorded in
`audit/statements.json`.
-/
import Lean
import ToyFuelWP

open Lean Elab Command

namespace RevalidationAudit

private def referenced : List Name := [
  `Toy.FuelWP.allRunsEventually_isOut_iff_not_wpGfp_false,
  `Toy.FuelWP.allRunsEventually_isOut_iff_wpLfp_isOut,
  `Toy.FuelWP.allRunsEventually_isOut_not_partial_wp_expressible,
  `Toy.FuelWP.allRunsEventually_not_partial_wp_of_divergent_violation,
  `Toy.FuelWP.alwaysDiverges_neg_spinOrExit,
  `Toy.FuelWP.alwaysDiverges_satisfies_every_partial_wp_and_no_total_wp,
  `Toy.FuelWP.chainSys_fuel_per_state_not_uniform,
  `Toy.FuelWP.countdownSys_start_wpLfp,
  `Toy.FuelWP.countdown_exists_wpFuelTotal_iff_wpLfp_fails,
  `Toy.FuelWP.countdown_wpLfp_without_uniform_fuel,
  `Toy.FuelWP.deterministic_pos_termBranch,
  `Toy.FuelWP.done_allRunsEventually_false_expressible,
  `Toy.FuelWP.done_not_every_partial_wp,
  `Toy.FuelWP.done_some_total_wp,
  `Toy.FuelWP.em_of_disjunctive_adequacy,
  `Toy.FuelWP.exists_wpFuelTotal_iff_wpLfp_ofStepFn,
  `Toy.FuelWP.exists_wpFuelTotal_iff_wpLfp_of_deterministic,
  `Toy.FuelWP.exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching,
  `Toy.FuelWP.exists_wpFuelTotal_of_wpGfp_of_not_hasInfiniteRun_of_finitelyBranchingFrom,
  `Toy.FuelWP.exists_wpFuelTotal_of_wpLfp_of_deterministic_of_decidable_terminal,
  `Toy.FuelWP.exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom,
  `Toy.FuelWP.fanToStuckSys_angelic_forall_fuel_not_gfp,
  `Toy.FuelWP.finitelyBranchingFrom_pos_countdown_count,
  `Toy.FuelWP.finitelyBranching_neg_countdown,
  `Toy.FuelWP.fixed_fuel_wpFuel_not_imp_wpGfp,
  `Toy.FuelWP.forall_wpFuel_iff_wpGfp,
  `Toy.FuelWP.forall_wpGfp_iff_alwaysDiverges,
  `Toy.FuelWP.hasInfiniteRun_refutes_every_total_wp,
  `Toy.FuelWP.loopSys_wpLfp_ne_wpGfp,
  `Toy.FuelWP.loop_allRunsEventually_true_expressible,
  `Toy.FuelWP.loop_finitelyBranching_no_total_fuel,
  `Toy.FuelWP.lpo_of_exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching,
  `Toy.FuelWP.lpo_of_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom,
  `Toy.FuelWP.lpo_of_koenig_form,
  `Toy.FuelWP.markov_of_wpLfp_iff_wpGfp_and_not_hasInfiniteRun,
  `Toy.FuelWP.nonvacuity_adequacy,
  `Toy.FuelWP.nonvacuity_allRunsEventually_isOut_nontrivial,
  `Toy.FuelWP.nonvacuity_alwaysDiverges,
  `Toy.FuelWP.nonvacuity_coinduction_induction,
  `Toy.FuelWP.nonvacuity_divergent_violation,
  `Toy.FuelWP.nonvacuity_exists_wpFuelTotal_iff_wpLfp_corollaries,
  `Toy.FuelWP.nonvacuity_exists_wpFuelTotal_iff_wpLfp_ofStepFn,
  `Toy.FuelWP.nonvacuity_exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom,
  `Toy.FuelWP.nonvacuity_forall_wpFuel_and_wpGfp,
  `Toy.FuelWP.nonvacuity_hasInfiniteRun,
  `Toy.FuelWP.nonvacuity_koenig_form,
  `Toy.FuelWP.nonvacuity_wpFuelTotal,
  `Toy.FuelWP.nonvacuity_wpFuel_antitone,
  `Toy.FuelWP.nonvacuity_wpFuel_iff_forall_reach_lt,
  `Toy.FuelWP.nonvacuity_wpLfp_iff_wpGfp_and_not_hasInfiniteRun,
  `Toy.FuelWP.not_partial_wp_expressible_of_alwaysDiverges_of_not,
  `Toy.FuelWP.not_wpGfp_not_iff_wpLfp_of_deterministic_of_not_stuck,
  `Toy.FuelWP.runEndOk_iff_not_stuck,
  `Toy.FuelWP.runEndOk_iff_or,
  `Toy.FuelWP.spinOrEmitLoopSys_allRunsEventually_not_wp_expressible,
  `Toy.FuelWP.spinOrExitSys_conjugate_ne_wpLfp,
  `Toy.FuelWP.spinOrExitSys_finitelyBranching_not_deterministic,
  `Toy.FuelWP.spinOrOutSys_spin_every_partial_wp_but_never_outputs,
  `Toy.FuelWP.startSpinOutSys_allRunsEventually_not_partial_wp_expressible,
  `Toy.FuelWP.startSpinOutSys_wpGfp_iff_allRunsEventually_off_spin,
  `Toy.FuelWP.stuckSys_conjugate_ne_wpLfp,
  `Toy.FuelWP.stuckSys_no_total_no_partial,
  `Toy.FuelWP.stuckSys_not_wpGfp_not_wpFuel_one,
  `Toy.FuelWP.stuck_finitelyBranching_no_infinite_run_no_total_fuel,
  `Toy.FuelWP.wpFuelTotal_iff_wpFuel_and_no_reach,
  `Toy.FuelWP.wpFuelTotal_monotone,
  `Toy.FuelWP.wpFuelTotal_monotone_drop_h,
  `Toy.FuelWP.wpFuelTotal_neg_chain_short,
  `Toy.FuelWP.wpFuelTotal_neg_zero_done,
  `Toy.FuelWP.wpFuelTotal_not_antitone_done,
  `Toy.FuelWP.wpFuelTotal_propSys_one_iff_not_not,
  `Toy.FuelWP.wpFuel_antitone,
  `Toy.FuelWP.wpFuel_antitone_drop_h,
  `Toy.FuelWP.wpFuel_iff_forall_reach_lt,
  `Toy.FuelWP.wpFuel_not_monotone_stuck,
  `Toy.FuelWP.wpFuel_of_wpGfp,
  `Toy.FuelWP.wpFuel_pos_zero_stuck,
  `Toy.FuelWP.wpGfp_adequacy,
  `Toy.FuelWP.wpGfp_adequacy_drop_h,
  `Toy.FuelWP.wpGfp_and_not_hasInfiniteRun_of_wpLfp,
  `Toy.FuelWP.wpGfp_coinduction,
  `Toy.FuelWP.wpGfp_coinduction_drop_hX,
  `Toy.FuelWP.wpGfp_coinduction_drop_hs,
  `Toy.FuelWP.wpGfp_false_iff_alwaysDiverges,
  `Toy.FuelWP.wpGfp_iff_forall_reach_runEndOk,
  `Toy.FuelWP.wpGfp_of_forall_reach_runEndOk,
  `Toy.FuelWP.wpGfp_of_forall_reach_runEndOk_drop_h,
  `Toy.FuelWP.wpGfp_of_forall_wpFuel,
  `Toy.FuelWP.wpGfp_of_wpFuelTotal,
  `Toy.FuelWP.wpGfp_pos_loop_false,
  `Toy.FuelWP.wpGfp_unfold,
  `Toy.FuelWP.wpLfp_iff_wpGfp_and_not_hasInfiniteRun,
  `Toy.FuelWP.wpLfp_induction,
  `Toy.FuelWP.wpLfp_induction_drop_hX,
  `Toy.FuelWP.wpLfp_induction_drop_hs,
  `Toy.FuelWP.wpLfp_of_exists_wpFuelTotal,
  `Toy.FuelWP.wpLfp_pos_chain,
  `Toy.FuelWP.wpLfp_unfold
]

private def inLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`ToyFuelWP).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inLib env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      closure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (n, _) in env.constants.toList do
    if inLib env n && !n.isInternal then
      let axs ← collectAxioms n
      lines := lines.push s!"AXIOMS {n} {axs.toList}"
  for l in lines.qsort (· < ·) do
    IO.println l
  for n in referenced do
    match env.find? n with
    | none => IO.println s!"MISSING {n}"
    | some ci =>
      let cl := closure env (ci.type.getUsedConstants.toList) {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      IO.println ("STATEMENT " ++ (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))]).compress)

end RevalidationAudit
