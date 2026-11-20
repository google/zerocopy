import Lean
import ToyMonitor

/-!
# Revalidation audit for the `ToyMonitor` library

This file is not part of the library target. Run it after `lake build` with

    lake env lean RevalidationAudit.lean

For every declaration named in `results.json` (the list `wanted` below, identical to the
keys of `audit/statements.json`) it prints one line

    REVALIDATION_STMT {"name": ..., "axioms": [...], "type_repr": ..., "closure": [...]}

where

* `axioms` is the result of `Lean.collectAxioms` (the data shown by `#print axioms`);
* `type_repr` is `repr` of the declaration's type (its statement);
* `closure` is the sorted list of entries `c : repr(type)` (followed by
  ` := repr(value)` when `c` is not a theorem), one per constant of a `ToyMonitor`
  module reachable from the statement through types, definition bodies and
  constructors (theorem bodies are not followed).

The SHA-256 of `type_repr` and of the closure entries joined by newlines are the
`statement_sha256` and `closure_sha256` recorded in `audit/statements.json`.
-/

open Lean Elab Command

private def auditRoots : List Name := [`ToyMonitor]

private def wanted : List Name := [
  `Toy.Monitor.accepts_fpGreedy_call_C_C_skip_of_satisfies,
  `Toy.Monitor.accepts_fpGreedy_of_satisfies_of_disjPrecise,
  `Toy.Monitor.accepts_fpGreedy_of_satisfies_of_disjPrecise_nonvacuous,
  `Toy.Monitor.accepts_fpSearch_of_satisfies_of_precise,
  `Toy.Monitor.accepts_fpSearch_of_satisfies_of_precise_nonvacuous,
  `Toy.Monitor.accepts_imp_satisfiesBy_of_strategySound,
  `Toy.Monitor.accepts_imp_satisfiesBy_of_strategySound_nonvacuous,
  `Toy.Monitor.accepts_imp_satisfiesBy_of_unannotConfined,
  `Toy.Monitor.accepts_imp_satisfiesBy_of_unannotConfined_nonvacuous,
  `Toy.Monitor.accepts_strict_fpGreedy_iff_satisfies_of_disjPrecise,
  `Toy.Monitor.accepts_strict_fpSearch_iff_satisfies_call_C_C_skip,
  `Toy.Monitor.accepts_strict_fpSearch_iff_satisfies_of_precise,
  `Toy.Monitor.existsFootprintComplete_not_imp_precise,
  `Toy.Monitor.fpGreedyR_strategySound,
  `Toy.Monitor.fpGreedy_recoversEveryWitness_CFlip_not_disjPrecise,
  `Toy.Monitor.fpGreedy_recoversEveryWitness_of_disjPrecise,
  `Toy.Monitor.fpGreedy_recoversEveryWitness_of_disjPrecise_nonvacuous,
  `Toy.Monitor.fpGreedy_rejects_satisfying_run_imprecise_contract,
  `Toy.Monitor.fpGreedy_rejects_satisfying_run_precise_not_disjPrecise,
  `Toy.Monitor.fpGreedy_strategySound,
  `Toy.Monitor.fpGreedy_strategySound_nonvacuous,
  `Toy.Monitor.fpSearch_existsFootprintComplete,
  `Toy.Monitor.fpSearch_recoversEveryWitness_of_precise,
  `Toy.Monitor.fpSearch_recoversEveryWitness_of_precise_nonvacuous,
  `Toy.Monitor.fpSearch_rejects_satisfying_run_imprecise_contract,
  `Toy.Monitor.fpSearch_strategySound,
  `Toy.Monitor.fpSearch_strategySound_nonvacuous,
  `Toy.Monitor.monitorAux_sound,
  `Toy.Monitor.noLeakCheck_accepts_leaky_post,
  `Toy.Monitor.noLeakCheck_later_callee_inherits_leaked_byte,
  `Toy.Monitor.not_precise_C,
  `Toy.Monitor.not_recoversEveryWitness_fpGreedy_C,
  `Toy.Monitor.not_recoversEveryWitness_fpSearch_C,
  `Toy.Monitor.owned0_or_owned1_each_run_accepted_by_some_strategy,
  `Toy.Monitor.owned0_or_owned1_no_sound_strategy_accepts_both,
  `Toy.Monitor.owned0_or_owned1_no_sound_strategy_accepts_both_nonvacuous,
  `Toy.Monitor.owned0_or_owned1_unsound_strategy_accepts_both,
  `Toy.Monitor.precise_of_disjPrecise,
  `Toy.Monitor.precise_of_disjPrecise_nonvacuous,
  `Toy.Monitor.precise_of_recoversEveryWitness,
  `Toy.Monitor.precise_of_recoversEveryWitness_nonvacuous,
  `Toy.Monitor.read_unowned_rejected_and_unsatisfied,
  `Toy.Monitor.restrict_witnesses_sep,
  `Toy.Monitor.restrict_witnesses_sep_allows_unallocated_addrs,
  `Toy.Monitor.restrict_witnesses_sep_needs_sat,
  `Toy.Monitor.restrict_witnesses_sep_nonvacuous,
  `Toy.Monitor.satisfiesBy_imp_accepts,
  `Toy.Monitor.satisfiesBy_imp_accepts_nonvacuous,
  `Toy.Monitor.satisfies_frame,
  `Toy.Monitor.satisfies_frame_needs_not_mem,
  `Toy.Monitor.satisfies_frame_nonvacuous,
  `Toy.Monitor.satisfies_imp_satisfiesBy_of_recoversEveryWitness,
  `Toy.Monitor.satisfies_imp_satisfiesBy_of_recoversEveryWitness_nonvacuous,
  `Toy.Monitor.trusted_monitor_checks_nested_annotated_call,
  `Toy.Monitor.trusted_unannot_read_outside_footprint_accepted_heap_unchanged,
  `Toy.Monitor.trusted_unannot_write_outside_footprint_accepted,
  `Toy.Monitor.unsound_strategy_accepts_contract_violating_run,
  `Toy.Monitor.write_outside_frame_changes_byte
]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => auditRoots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inPkg env n then closure env rest acc else
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
  for n in wanted do
    match env.find? n with
    | none => IO.println ("REVALIDATION_MISSING " ++ n.toString)
    | some ci =>
      let axs ← collectAxioms n
      let cl := closure env (ci.type.getUsedConstants.toList) {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      IO.println ("REVALIDATION_STMT " ++ (Json.mkObj [("name", toJson n.toString),
        ("axioms", toJson (axs.map Name.toString)),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))]).compress)
