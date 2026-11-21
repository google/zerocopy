import Lean
import ToyDataflow

/-!
# Revalidation audit program (outside the `ToyDataflow` library target)

Run from the `lean/` directory after `lake build`:

    lake env lean RevalidationAudit.lean

For every Lean name referenced by `results.json` this prints

* `AXIOMS <name> [...]`: the axioms the declaration depends on (`Lean.collectAxioms`);
* `SIGNATURE <name>` followed by the pretty-printed signature (binders and statement);
* `STATEMENT_JSON {...}`: the `repr` of the statement (the declaration's type) and the
  sorted closure text: for every constant of the `ToyDataflow` library reachable from the
  statement, its name, the `repr` of its type and, unless it is a theorem, the `repr` of
  its value (theorem bodies are excluded, so proofs can change without changing hashes).

`support/revalidate.py` and the inline snippet in `REPORT.md` hash the `STATEMENT_JSON`
fields with SHA-256 and compare them with `audit/statements.json`.
-/

open Lean Elab Command Meta

namespace RevalidationAudit

def roots : List Name := [`ToyDataflow]

def wanted : List Name := [
  `Toy.Dataflow.IsLeastSolution.unique,
  `Toy.Dataflow.IsMOPAt.unique,
  `Toy.Dataflow.Lat.acc_of_heightLe,
  `Toy.Dataflow.Lat.leTrans_of_leRefl_leAntisymm_joinLeIff,
  `Toy.Dataflow.Walk.val_eq_foldl,
  `Toy.Dataflow.acc_strictly_weaker_than_heightLe,
  `Toy.Dataflow.assignXYZ_monotone,
  `Toy.Dataflow.assignXYZ_not_distributive,
  `Toy.Dataflow.assignYZ_distributive,
  `Toy.Dataflow.assignYZ_not_strict,
  `Toy.Dataflow.boolLat_heightLe_one,
  `Toy.Dataflow.boolLat_isJSL,
  `Toy.Dataflow.boolLat_not_heightLe_zero,
  `Toy.Dataflow.bvLat_heightLe,
  `Toy.Dataflow.bvLat_isJSL,
  `Toy.Dataflow.bvMustLat_isJSL,
  `Toy.Dataflow.cfg_empty_carrier_empty,
  `Toy.Dataflow.cfg_zero_empty,
  `Toy.Dataflow.copyBit0_distributive,
  `Toy.Dataflow.copyBit0_not_genKill,
  `Toy.Dataflow.copyXY_distributive,
  `Toy.Dataflow.cpDiamond_exists_isLeastSolution_mfp_x_top_ne_mop_x_const3,
  `Toy.Dataflow.cpDiamond_isLeastSolution,
  `Toy.Dataflow.cpDiamond_mfp_needs_least,
  `Toy.Dataflow.cpDiamond_mfp_x_top_ne_mop_x_const3,
  `Toy.Dataflow.cpDiamond_sameBranches_exact,
  `Toy.Dataflow.cpLat_heightLe,
  `Toy.Dataflow.cpLat_isJSL,
  `Toy.Dataflow.cyclic_exactness_on_unboundedChainsLat,
  `Toy.Dataflow.diamondExact_const_mem_needs_monotone,
  `Toy.Dataflow.diamondExact_const_mem_nonvacuous,
  `Toy.Dataflow.diamondExact_const_needs_nonempty_init,
  `Toy.Dataflow.diamondExact_iff_distributiveOnRealizable_of_monotone,
  `Toy.Dataflow.diamondExact_iff_distributive_of_acc_of_const_mem_of_nonempty,
  `Toy.Dataflow.diamondExact_iff_distributive_of_monotone_of_const_mem_of_nonempty,
  `Toy.Dataflow.diamondExact_iff_nonvacuous,
  `Toy.Dataflow.diamondExact_needs_distributiveOnRealizable,
  `Toy.Dataflow.diamondExact_needs_monotone,
  `Toy.Dataflow.diamondExact_not_exact_on_two_step_branches,
  `Toy.Dataflow.diamondExact_of_distributiveOnRealizable,
  `Toy.Dataflow.diamondExact_singleton_of_not_distributive,
  `Toy.Dataflow.diamond_entry_id_matters,
  `Toy.Dataflow.distributiveOnRealizable_of_diamondExact_of_monotone,
  `Toy.Dataflow.distributive_of_monotone_of_total,
  `Toy.Dataflow.exactness_corollaries_combined_counterexample,
  `Toy.Dataflow.exactness_corollaries_need_allReachable_or_strict,
  `Toy.Dataflow.exactness_holds_on_unboundedChainsLat,
  `Toy.Dataflow.exactness_needs_acc,
  `Toy.Dataflow.exactness_needs_distributive,
  `Toy.Dataflow.exactness_needs_least,
  `Toy.Dataflow.exactness_needs_unreachableStrict,
  `Toy.Dataflow.exactness_nonvacuous,
  `Toy.Dataflow.exists_exactness_combined_counterexamples,
  `Toy.Dataflow.exists_exactness_counterexamples,
  `Toy.Dataflow.exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict,
  `Toy.Dataflow.exists_isLeastSolution_counterexamples,
  `Toy.Dataflow.exists_isLeastSolution_of_monotone_of_acc,
  `Toy.Dataflow.exists_isMOPAt_of_acc,
  `Toy.Dataflow.fin4PreLat_law_profile,
  `Toy.Dataflow.finChainLat_heightLe,
  `Toy.Dataflow.finChainLat_isJSL,
  `Toy.Dataflow.genKill_distributive,
  `Toy.Dataflow.genKill_distributive_must,
  `Toy.Dataflow.genKill_exactness_needs_genKill_form,
  `Toy.Dataflow.genKill_exactness_needs_unreachable_gen_empty,
  `Toy.Dataflow.genKill_exactness_nonvacuous,
  `Toy.Dataflow.genKill_exists_exactness_combined_counterexamples,
  `Toy.Dataflow.genKill_exists_isLeastSolution_and_isMOPAt_of_unreachable_gen_empty,
  `Toy.Dataflow.genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty,
  `Toy.Dataflow.genKill_killOnly_strict_may_not_must,
  `Toy.Dataflow.genKill_must_strict_nonempty_kill_nonvacuous,
  `Toy.Dataflow.genKill_strict_iff,
  `Toy.Dataflow.genKill_strict_must_iff,
  `Toy.Dataflow.isEquationSolution_of_isLeastSolution_of_monotone,
  `Toy.Dataflow.isMOPAt_bot_of_not_reachable,
  `Toy.Dataflow.isMOPAt_of_isLeastSolution_of_distributive_of_allReachable,
  `Toy.Dataflow.isMOPAt_of_isLeastSolution_of_distributive_of_strict,
  `Toy.Dataflow.isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict,
  `Toy.Dataflow.isSolution_iff_eqRHS_le,
  `Toy.Dataflow.kildall_acc_has_no_uniform_fuel,
  `Toy.Dataflow.kildall_decidableRel_irrelevant,
  `Toy.Dataflow.kildall_eq_some_isLeastSolution_of_monotone_of_heightLe,
  `Toy.Dataflow.kildall_eq_some_isMOPAt_of_distributive_of_unreachableStrict_of_heightLe,
  `Toy.Dataflow.kildall_fuel_bound_attained,
  `Toy.Dataflow.kildall_isLeastSolution_of_monotone_of_eq_some,
  `Toy.Dataflow.kildall_isMOPAt_counterexamples,
  `Toy.Dataflow.kildall_isMOPAt_nonvacuous,
  `Toy.Dataflow.kildall_isSolution_of_eq_some,
  `Toy.Dataflow.kildall_isSome_of_heightLe,
  `Toy.Dataflow.kildall_needs_eq_some,
  `Toy.Dataflow.kildall_needs_heightLe,
  `Toy.Dataflow.kildall_needs_monotone,
  `Toy.Dataflow.kildall_nonvacuous,
  `Toy.Dataflow.monotone_of_diamondExact_of_acc_of_const_mem_of_nonempty,
  `Toy.Dataflow.monotone_of_distributive,
  `Toy.Dataflow.mop_le_of_isSolution_of_monotone,
  `Toy.Dataflow.natMaxLat_isJSL,
  `Toy.Dataflow.natMaxLat_not_acc,
  `Toy.Dataflow.natMaxLat_not_heightLe,
  `Toy.Dataflow.no_lat_violates_only_leTrans,
  `Toy.Dataflow.notAntisymmLat_law_profile,
  `Toy.Dataflow.notBotLat_law_profile,
  `Toy.Dataflow.notCFG_isLeastSolution_not_isEquationSolution,
  `Toy.Dataflow.notJoinLat_law_profile,
  `Toy.Dataflow.notReflLat_law_profile,
  `Toy.Dataflow.notTransLat_law_profile,
  `Toy.Dataflow.omegaLat_isJSL,
  `Toy.Dataflow.omegaLat_monotone_distributive,
  `Toy.Dataflow.omegaLat_not_acc,
  `Toy.Dataflow.omegaLat_total,
  `Toy.Dataflow.soundness_needs_isMOPAt,
  `Toy.Dataflow.soundness_needs_leTrans,
  `Toy.Dataflow.soundness_needs_monotone,
  `Toy.Dataflow.soundness_needs_solution,
  `Toy.Dataflow.soundness_nonvacuous,
  `Toy.Dataflow.stepMid_distributive,
  `Toy.Dataflow.strict_and_genKill_exactness_needs_least,
  `Toy.Dataflow.strict_exactness_needs_acc,
  `Toy.Dataflow.strict_exactness_needs_distributive,
  `Toy.Dataflow.strict_exactness_nonvacuous,
  `Toy.Dataflow.ugCFG_isMOPAt_two_empty,
  `Toy.Dataflow.unboundedChainsLat_acc,
  `Toy.Dataflow.unboundedChainsLat_isJSL,
  `Toy.Dataflow.unboundedChainsLat_not_heightLe,
  `Toy.Dataflow.unreachableStrict_strictly_between_nonvacuous,
  `Toy.Dataflow.walk_val_le_of_isSolution_of_monotone,
  `Toy.Dataflow.withBotIntLat_isJSL,
  `Toy.Dataflow.withBotIntLat_not_acc]

def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => roots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
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

end RevalidationAudit

open RevalidationAudit in
open Toy.Dataflow in
#eval show CommandElabM Unit from do
  let env ← getEnv
  for n in wanted do
    match env.find? n with
    | none => IO.println s!"MISSING {n}"
    | some ci =>
      let axs ← collectAxioms n
      IO.println s!"AXIOMS {n} {axs.toList}"
      let sig ← liftTermElabM do
        let f ← Lean.PrettyPrinter.ppSignature n
        pure (Std.Format.pretty f.fmt 100)
      IO.println s!"SIGNATURE {n}"
      IO.println sig
      IO.println "END_SIGNATURE"
      let cl := closure env (ci.type.getUsedConstants.toList) {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      IO.println ("STATEMENT_JSON " ++ (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))]).compress)
