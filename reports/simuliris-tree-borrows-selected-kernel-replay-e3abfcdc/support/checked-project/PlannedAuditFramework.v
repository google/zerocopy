(* Proposed observation-only annotation. Not compiled in this planning task. *)
Require Import simuliris.simulation.adequacy.
Require Import simuliris.simulation.fairness_adequacy.
Require Import simuliris.tree_borrows.adequacy.
Require Import simuliris.tree_borrows.refl.

Set Printing Width 120.

Check @simuliris.simulation.adequacy.slsls_adequacy.
Print Assumptions simuliris.simulation.adequacy.slsls_adequacy.

Check @simuliris.simulation.fairness_adequacy.sim_pool_preserves_fair_termination.
Print Assumptions simuliris.simulation.fairness_adequacy.sim_pool_preserves_fair_termination.

Check @simuliris.tree_borrows.adequacy.prog_rel_adequacy.
Print Assumptions simuliris.tree_borrows.adequacy.prog_rel_adequacy.

Check @simuliris.tree_borrows.adequacy.log_rel_adequacy.
Print Assumptions simuliris.tree_borrows.adequacy.log_rel_adequacy.

Check @simuliris.tree_borrows.refl.sb_log_rel_structural.
Print Assumptions simuliris.tree_borrows.refl.sb_log_rel_structural.

Check @simuliris.tree_borrows.refl.log_rel_refl.
Print Assumptions simuliris.tree_borrows.refl.log_rel_refl.

Check @simuliris.tree_borrows.refl.log_rel_ctx.
Print Assumptions simuliris.tree_borrows.refl.log_rel_ctx.

