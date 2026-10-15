(* Proposed observation-only annotation. Not compiled in this planning task. *)
Require Import simuliris.simulation.language.
Require Import simuliris.tree_borrows.examples.lib.
Require Import simuliris.tree_borrows.step_laws.steps_local.
Require Import simuliris.tree_borrows.step_laws.steps_retag.
Require Import simuliris.tree_borrows.step_laws.steps_opt.
Require Import simuliris.tree_borrows.loc_controlled_laws.
Require Import simuliris.tree_borrows.logical_state.

Set Printing Width 120.

Check @simuliris.simulation.language.safe_reach.
Print Assumptions simuliris.simulation.language.safe_reach.

Check @simuliris.tree_borrows.examples.lib.write_entire_range.
Print Assumptions simuliris.tree_borrows.examples.lib.write_entire_range.

Check @simuliris.tree_borrows.examples.lib.sim_new_place_local.
Print Assumptions simuliris.tree_borrows.examples.lib.sim_new_place_local.

Check @simuliris.tree_borrows.examples.lib.new_place_safe_reach.
Print Assumptions simuliris.tree_borrows.examples.lib.new_place_safe_reach.

Check @simuliris.tree_borrows.step_laws.steps_local.sim_alloc_local.
Print Assumptions simuliris.tree_borrows.step_laws.steps_local.sim_alloc_local.

Check @simuliris.tree_borrows.step_laws.steps_retag.sim_retag_default.
Print Assumptions simuliris.tree_borrows.step_laws.steps_retag.sim_retag_default.

Check @simuliris.tree_borrows.step_laws.steps_retag.sim_retag_fnentry.
Print Assumptions simuliris.tree_borrows.step_laws.steps_retag.sim_retag_fnentry.

Check @simuliris.tree_borrows.step_laws.steps_opt.sim_protected_unprotect.
Print Assumptions simuliris.tree_borrows.step_laws.steps_opt.sim_protected_unprotect.

Check @simuliris.tree_borrows.loc_controlled_laws.loc_controlled_read_after_reborrow_creates.
Print Assumptions simuliris.tree_borrows.loc_controlled_laws.loc_controlled_read_after_reborrow_creates.

Check @simuliris.tree_borrows.logical_state.array_tag.
Print Assumptions simuliris.tree_borrows.logical_state.array_tag.

Check @simuliris.tree_borrows.loc_controlled_laws.pointer_kind_to_tag_unprotected.
Print Assumptions simuliris.tree_borrows.loc_controlled_laws.pointer_kind_to_tag_unprotected.

Check @simuliris.tree_borrows.loc_controlled_laws.pointer_kind_to_tag_protected.
Print Assumptions simuliris.tree_borrows.loc_controlled_laws.pointer_kind_to_tag_protected.

