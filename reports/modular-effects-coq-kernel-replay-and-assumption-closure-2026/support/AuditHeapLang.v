(* Owned observation-only annotation. No definitions, axioms, admissions or proof changes. *)
Require Import iris.itree.heaplang.adequacy iris.itree.heaplang.opsem_adequacy.

Set Printing Width 120.

Check @iris.itree.heaplang.adequacy.wp_adequacy_irel.
Print Assumptions iris.itree.heaplang.adequacy.wp_adequacy_irel.

Check @iris.itree.heaplang.adequacy.wp_adequacy_eval.
Print Assumptions iris.itree.heaplang.adequacy.wp_adequacy_eval.

Check @iris.itree.heaplang.adequacy.wp_partial_soundness.
Print Assumptions iris.itree.heaplang.adequacy.wp_partial_soundness.

Check @iris.itree.heaplang.adequacy.wp_total_soundness.
Print Assumptions iris.itree.heaplang.adequacy.wp_total_soundness.

Check @iris.itree.heaplang.opsem_adequacy.execution_from_opsem_trace.
Print Assumptions iris.itree.heaplang.opsem_adequacy.execution_from_opsem_trace.

Check @iris.itree.heaplang.opsem_adequacy.partially_adequate_opsem_adequate.
Print Assumptions iris.itree.heaplang.opsem_adequacy.partially_adequate_opsem_adequate.

Check @iris.itree.heaplang.opsem_adequacy.wp_later_opsem_adequate.
Print Assumptions iris.itree.heaplang.opsem_adequacy.wp_later_opsem_adequate.

Check @iris.itree.heaplang.opsem_adequacy.wp_total_opsem_adequate.
Print Assumptions iris.itree.heaplang.opsem_adequacy.wp_total_opsem_adequate.
