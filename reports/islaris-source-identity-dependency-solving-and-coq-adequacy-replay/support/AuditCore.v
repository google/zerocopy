(* Owned observation-only annotation. No definitions, axioms, admissions or proof changes. *)
Require Import iris.itree.axioms iris.itree.exec iris.itree.state iris.itree.heap.
Require Import iris.itree.threadpool.exec iris.itree.threadpool.interleaving.
Require Import iris.itree.examplelang.adequacy.

Set Printing Width 120.

Check @iris.itree.axioms.AxChoice.
Print Assumptions iris.itree.axioms.AxChoice.
Check @iris.itree.axioms.Ax.eq_rect_eq.
Print Assumptions iris.itree.axioms.Ax.eq_rect_eq.
Check @bisimulation_is_eq.
Print Assumptions bisimulation_is_eq.

Check @iris.itree.exec.handler_adequate_from_simple.
Print Assumptions iris.itree.exec.handler_adequate_from_simple.

Check @iris.itree.exec.sumEH_adequate.
Print Assumptions iris.itree.exec.sumEH_adequate.

Check @iris.itree.exec.sumSEH_adequate.
Print Assumptions iris.itree.exec.sumSEH_adequate.

Check @iris.itree.exec.wpi_adequate.
Print Assumptions iris.itree.exec.wpi_adequate.

Check @iris.itree.exec.wpi_adequate_pure.
Print Assumptions iris.itree.exec.wpi_adequate_pure.

Check @iris.itree.state.stateEH_adequate.
Print Assumptions iris.itree.state.stateEH_adequate.

Check @iris.itree.state.state_adequacy.
Print Assumptions iris.itree.state.state_adequacy.

Check @iris.itree.heap.wpi_load.
Print Assumptions iris.itree.heap.wpi_load.

Check @iris.itree.heap.wpi_store.
Print Assumptions iris.itree.heap.wpi_store.

Check @iris.itree.heap.wpi_allocN.
Print Assumptions iris.itree.heap.wpi_allocN.

Check @iris.itree.heap.heap_adequacy.
Print Assumptions iris.itree.heap.heap_adequacy.

Check @iris.itree.threadpool.exec.threadpoolEH_adequate.
Print Assumptions iris.itree.threadpool.exec.threadpoolEH_adequate.

Check @iris.itree.threadpool.interleaving.threadpool_adequacy.
Print Assumptions iris.itree.threadpool.interleaving.threadpool_adequacy.

Check @iris.itree.examplelang.adequacy.wp_adequacy_irel.
Print Assumptions iris.itree.examplelang.adequacy.wp_adequacy_irel.
