(* Owned observation-only annotation. No definitions, axioms, admissions or proof changes. *)
Require Import isla.adequacy isla.adequacy_itree.

Set Printing Width 120.

Check @isla.adequacy.isla_adequacy.
Print Assumptions isla.adequacy.isla_adequacy.

Check @isla.adequacy_itree.isla_exec_adequate.
Print Assumptions isla.adequacy_itree.isla_exec_adequate.

Check @isla.adequacy_itree.isla_adequacy.
Print Assumptions isla.adequacy_itree.isla_adequacy.
