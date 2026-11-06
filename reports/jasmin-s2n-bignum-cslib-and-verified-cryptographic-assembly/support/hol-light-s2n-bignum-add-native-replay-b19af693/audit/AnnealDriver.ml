(* PREPARATION ONLY. Fixed future owned output path, not an existing input.
   Separate outer driver observes inner-entry digest after its completion. *)
loadt "/home/opam/anneal-cross-output/audit/AnnealSelectedAudit.ml";;
anneal_print_ledger "after_inner_audit";;
anneal_original_check_axioms ();;
Printf.printf "ANNEAL_CHECK_AXIOMS_OUTER_PASS\n";;
Printf.printf "ANNEAL_AUDIT_FINISHED\n%!";;
