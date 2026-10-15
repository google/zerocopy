(* PREPARATION ONLY. Deliberate negative-only core HOL process.
   Never combine with an importer, arithmetic or positive-proof process.
   T is already provable; registering it as a non-basic axiom should still
   violate the original policy. No desired false-result axiom is introduced. *)
let anneal_axiom_original_check = Hol_lib.check_axioms;;
anneal_axiom_original_check ();;
Printf.printf "ANNEAL_AXIOM_BASELINE_PASS\n%!";;
let anneal_negative_registered_truth = Hol_lib.Hol.new_axiom `T`;;
Printf.printf "ANNEAL_AXIOM_REGISTERED %s\n%!"
  (Hol_lib.string_of_thm anneal_negative_registered_truth);;
anneal_axiom_original_check ();;
Printf.printf "ANNEAL_AXIOM_UNEXPECTED_ACCEPTANCE\n%!";;
