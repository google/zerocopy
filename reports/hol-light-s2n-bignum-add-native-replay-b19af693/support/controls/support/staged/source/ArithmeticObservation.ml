(* PREPARATION ONLY. Core HOL module only; no s2n proof or model imports.
   These are numeral-conversion theorems, not a machine-state theorem. *)
let anneal_arith_original_check = Hol_lib.check_axioms;;
anneal_arith_original_check ();;
let anneal_arith_observe name term expected =
  let th = Hol_lib.NUM_REDUCE_CONV term in
  if Hol_lib.Hol.hyp th <> [] then failwith "unexpected arithmetic hypotheses";
  let left,right = Hol_lib.dest_eq (Hol_lib.Hol.concl th) in
  if left <> term || right <> expected then
    failwith "unexpected arithmetic conversion conclusion";
  Printf.printf "ANNEAL_ARITH_THEOREM %s\n%s\n"
    name (Hol_lib.string_of_thm th);;
anneal_arith_observe "one_limb_sum"
  `((2 EXP 64 - 1) + 1) MOD 2 EXP 64` `0:num`;;
anneal_arith_observe "one_limb_carry"
  `((2 EXP 64 - 1) + 1) DIV 2 EXP 64` `1:num`;;
anneal_arith_observe "different_observations" `(0:num) = 1` `F`;;
anneal_arith_original_check ();;
Printf.printf "ANNEAL_ARITH_FINISHED\n%!";;
