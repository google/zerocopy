open Hol_lib;;
open Hol_loader;;
(* /home/opam/anneal-cross-output/controls/source/AxiomPolicyNegative.ml *)
#1 "/home/opam/anneal-cross-output/controls/source/AxiomPolicyNegative.ml"
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
(* update digest *)
loaded_files := 
  let digest_bytes = [|41; 128; 182; 93; 39; 187; 221; 99; 84; 179; 148; 33; 42; 42; 173; 135|] in
  let digest = Bytes.init (Array.length digest_bytes) (fun i -> Char.chr digest_bytes.(i)) in
  ("AxiomPolicyNegative.ml", Bytes.to_string digest)::!loaded_files;;

