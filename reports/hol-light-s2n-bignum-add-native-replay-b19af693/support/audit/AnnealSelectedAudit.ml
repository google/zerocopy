(* PREPARATION ONLY. Not compiled/executed. Owned observation entry; original
   HOL and complete s2n proof sources remain unchanged. No axiom is added. *)
let anneal_original_check_axioms = Hol_lib.check_axioms;;
let anneal_original_axioms = Hol_lib.Hol.axioms;;
let anneal_original_hyp = Hol_lib.Hol.hyp;;
let anneal_original_string_of_thm = Hol_lib.string_of_thm;;

let anneal_print_ledger stage =
  List.iter (fun (name,digest) ->
    Printf.printf "ANNEAL_LOADED %s %S %s\n"
      stage name (Digest.to_hex digest)) !Hol_loader.loaded_files;;

anneal_original_check_axioms ();;
anneal_print_ledger "core_before_proof";;
loadt "x86/proofs/bignum_add.ml";;

let anneal_observe name th =
  if anneal_original_hyp th <> [] then
    failwith ("Unexpected explicit hypotheses: " ^ name);
  Printf.printf "ANNEAL_THEOREM_BEGIN %s\n%s\nANNEAL_THEOREM_END %s\n"
    name (anneal_original_string_of_thm th) name;;

List.iter (fun (name,th) -> anneal_observe name th)
 ["bignum_add_mc",bignum_add_mc;
  "bignum_add_tmc",bignum_add_tmc;
  "BIGNUM_ADD_EXEC.length_theorem",fst BIGNUM_ADD_EXEC;
  "bignum_add_windows_mc",bignum_add_windows_mc;
  "bignum_add_windows_tmc",bignum_add_windows_tmc;
  "BIGNUM_ADD_CORRECT",BIGNUM_ADD_CORRECT;
  "BIGNUM_ADD_NOIBT_SUBROUTINE_CORRECT",BIGNUM_ADD_NOIBT_SUBROUTINE_CORRECT;
  "BIGNUM_ADD_SUBROUTINE_CORRECT",BIGNUM_ADD_SUBROUTINE_CORRECT;
  "BIGNUM_ADD_WINDOWS_CORRECT",BIGNUM_ADD_WINDOWS_CORRECT;
  "BIGNUM_ADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT",BIGNUM_ADD_NOIBT_WINDOWS_SUBROUTINE_CORRECT;
  "BIGNUM_ADD_WINDOWS_SUBROUTINE_CORRECT",BIGNUM_ADD_WINDOWS_SUBROUTINE_CORRECT];;

Printf.printf "ANNEAL_DECODE_ARRAY_LENGTH %d\n" (Array.length (snd BIGNUM_ADD_EXEC));;
Array.iteri (fun offset item -> match item with
  | None -> Printf.printf "ANNEAL_DECODE_NONE %d\n" offset
  | Some th -> anneal_observe
      (Printf.sprintf "BIGNUM_ADD_EXEC.decode_%d" offset) th)
  (snd BIGNUM_ADD_EXEC);;

(* This is an instantiation of the ACTUAL upstream theorem, not a replacement
   operational model. Every code/ABI/alias/stack/frame premise is retained. *)
let ANNEAL_ONE_LIMB_SUBROUTINE_CORRECT =
  Hol_lib.SPECL
    [`word 1:int64`; `z:int64`; `word 1:int64`; `x:int64`; `a:num`;
     `word 1:int64`; `y:int64`; `b:num`; `pc:num`;
     `stackpointer:int64`; `returnaddress:int64`]
    BIGNUM_ADD_SUBROUTINE_CORRECT;;
anneal_observe "ANNEAL_ONE_LIMB_SUBROUTINE_CORRECT"
               ANNEAL_ONE_LIMB_SUBROUTINE_CORRECT;;

anneal_original_check_axioms ();;
Printf.printf "ANNEAL_CHECK_AXIOMS_PASS\n";;
List.iter (fun th -> Printf.printf "ANNEAL_GLOBAL_AXIOM %s\n"
  (anneal_original_string_of_thm th)) (anneal_original_axioms());;
Printf.printf "ANNEAL_AUDIT_INNER_FINISHED\n%!";;
