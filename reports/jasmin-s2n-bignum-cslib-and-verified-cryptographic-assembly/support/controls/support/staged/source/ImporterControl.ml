(* CONTROL PLAN ONLY. Not compiled/staged/run. Original upstream base only;
   NEVER load bignum_add.ml or either positive observation entry. *)
let anneal_control_original_check = Hol_lib.check_axioms;;
let anneal_control_original_hyp = Hol_lib.Hol.hyp;;
let anneal_control_original_printer = Hol_lib.string_of_thm;;
anneal_control_original_check ();;
loadt "x86/proofs/base.ml";;
anneal_control_original_check ();;
List.iter (fun (name,digest) -> Printf.printf "ANNEAL_CONTROL_LOADED %S %s\n"
  name (Digest.to_hex digest)) !Hol_loader.loaded_files;;
let anneal_control_literal = [243; 15; 30; 250; 77; 49; 210; 72; 57; 215; 72; 15; 66; 215; 76; 57; 199; 76; 15; 66; 199; 76; 57; 194; 114; 71; 72; 41; 215; 76; 41; 194; 72; 255; 194; 77; 133; 192; 116; 37; 74; 139; 4; 209; 75; 19; 4; 209; 74; 137; 4; 214; 73; 255; 194; 73; 255; 200; 117; 236; 235; 15; 74; 139; 4; 209; 72; 131; 208; 0; 74; 137; 4; 214; 73; 255; 194; 72; 255; 202; 117; 236; 184; 0; 0; 0; 0; 72; 131; 208; 0; 72; 133; 255; 117; 67; 195; 76; 41; 199; 73; 41; 208; 72; 133; 210; 116; 20; 74; 139; 4; 209; 75; 19; 4; 209; 74; 137; 4; 214; 73; 255; 194; 72; 255; 202; 117; 236; 75; 139; 4; 209; 72; 131; 208; 0; 74; 137; 4; 214; 73; 255; 194; 73; 255; 200; 117; 236; 184; 0; 0; 0; 0; 72; 131; 208; 0; 72; 133; 255; 117; 1; 195; 74; 137; 4; 214; 72; 49; 192; 235; 4; 74; 137; 4; 214; 73; 255; 194; 72; 255; 207; 117; 244; 195];;
let anneal_control_case = Sys.argv.(1);;
let anneal_control_path = Sys.argv.(2);;
let anneal_control_bytes =
  if anneal_control_case = "C1" then [0]
  else if List.mem anneal_control_case ["C0";"C2";"C3";"C4";"C9"]
  then anneal_control_literal
  else failwith "unknown owned control case";;
Printf.printf "ANNEAL_CONTROL_READY %s\n%!" anneal_control_case;;
let anneal_control_thm = define_assert_from_elf
  "anneal_control_mc" anneal_control_path anneal_control_bytes;;
if anneal_control_original_hyp anneal_control_thm <> []
then failwith "unexpected control theorem hypotheses";;
Printf.printf "ANNEAL_CONTROL_THEOREM %s\n%s\n"
  anneal_control_case (anneal_control_original_printer anneal_control_thm);;
anneal_control_original_check ();;
Printf.printf "ANNEAL_CONTROL_IMPORT_ACCEPTED %s\n%!" anneal_control_case;;
