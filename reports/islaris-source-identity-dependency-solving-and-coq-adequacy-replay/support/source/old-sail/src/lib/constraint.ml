(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

module Big_int = Nat_big_num
open Ast
open Ast_util
open Util

let opt_smt_verbose = ref false

type solver = { command : string; header : string; footer : string; negative_literals : bool; uninterpret_power : bool }

let cvc4_solver =
  {
    command = "cvc4 -L smtlib2 --tlimit=2000";
    header = "(set-logic QF_UFNIA)\n";
    footer = "";
    negative_literals = false;
    uninterpret_power = true;
  }

let mathsat_solver =
  {
    command = "mathsat";
    header = "(set-logic QF_UFLIA)\n";
    footer = "";
    negative_literals = false;
    uninterpret_power = true;
  }

let z3_solver =
  {
    command = "z3 -t:1000 -T:10";
    (* Using push and pop is much faster, I believe because
       incremental mode uses a different solver. *)
    header = "(push)\n";
    footer = "(pop)\n";
    negative_literals = true;
    uninterpret_power = false;
  }

let yices_solver =
  {
    command = "yices-smt2 --timeout=2";
    header = "(set-logic QF_UFLIA)\n";
    footer = "";
    negative_literals = false;
    uninterpret_power = true;
  }

let vampire_solver =
  {
    (* vampire sometimes likes to ignore its time limit *)
    command = "timeout -s SIGKILL 3s vampire --time_limit 2s --input_syntax smtlib2 --mode smtcomp";
    header = "";
    footer = "";
    negative_literals = false;
    uninterpret_power = true;
  }

let alt_ergo_solver =
  { command = "alt-ergo"; header = ""; footer = ""; negative_literals = false; uninterpret_power = true }

let opt_solver = ref z3_solver

let set_solver = function
  | "z3" -> opt_solver := z3_solver
  | "alt-ergo" -> opt_solver := alt_ergo_solver
  | "cvc4" -> opt_solver := cvc4_solver
  | "mathsat" -> opt_solver := mathsat_solver
  | "vampire" -> opt_solver := vampire_solver
  | "yices" -> opt_solver := yices_solver
  | unknown -> prerr_endline ("Unrecognised SMT solver " ^ unknown)

(* SMTLIB v2.0 format is based on S-expressions so we have a
   lightweight representation of those here. *)
type sexpr = List of sexpr list | Atom of string

let sfun (fn : string) (xs : sexpr list) : sexpr = List (Atom fn :: xs)

let rec pp_sexpr : sexpr -> string = function List xs -> "(" ^ string_of_list " " pp_sexpr xs ^ ")" | Atom x -> x

let rec add_sexpr buf = function
  | List xs ->
      Buffer.add_char buf '(';
      Util.iter_last
        (fun last x ->
          add_sexpr buf x;
          if not last then Buffer.add_char buf ' '
        )
        xs;
      Buffer.add_char buf ')'
  | Atom x -> Buffer.add_string buf x

let rec add_list buf sep add_elem = function
  | [] -> ()
  | [x] -> add_elem buf x
  | x :: xs ->
      add_elem buf x;
      Buffer.add_char buf sep;
      add_list buf sep add_elem xs

(* Each non-Type/Order kind in Sail maps to a type in the SMT solver *)
let smt_type l = function
  | K_int -> Atom "Int"
  | K_bool -> Atom "Bool"
  | _ -> raise (Reporting.err_unreachable l __POS__ "Tried to pass Type or Order kinded variable to SMT solver")

let to_smt l vars constr =
  (* Numbering all SMT variables v0, ... vn, rather than generating
     names based on their Sail names (e.g. using zencode) ensures that
     alpha-equivalent constraints generate the same SMT problem, which
     is important for the SMT memoisation to work properly. *)
  let var_map = ref KBindings.empty in
  let vnum = ref (-1) in
  let smt_var v =
    match KBindings.find_opt v !var_map with
    | Some n -> (Atom ("v" ^ string_of_int n), false)
    | None ->
        let n = !vnum + 1 in
        var_map := KBindings.add v n !var_map;
        vnum := n;
        (Atom ("v" ^ string_of_int n), true)
  in

  let exponentials = ref [] in

  (* var_decs outputs the list of variables to be used by the SMT
     solver in SMTLIB v2.0 format. It takes a kind_aux KBindings, as
     returned by Type_check.get_typ_vars *)
  let var_decs l (vars : kind_aux KBindings.t) : sexpr list =
    vars |> KBindings.bindings |> List.map (fun (v, k) -> sfun "declare-const" [fst (smt_var v); smt_type l k])
  in
  let rec smt_nexp (Nexp_aux (aux, _) : nexp) : sexpr =
    match aux with
    | Nexp_id id -> Atom (Util.zencode_string (string_of_id id))
    | Nexp_var v -> fst (smt_var v)
    | Nexp_constant c when Big_int.less_equal c (Big_int.of_int (-1)) && not !opt_solver.negative_literals ->
        sfun "-" [Atom "0"; Atom (Big_int.to_string (Big_int.abs c))]
    | Nexp_constant c -> Atom (Big_int.to_string c)
    | Nexp_app (id, nexps) -> sfun (string_of_id id) (List.map smt_nexp nexps)
    | Nexp_times (nexp1, nexp2) -> sfun "*" [smt_nexp nexp1; smt_nexp nexp2]
    | Nexp_sum (nexp1, nexp2) -> sfun "+" [smt_nexp nexp1; smt_nexp nexp2]
    | Nexp_minus (nexp1, nexp2) -> sfun "-" [smt_nexp nexp1; smt_nexp nexp2]
    | Nexp_exp nexp -> begin
        match nexp_simp nexp with
        | Nexp_aux (Nexp_constant c, _) when Big_int.greater_equal c Big_int.zero ->
            Atom (Big_int.to_string (Big_int.pow_int_positive 2 (Big_int.to_int c)))
        | nexp when !opt_solver.uninterpret_power ->
            let exp = smt_nexp nexp in
            exponentials := exp :: !exponentials;
            sfun "sailexp" [exp]
        | nexp ->
            let exp = smt_nexp nexp in
            exponentials := exp :: !exponentials;
            sfun "to_int" [sfun "^" [Atom "2"; exp]]
      end
    | Nexp_neg nexp -> sfun "-" [smt_nexp nexp]
  in
  let rec smt_constraint (NC_aux (aux, _) : n_constraint) : sexpr =
    match aux with
    | NC_equal (nexp1, nexp2) -> sfun "=" [smt_nexp nexp1; smt_nexp nexp2]
    | NC_bounded_le (nexp1, nexp2) -> sfun "<=" [smt_nexp nexp1; smt_nexp nexp2]
    | NC_bounded_lt (nexp1, nexp2) -> sfun "<" [smt_nexp nexp1; smt_nexp nexp2]
    | NC_bounded_ge (nexp1, nexp2) -> sfun ">=" [smt_nexp nexp1; smt_nexp nexp2]
    | NC_bounded_gt (nexp1, nexp2) -> sfun ">" [smt_nexp nexp1; smt_nexp nexp2]
    | NC_not_equal (nexp1, nexp2) -> sfun "not" [sfun "=" [smt_nexp nexp1; smt_nexp nexp2]]
    | NC_set (v, ints) -> sfun "or" (List.map (fun i -> sfun "=" [fst (smt_var v); Atom (Big_int.to_string i)]) ints)
    | NC_or (nc1, nc2) -> sfun "or" [smt_constraint nc1; smt_constraint nc2]
    | NC_and (nc1, nc2) -> sfun "and" [smt_constraint nc1; smt_constraint nc2]
    | NC_app (id, args) -> sfun (string_of_id id) (List.map smt_typ_arg args)
    | NC_true -> Atom "true"
    | NC_false -> Atom "false"
    | NC_var v -> fst (smt_var v)
  and smt_typ_arg (A_aux (aux, l) : typ_arg) : sexpr =
    match aux with
    | A_nexp nexp -> smt_nexp nexp
    | A_bool nc -> smt_constraint nc
    | _ -> raise (Reporting.err_unreachable l __POS__ "Tried to pass Type or Order kind to SMT function")
  in
  let smt_constr = smt_constraint constr in
  (var_decs l vars, smt_constr, smt_var, !exponentials)

let sailexp_concrete n =
  List.init (n + 1) (fun i ->
      sfun "=" [sfun "sailexp" [Atom (string_of_int i)]; Atom (Big_int.to_string (Big_int.pow_int_positive 2 i))]
  )

let smtlib_of_constraints ?(get_model = false) l vars extra constr : string * (kid -> sexpr * bool) * sexpr list =
  let open Buffer in
  let buf = create 512 in
  add_string buf !opt_solver.header;
  let variables, problem, var_map, exponentials = to_smt l vars constr in
  add_list buf '\n' add_sexpr variables;
  add_char buf '\n';
  if !opt_solver.uninterpret_power then add_string buf "(declare-fun sailexp (Int) Int)\n";
  add_list buf '\n' (fun buf sexpr -> add_sexpr buf (sfun "assert" [sexpr])) extra;
  add_char buf '\n';
  add_sexpr buf (sfun "assert" [problem]);
  add_string buf "\n(check-sat)";
  if get_model then add_string buf "\n(get-model)";
  add_char buf '\n';
  add_string buf !opt_solver.footer;
  (Buffer.contents buf, var_map, exponentials)

type smt_result = Unknown | Sat | Unsat

module DigestMap = Map.Make (Digest)

let known_problems = ref DigestMap.empty
let known_uniques = ref DigestMap.empty

let load_digests_err () =
  let in_chan = open_in_bin "z3_problems" in
  let rec load () =
    let digest = Digest.input in_chan in
    let result = input_byte in_chan in
    begin
      match result with
      | 0 -> known_problems := DigestMap.add digest Unknown !known_problems
      | 1 -> known_problems := DigestMap.add digest Sat !known_problems
      | 2 -> known_problems := DigestMap.add digest Unsat !known_problems
      | 3 -> known_uniques := DigestMap.add digest None !known_uniques
      | 4 ->
          let solution = input_binary_int in_chan in
          known_uniques := DigestMap.add digest (Some solution) !known_uniques
      | _ -> assert false
    end;
    load ()
  in
  try load () with End_of_file -> close_in in_chan

let load_digests () = try load_digests_err () with Sys_error _ -> ()

let save_digests () =
  let out_chan = open_out_bin "z3_problems" in
  let output_problem digest result =
    Digest.output out_chan digest;
    match result with
    | Unknown -> output_byte out_chan 0
    | Sat -> output_byte out_chan 1
    | Unsat -> output_byte out_chan 2
  in
  DigestMap.iter output_problem !known_problems;
  let output_solution digest result =
    Digest.output out_chan digest;
    match result with
    | None -> output_byte out_chan 3
    | Some i ->
        output_byte out_chan 4;
        output_binary_int out_chan i
  in
  DigestMap.iter output_solution !known_uniques;
  close_out out_chan

let kopt_pair kopt = (kopt_kid kopt, unaux_kind (kopt_kind kopt))

let bound_exponential sexpr = sfun "and" [sfun "<=" [Atom "0"; sexpr]; sfun "<=" [sexpr; Atom "64"]]

let constraint_to_smt l constr =
  let vars =
    kopts_of_constraint constr |> KOptSet.elements |> List.map kopt_pair
    |> List.fold_left (fun m (k, v) -> KBindings.add k v m) KBindings.empty
  in
  let vars, sexpr, var_map, exponentials = to_smt l vars constr in
  let vars = string_of_list "\n" pp_sexpr vars in
  ( vars ^ "\n(assert " ^ pp_sexpr sexpr ^ ")",
    (fun v ->
      let sexpr, found = var_map v in
      (pp_sexpr sexpr, found)
    ),
    List.map pp_sexpr exponentials
  )

let rec call_smt' l extra constraints =
  let vars =
    kopts_of_constraint constraints |> KOptSet.elements |> List.map kopt_pair
    |> List.fold_left (fun m (k, v) -> KBindings.add k v m) KBindings.empty
  in
  let problems = [constraints] in
  let smt_file, _, exponentials = smtlib_of_constraints l vars extra constraints in

  if !opt_smt_verbose then prerr_endline (Printf.sprintf "SMTLIB2 constraints are: \n%s%!" smt_file);

  let rec input_lines chan = function
    | 0 -> []
    | n ->
        let l = input_line chan in
        let ls = input_lines chan (n - 1) in
        l :: ls
  in

  let rec input_all chan = match input_line chan with l -> l :: input_all chan | exception End_of_file -> [] in

  let digest = Digest.string smt_file in

  let result =
    match DigestMap.find_opt digest !known_problems with
    | Some result -> result
    | None -> (
        let input_file, tmp_chan =
          try Filename.open_temp_file "constraint_" ".smt2"
          with Sys_error msg -> raise (Reporting.err_general l ("Could not open temp file when calling SMT: " ^ msg))
        in
        output_string tmp_chan smt_file;
        close_out tmp_chan;
        let status, smt_output, smt_errors =
          try
            let smt_out, smt_in, smt_err =
              Unix.open_process_full (!opt_solver.command ^ " " ^ input_file) (Unix.environment ())
            in
            let smt_output =
              try List.combine problems (input_lines smt_out (List.length problems))
              with End_of_file -> List.combine problems ["unknown"]
            in
            let smt_errors = input_all smt_err in
            let status = Unix.close_process_full (smt_out, smt_in, smt_err) in
            (status, smt_output, smt_errors)
          with exn -> raise (Reporting.err_general l ("Error when calling smt: " ^ Printexc.to_string exn))
        in
        let _ =
          match status with
          | Unix.WEXITED 0 -> ()
          | Unix.WEXITED n ->
              raise
                (Reporting.err_general l
                   ("SMT solver returned unexpected status " ^ string_of_int n ^ "\n" ^ String.concat "\n" smt_errors)
                )
          | Unix.WSIGNALED n | Unix.WSTOPPED n ->
              raise (Reporting.err_general l ("SMT solver killed by signal " ^ string_of_int n))
        in
        Sys.remove input_file;
        try
          let _problem, _ = List.find (fun (_, result) -> result = "unsat") smt_output in
          known_problems := DigestMap.add digest Unsat !known_problems;
          Unsat
        with Not_found ->
          let unsolved = List.filter (fun (_, result) -> result = "unknown") smt_output in
          if unsolved == [] then (
            known_problems := DigestMap.add digest Sat !known_problems;
            Sat
          )
          else (
            known_problems := DigestMap.add digest Unknown !known_problems;
            Unknown
          )
      )
  in
  ( ( match result with
    | Unsat -> Unsat
    | Sat -> Sat
    | Unknown when exponentials <> [] && not !opt_solver.uninterpret_power ->
        (* If we get an unknown result for a constraint involving `2^x`,
           then try replacing `2^` with an uninterpreted function to see
           if the problem would be unsat in that case. *)
        opt_solver := { !opt_solver with uninterpret_power = true };
        let result = call_smt_uninterpret_power ~bound:64 l constraints in
        opt_solver := { !opt_solver with uninterpret_power = false };
        result
    | Unknown -> Unknown
    ),
    exponentials
  )

and call_smt_uninterpret_power ~bound l constraints =
  match call_smt' l (sailexp_concrete bound) constraints with
  | Unsat, _ -> Unsat
  | Sat, exponentials -> begin
      match call_smt' l (sailexp_concrete bound @ List.map bound_exponential exponentials) constraints with
      | Sat, _ -> Sat
      | _ -> Unknown
    end
  | _ -> Unknown

let call_smt l constraints =
  let t = Profile.start_smt () in
  let result =
    if !opt_solver.uninterpret_power then call_smt_uninterpret_power ~bound:64 l constraints
    else fst (call_smt' l [] constraints)
  in
  Profile.finish_smt t;
  result

let solve_smt_file l extra constraints =
  let vars =
    kopts_of_constraint constraints |> KOptSet.elements |> List.map kopt_pair
    |> List.fold_left (fun m (k, v) -> KBindings.add k v m) KBindings.empty
  in
  smtlib_of_constraints ~get_model:true l vars extra constraints

let call_smt_solve l smt_file smt_vars var =
  let smt_var = pp_sexpr (fst (smt_vars var)) in
  if !opt_smt_verbose then
    prerr_endline (Printf.sprintf "SMTLIB2 constraints are (solve for %s): \n%s%!" smt_var smt_file)
  else ();

  let rec input_all chan =
    try
      let l = input_line chan in
      let ls = input_all chan in
      l :: ls
    with End_of_file -> []
  in

  let input_file, tmp_chan = Filename.open_temp_file "constraint_" ".smt2" in
  output_string tmp_chan smt_file;
  close_out tmp_chan;
  let smt_output =
    try
      let t = Profile.start_smt () in
      let smt_chan = Unix.open_process_in ("z3 -t:1000 -T:10 " ^ input_file) in
      let smt_output = String.concat " " (input_all smt_chan) in
      let _ = Unix.close_process_in smt_chan in
      Profile.finish_smt t;
      smt_output
    with exn -> raise (Reporting.err_general l ("Got error when calling smt: " ^ Printexc.to_string exn))
  in
  Sys.remove input_file;
  let regexp = {|(define-fun |} ^ smt_var ^ {| () Int[ ]+\([0-9]+\))|} in
  try
    let _ = Str.search_forward (Str.regexp regexp) smt_output 0 in
    let result = Big_int.of_string (Str.matched_group 1 smt_output) in
    Some result
  with Not_found -> None

let call_smt_solve_bitvector l smt_file smt_vars =
  let rec input_all chan =
    try
      let l = input_line chan in
      let ls = input_all chan in
      l :: ls
    with End_of_file -> []
  in

  let input_file, tmp_chan = Filename.open_temp_file "constraint_" ".smt2" in
  output_string tmp_chan smt_file;
  close_out tmp_chan;
  let smt_output =
    try
      let t = Profile.start_smt () in
      let smt_chan = Unix.open_process_in ("z3 -t:1000 -T:10 " ^ input_file) in
      let smt_output = String.concat " " (input_all smt_chan) in
      let _ = Unix.close_process_in smt_chan in
      Profile.finish_smt t;
      smt_output
    with exn -> raise (Reporting.err_general l ("Got error when calling smt: " ^ Printexc.to_string exn))
  in
  Sys.remove input_file;
  List.map
    (fun (smt_var, smt_ty) ->
      let smt_var_str = "p" ^ string_of_int smt_var in
      try
        if smt_ty = "Int" then (
          let regexp = "(define-fun " ^ smt_var_str ^ {| () Int [ ]+\([0-9]+\|\((- [0-9]+)\)\))|} in
          let _ = Str.search_forward (Str.regexp regexp) smt_output 0 in
          let result = Str.matched_group 1 smt_output in
          if result.[0] = '(' then (
            let n = Big_int.of_string (String.sub result 3 (String.length result - 4)) in
            Some (smt_var, mk_lit (L_num (Big_int.negate n)))
          )
          else Some (smt_var, mk_lit (L_num (Big_int.of_string result)))
        )
        else (
          let regexp = "(define-fun " ^ smt_var_str ^ " () " ^ smt_ty ^ {|[ ]+\(#[xb]\)\([0-9A-Fa-f]+\))|} in
          let _ = Str.search_forward (Str.regexp regexp) smt_output 0 in
          let prefix = Str.matched_group 1 smt_output in
          let result = Str.matched_group 2 smt_output in
          match prefix with
          | "#b" -> Some (smt_var, mk_lit (L_bin result))
          | "#x" -> Some (smt_var, mk_lit (L_hex result))
          | _ -> raise (Reporting.err_general l "Could not parse bitvector value from SMT solver")
        )
      with Not_found -> None
    )
    smt_vars
  |> Util.option_all

let solve_smt l constraints var =
  let smt_file, smt_vars, _ = solve_smt_file l [] constraints in
  call_smt_solve l smt_file smt_vars var

let solve_all_smt l constraints var =
  let rec aux results =
    let constraints = List.fold_left (fun ncs r -> nc_and ncs (nc_neq (nconstant r) (nvar var))) constraints results in
    match solve_smt l constraints var with
    | Some result -> aux (result :: results)
    | None -> (
        match call_smt l constraints with Unsat -> Some results | _ -> None
      )
  in
  aux []

let solve_unique_smt' l constraints exp_defn exp_bound var =
  let smt_file, smt_vars, exponentials = solve_smt_file l (exp_defn @ exp_bound) constraints in
  let digest = Digest.string (smt_file ^ pp_sexpr (fst (smt_vars var))) in
  let result =
    match DigestMap.find_opt digest !known_uniques with
    | Some (Some result) -> Some (Big_int.of_int result)
    | Some None -> None
    | None -> (
        match call_smt_solve l smt_file smt_vars var with
        | Some result ->
            let t = Profile.start_smt () in
            let smt_result' = fst (call_smt' l exp_defn (nc_and constraints (nc_neq (nconstant result) (nvar var)))) in
            Profile.finish_smt t;
            begin
              match smt_result' with
              | Unsat ->
                  if Big_int.less_equal Big_int.zero result && Big_int.less result (Big_int.pow_int_positive 2 30) then
                    known_uniques := DigestMap.add digest (Some (Big_int.to_int result)) !known_uniques
                  else ();
                  Some result
              | _ ->
                  known_uniques := DigestMap.add digest None !known_uniques;
                  None
            end
        | None ->
            known_uniques := DigestMap.add digest None !known_uniques;
            None
      )
  in
  (result, exponentials)

(* Follows the same approach as call_smt' for unknown results due to
   exponentials, retrying with a bounded spec. *)

let solve_unique_smt l constraints var =
  let t = Profile.start_smt () in
  let result =
    match solve_unique_smt' l constraints [] [] var with
    | Some result, _ -> Some result
    | None, [] -> None
    | None, exponentials ->
        opt_solver := { !opt_solver with uninterpret_power = true };
        let sailexp = sailexp_concrete 64 in
        let exp_bound = List.map bound_exponential exponentials in
        let result, _ = solve_unique_smt' l constraints sailexp exp_bound var in
        opt_solver := { !opt_solver with uninterpret_power = false };
        result
  in
  Profile.finish_smt t;
  result
