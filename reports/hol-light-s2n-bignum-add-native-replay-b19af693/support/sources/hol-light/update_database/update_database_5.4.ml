(* ========================================================================= *)
(* Create search database from OCaml / modify search database dynamically.   *)
(*                                                                           *)
(* This file assigns to "theorems", which is a list of name-theorem pairs.   *)
(* The core system already has such a database set up. Use this file if you  *)
(* want to update the database beyond the core, so you can search it.        *)
(*                                                                           *)
(* The trickery to get at the OCaml environment is due to Roland Zumkeller   *)
(* and Michael Farber. It works by copying some internal data structures and *)
(* casting into the copy using Obj.magic.                                    *)
(* ========================================================================= *)

module Ocaml_typing = struct

open Types

(* If the given type is simple return its name, otherwise None. *)

let rec get_simple_type = function
  | Tlink texpr ->
    (match get_desc texpr with
    | Tconstr (Pident p,[],_) -> Some (Ident.name p)
    | d -> get_simple_type d)
  | Tconstr (Path.Pident p,  [], _) -> Some (Ident.name p)
  | _ -> None;;

(* Execute any OCaml expression given as a string. *)

let exec s = (ignore o Toploop.execute_phrase false Format.std_formatter
  o !Toploop.parse_toplevel_phrase o Lexing.from_string) s

(* Evaluate any OCaml expression given as a string. *)

let eval n =
  if String.contains n '.' then begin
    exec ("let buf__ = ( " ^ n ^ " );;");
    Obj.magic (Toploop.getvalue "buf__")
  end else Obj.magic (Toploop.getvalue n)

(* Register all theorems added since the last update. *)
end

module Lookuptheorems = struct
open Types

let lid_cons (lidopt:Longident.t option) (id:string): Longident.t =
  let idloc:string Location.loc = { txt = id; loc = Location.none } in
  match lidopt with
    None -> Longident.Lident id
  | Some li -> Longident.Ldot({ txt = li; loc = Location.none }, idloc)

let it_val_1 lidopt s p vd acc =
  if (Some "thm") = Ocaml_typing.get_simple_type (get_desc vd.Types.val_type) then
    (lid_cons lidopt s)::acc else acc

let it_mod_1 lidopt s p md acc = (lid_cons lidopt s)::acc

let enum0 (lidopt:Longident.t option) =
  try
    let vl = Env.fold_values (it_val_1 lidopt) lidopt
        !Toploop.toplevel_env [] in
    let ml = Env.fold_modules (it_mod_1 lidopt) lidopt
        !Toploop.toplevel_env [] in
    (vl, ml)
  with Not_found ->
    (* Looking for (Longident.Lident "Stream") raises Not_found.
       Stream is a deprecated alias module of "Stdlib.Stream", and the camlp-streams
       package that is used by pa_hol_syntax redefines Stream, which seems to
       confuse Env.fold_values and Env.fold_modules. *)
    ([], [])

let rec enum1 lidopt acc =
  match enum0 lidopt with
    (vl, []) -> vl@acc
  | (vl, ml) ->
     List.fold_left (fun acc mlid ->
         enum1 (Some mlid) acc) (vl@acc) ml

let string_of_longident lid =
  String.concat "." (Longident.flatten lid)

let all_theorems () =
  let _ = Ocaml_typing.exec ("unset_jrh_lexer;;") in
  let res = enum1 None []
    |> List.map (fun lid ->
        let s = string_of_longident lid in
        (s, (Ocaml_typing.eval s : thm))) in
  let _ = Ocaml_typing.exec ("set_jrh_lexer;;") in
  res
end


let update_database () =
    theorems := Lookuptheorems.all_theorems()

(* ------------------------------------------------------------------------- *)
(* Put an assignment of a theorem database in the named file.                *)
(* ------------------------------------------------------------------------- *)

let make_database_assignment filename =
  update_database();
  (let allnames = uniq(sort (<) (map fst (!theorems))) in
   let names = subtract allnames ["it"] in
   let entries = map (fun n -> "\""^n^"\","^n) names in
   let text = "needs \"help.ml\";;\n\n"^
              "theorems :=\n[\n"^
              end_itlist (fun a b -> a^";\n"^b) entries^"\n];;\n" in
   file_of_string filename text);;

(* ------------------------------------------------------------------------- *)
(* Search (automatically updates)                                            *)
(* ------------------------------------------------------------------------- *)

let search =
  let rec immediatesublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> h1 = h2 && immediatesublist t1 t2 in
  let rec sublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> immediatesublist l1 l2 || sublist l1 t2 in
  let exists_subterm_satisfying p (n,th) = can (find_term p) (concl th)
  and name_contains s (n,th) = sublist (explode s) (explode n) in
  let rec filterpred tm =
    match tm with
      Comb(Var("<omit this pattern>",_),t) -> not o filterpred t
    | Comb(Var("<match theorem name>",_),Var(pat,_)) -> name_contains pat
    | Comb(Var("<match aconv>",_),pat) -> exists_subterm_satisfying (aconv pat)
    | pat -> exists_subterm_satisfying (can (term_match [] pat)) in
  fun pats ->
    update_database();
    let triv,nontriv = partition is_var pats in
    (if triv <> [] then
      warn true
         ("Ignoring plain variables in search: "^
          end_itlist (fun s t -> s^", "^t) (map (fst o dest_var) triv))
     else ());
    (if nontriv = [] && triv <> [] then []
     else sort (increasing fst)
               (itlist (filter o filterpred) pats (!theorems)));;

(* ------------------------------------------------------------------------- *)
(* Update to bring things back to current state.                             *)
(* ------------------------------------------------------------------------- *)

update_database();;

(* This printf checks whether standard modules like Printf are still alive
   after update_database.
   See also: https://github.com/ocaml/ocaml/issues/12271 *)
Printf.printf "update_database.ml loaded! # theorems: %d\n"
   (List.length !theorems);;
