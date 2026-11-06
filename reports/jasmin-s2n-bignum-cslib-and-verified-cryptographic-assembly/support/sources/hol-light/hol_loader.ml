(* ========================================================================= *)
(*                               HOL LIGHT                                   *)
(*                                                                           *)
(*              Modern OCaml version of the HOL theorem prover               *)
(*                                                                           *)
(*                            John Harrison                                  *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2024                       *)
(*              (c) Copyright, Juneyoung Lee 2024                            *)
(* ========================================================================= *)

let hol_dir = ref
  (try Sys.getenv "HOLLIGHT_DIR" with Not_found -> Sys.getcwd());;

(* ------------------------------------------------------------------------- *)
(* Load files from system and/or user-settable directories.                  *)
(* Paths map initial "$/" to !hol_dir dynamically; use $$ to get the actual  *)
(* $ character at the start of a directory.                                  *)
(* ------------------------------------------------------------------------- *)

(* A flag that sets whether use_file must raise Failure if loading the file  *)
(* did not succeed. If set to true, this helps (nested) loading of files fail*)
(* early. However, propagation of the failure will cause Toplevel to forget  *)
(* bindings ('let .. = ..;;') that have been made before the erroneous       *)
(* statement in the file. This leads to an inconsistent state between        *)
(* variable and defined constants in HOL Light.                              *)
let use_file_raise_failure = ref false;;

let file_loader = ref (fun (s:string) -> failwith "uninitialized"; false);;

let use_file s =
  if !file_loader s then ()
  else if !use_file_raise_failure
  then failwith("Error in included file "^s)
  else (Format.print_string("Error in included file "^s);
        Format.print_newline());;

let hol_expand_directory s =
  if s = "$" || s = "$/" then !hol_dir
  else if s = "$$" then "$"
  else if String.length s <= 2 then s
  else if String.sub s 0 2 = "$$" then (String.sub s 1 (String.length s - 1))
  else if String.sub s 0 2 = "$/"
  then Filename.concat (!hol_dir) (String.sub s 2 (String.length s - 2))
  else s;;

let load_path = ref ["."; "$"];;

(* Read the HOLLIGHT_LOAD_PATH env variable *)
let p = try Sys.getenv "HOLLIGHT_LOAD_PATH" with Not_found -> "" in
let new_paths:string list =
  (* Separator, to split p into multiple paths *)
  let sep = if Sys.win32 then ';' else (* Cygwin and Unix *) ':' in

  (* Tokenize. Avoid using Str.regexp which needs to load the Str module *)
  let prev_idx = ref 0 in
  let escaped = ref false in
  let quote = ref None (* either Some '\'' or Some '"' *) in
  let l = String.length p in
  let new_paths = ref [] in

  for i = 0 to l - 1 do
    (* Was p[i-1] a backslash ('\\')? *)
    if !escaped then escaped := false else

    (* Is it inside a quotation ("..." or '...')? *)
    if !quote <> None then
      (* Is p[i] closing the quotation? *)
      if !quote = Some p.[i] then quote := None
      else ()
    else

    (* Is it a separator (':' or ';')? *)
    if p.[i] = sep then begin
      new_paths := !new_paths @ [String.sub p !prev_idx (i - !prev_idx)];
      prev_idx := i + 1
    end else if p.[i] = '\\' then
      (* escaping the next character *)
      escaped := true
    else if (p.[i] = '\'' || p.[i] = '"') then
      (* it is opening a quotation *)
      quote := Some p.[i]
    else ()
  done;
  (* add the remaining string *)
  new_paths := !new_paths @ [String.sub p !prev_idx (l - !prev_idx)];
  !new_paths in
load_path := !load_path @ new_paths;;

let loaded_files = ref [];;

let file_on_path p s =
  if not (Filename.is_relative s) then s else
  let p' = List.map hol_expand_directory p in
  let d = List.find (fun d -> Sys.file_exists(Filename.concat d s)) p' in
  Filename.concat (if d = "." then Sys.getcwd() else d) s;;

let load_on_path p s =
  let s' = file_on_path p s in
  let fileid = (Filename.basename s',Digest.file s') in
  let old_loaded_files = !loaded_files in
  try
    use_file s'; loaded_files := fileid::(!loaded_files)
  with f ->
    (* Exception in use_file implies that s' could not be loaded and
       use_file_raise_failure was true. Rollback any updates in
       loaded_files. *)
    (loaded_files := old_loaded_files; raise f);;

let loads s = load_on_path ["$"] s;;

let loadt s = load_on_path (!load_path) s;;

let needs s =
  let s' = file_on_path (!load_path) s in
  let fileid = (Filename.basename s',Digest.file s') in
  if List.mem fileid (!loaded_files)
  then Format.print_string("File \""^s^"\" already loaded\n") else loadt s;;
