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

open Libsail
open Ast_compare
open Ast_util
open Interactive.State

let opt_lean_output_dir : string option ref = ref None

let opt_lean_force_output : bool ref = ref false

let opt_lean_import_files : string list ref = ref []

let opt_lean_noncomputable : bool ref = ref false

let opt_lean_real_numbers : bool ref = ref false

let opt_single_file : bool ref = ref false

let opt_lean_executable : bool ref = ref false

let opt_lean_lib_path : string option ref = ref None

let opt_lean_lib_git : string option ref = ref None

let opt_lean_lib_rev : string option ref = ref None

(* We keep two flags to use the [If_flag] in the list of rewrites. They should never be equal. *)
let opt_enable_matchbv : bool ref = ref false
let opt_disable_matchbv : bool ref = ref true

let lean_version : string = "lean4:v4.29.0"
let mathlib_version : string = "v4.29.0"
let lib_default_git : string = "https://github.com/rems-project/lean-sail"
let lib_default_rev : string = "v7"

let lean_options =
  [
    ( Flag.create ~prefix:["lean"] ~arg:"directory" "output_dir",
      Arg.String (fun dir -> opt_lean_output_dir := Some dir),
      "set a custom directory to output generated Lean"
    );
    ( Flag.create ~prefix:["lean"] "force_output",
      Arg.Unit (fun () -> opt_lean_force_output := true),
      "removes the content of the output directory if it is non-empty"
    );
    ( Flag.create ~prefix:["lean"] "single_file",
      Arg.Unit (fun () -> opt_single_file := true),
      "puts the entire output in a single .lean file"
    );
    ( Flag.create ~prefix:["lean"] "matchbv",
      Arg.Unit
        (fun () ->
          opt_disable_matchbv := false;
          opt_enable_matchbv := true
        ),
      "use matchbv in the Lean output"
    );
    ( Flag.create ~prefix:["lean"] ~arg:"width" "line_width",
      Arg.Int (fun n -> Pretty_print_lean.opt_line_width := n),
      "maximum line length of the generated Lean code"
    );
    ( Flag.create ~prefix:["lean"] "noncomputable",
      Arg.Unit (fun () -> opt_lean_noncomputable := true),
      "add a 'noncomputable section' at the beginning of the output"
    );
    ( Flag.create ~prefix:["lean"] "real-numbers",
      Arg.Unit (fun () -> opt_lean_real_numbers := true),
      "enable real numbers (in particular, depend on mathlib)"
    );
    ( Flag.create ~prefix:["lean"] ~arg:"typename" "extern_type",
      Arg.String Pretty_print_lean.(fun ty -> opt_extern_types := ty :: !opt_extern_types),
      "do not generate a definition for the type"
    );
    ( Flag.create ~prefix:["lean"] ~arg:"file" "import_file",
      Arg.String (fun file -> opt_lean_import_files := file :: !opt_lean_import_files),
      "import this file in the generated model"
    );
    ( Flag.create ~prefix:["lean"] ~arg:"func-name" "noncomputable_function",
      Arg.String
        Pretty_print_lean.(fun fn -> opt_noncomputable_functions := IdSet.add (mk_id fn) !opt_noncomputable_functions),
      "do not generate executable code for this function"
    );
    ( Flag.create ~prefix:["lean"] ~arg:"func-name" "partial_function",
      Arg.String Pretty_print_lean.(fun fn -> opt_partial_functions := IdSet.add (mk_id fn) !opt_partial_functions),
      "disable the totality check for this function"
    );
    ( Flag.create ~prefix:["lean"] ~arg:"func-name" "non_beq_type",
      Arg.String Pretty_print_lean.(fun fn -> non_beq_types := IdSet.add (mk_id fn) !non_beq_types),
      "disable deriving a BEq instance for this type"
    );
    ( Flag.create ~prefix:["lean"] "executable",
      Arg.Unit (fun () -> opt_lean_executable := true),
      "generate an executable if there is a main function in the Sail program"
    );
    ( Flag.create ~prefix:["lean"] "lib-path",
      Arg.String (fun p -> opt_lean_lib_path := Some p),
      "(local) path of the Lean support library, for development"
    );
    ( Flag.create ~prefix:["lean"] "lib-repo",
      Arg.String (fun r -> opt_lean_lib_git := Some r),
      "url of the git repository of the Lean support library"
    );
    ( Flag.create ~prefix:["lean"] "lib-rev",
      Arg.String (fun r -> opt_lean_lib_rev := Some r),
      "revision of the Lean support library"
    );
  ]

(* TODO[javra]: Currently these are the same as the Coq rewrites, we might want to change them. *)
let lean_rewrites =
  let open Rewrites in
  [
    ("move_termination_measures", []);
    ("instantiate_outcomes", [String_arg "lean"; Bool_arg true]);
    ("realize_mappings", []);
    ("remove_vector_subrange_pats", []);
    ("remove_duplicate_valspecs", []);
    ("toplevel_string_append", []);
    ("pat_string_append", []);
    ("mapping_patterns", []);
    ("add_unspecified_rec", []);
    ("undefined", [Bool_arg true]);
    ("remove_not_pats", []);
    ("remove_impossible_int_cases", []);
    ("tuple_assignments", []);
    ("vector_concat_assignments", []);
    ("simple_assignments", []);
    ("remove_mixed_bitvector_literal_pats", [If_flag opt_disable_matchbv]);
    ("remove_vector_concat", [If_flag opt_disable_matchbv]);
    ("remove_bitvector_pats", [If_flag opt_disable_matchbv]);
    ("recheck_defs", []);
    (* ("remove_numeral_pats", []); *)
    (* ("pattern_literals", [Literal_arg "lem"]); *)
    ("fun_guarded_pats", [If_flag opt_enable_matchbv]);
    ("guarded_pats", [If_flag opt_disable_matchbv]);
    (* ("register_ref_writes", rewrite_register_ref_writes); *)
    ("nexp_ids", []);
    ("split", [String_arg "execute"]);
    ("minimise_recursive_functions", []);
    ("remove_bitfield_records", []);
    ("recheck_defs", []);
    (* Put prover regstate generation after removing bitfield records,
       which has to be followed by type checking *)
    (* ("prover_regstate", [Bool_arg false]); *)
    (* ("remove_assert", rewrite_ast_remove_assert); *)
    ("top_sort_defs", []);
    ("add_register_init_function", []);
    ("const_prop_mutrec", [String_arg "lean"]);
    ("exp_lift_assign", []);
    ("early_return", []);
    (* We need to do the exhaustiveness check before merging, because it may
       introduce new wildcard clauses *)
    ("recheck_defs", []);
    ("pattern_exhaustivity_redundancy", [If_flag opt_disable_matchbv]);
    (* merge funcls before adding the measure argument so that it doesn't
       disappear into an internal pattern match *)
    ("merge_function_clauses", []);
    ("recheck_defs", []);
    ("rewrite_loops_with_escape_effect", []);
    ("recheck_defs", []);
    ("infer_effects", [Bool_arg true]);
    ("attach_effects", []);
    ("remove_blocks", []);
    ("attach_effects", []);
    (* ("letbind_effects", []); *)
    ("remove_e_assign", []);
    (* ^^^^ replace loops by dummy function calls *)
    ("attach_effects", []);
    ("internal_lets", []);
    (* ^^^^ transforms var into let *)
    ("remove_superfluous_letbinds", []);
    ("remove_superfluous_returns", []);
    ("bit_lists_to_lits", []);
    ("toplevel_let_patterns", []);
    ("recheck_defs", []);
    ("attach_effects", []);
  ]

type lean_context = {
  out_name : string;
  out_name_camel : string;
  sail_dir : string;
  types_file : out_channel;
  funcs_file : out_channel;
  import_files : out_channel list;
  lakefile : out_channel;
  lakemanifest : out_channel;
}

let file_to_module (filename : string) =
  let base = Filename.basename filename in
  Filename.chop_extension base

let interface_module interface_v = if interface_v = 1 then "ConcurrencyInterfaceV1" else "ArchSem"

let file_prelude version namespace =
  let non_computable = if !opt_lean_noncomputable then "noncomputable section\n" else "" in
  Printf.sprintf
    {|set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.%s

%snamespace %s

|}
    (interface_module version) non_computable namespace

let path_to_static_library sail_dir str = Filename.quote (sail_dir ^ "/src/sail_lean_backend/Sail/" ^ str ^ ".lean")

let copy_from_static_library out_name_camel sail_dir lean_sail_dir str =
  Unix.system
    (Printf.sprintf "sed 's/THE_MODULE_NAME/%s/g' %s > %s.lean" out_name_camel (path_to_static_library sail_dir str)
       (lean_sail_dir ^ "/" ^ str |> Filename.quote)
    )
  |> ignore

let print_function_file_prelude interface_v file out_name_camel (imp_refs : string list) =
  let _ =
    match imp_refs with
    | [] ->
        output_string file "import Sail\n";
        output_string file ("import " ^ out_name_camel ^ ".Defs\n");
        List.iter
          (fun filename -> output_string file ("import " ^ out_name_camel ^ "." ^ file_to_module filename ^ "\n"))
          !opt_lean_import_files
    | ns -> List.iter (fun n -> output_string file ("import " ^ out_name_camel ^ "." ^ n ^ "\n")) ns
  in
  output_string file ("\n" ^ file_prelude interface_v out_name_camel);
  Printf.fprintf file "open %s\n\n" (interface_module interface_v);
  output_string file "namespace Functions\n\n"

let start_lean_output interface_v (out_name : string) (import_names : string list) (import_refs : string list list)
    (main_import_refs : string list) default_sail_dir =
  let base_dir = match !opt_lean_output_dir with Some dir -> dir | None -> "." in
  let project_dir = Filename.concat base_dir out_name in
  if !opt_lean_force_output && Sys.file_exists project_dir && Sys.is_directory project_dir then (
    let _ = Unix.system ("rm -r " ^ Filename.quote project_dir ^ "/*") in
    ()
  )
  else Unix.mkdir project_dir 0o775;
  let gitignore = open_out (Filename.concat project_dir ".gitignore") in
  (* Ignore the `.lake` directory generated by lake*)
  output_string gitignore "/.lake";
  close_out gitignore;
  let lean_toolchain = open_out (Filename.concat project_dir "lean-toolchain") in
  output_string lean_toolchain ("leanprover/" ^ lean_version);
  close_out lean_toolchain;
  let sail_dir = Reporting.get_sail_dir default_sail_dir in
  let out_name_camel = Libsail.Util.to_upper_camel_case out_name in
  let import_names_camel = List.map Libsail.Util.to_upper_camel_case import_names in
  let import_refs_camel = List.map (fun rs -> List.map Libsail.Util.to_upper_camel_case rs) import_refs in
  let main_import_refs_camel = List.map Libsail.Util.to_upper_camel_case main_import_refs in
  let lean_src_dir = Filename.concat project_dir out_name_camel in
  if not (Sys.file_exists lean_src_dir) then Unix.mkdir lean_src_dir 0o775;
  let real_numbers_file =
    if !opt_lean_real_numbers then "/src/sail_lean_backend/Sail/Real.lean"
    else "/src/sail_lean_backend/Sail/FakeReal.lean"
  in
  opt_lean_import_files := (sail_dir ^ real_numbers_file) :: !opt_lean_import_files;
  let specialization_file = if interface_v = 1 then "SpecializationV1.lean" else "SpecializationArchSem.lean" in
  opt_lean_import_files := (sail_dir ^ "/src/sail_lean_backend/Sail/" ^ specialization_file) :: !opt_lean_import_files;
  List.iter
    (fun filename ->
      let filepath = Filename.concat lean_src_dir (file_to_module filename) in
      Unix.system
        (Printf.sprintf "sed 's/THE_MODULE_NAME/%s/g' %s > %s.lean" out_name_camel (Filename.quote filename) filepath)
      |> ignore
    )
    !opt_lean_import_files;
  let types_file = open_out (Filename.concat lean_src_dir "Defs.lean") in
  output_string types_file "import Sail\n";
  output_string types_file "open PreSail\n\n";
  output_string types_file (file_prelude interface_v out_name_camel);
  let funcs_file = open_out (Filename.concat project_dir (out_name_camel ^ ".lean")) in
  let lakefile = open_out (Filename.concat project_dir "lakefile.toml") in
  let lakemanifest = open_out (Filename.concat project_dir "lake-manifest.json") in
  let import_files =
    List.map (fun name -> open_out (Filename.concat lean_src_dir (name ^ ".lean"))) import_names_camel
  in
  (* TODO get the last import name by other means than this fold *)
  let last_import_name =
    List.fold_left
      (fun prev_name (out, (n, imps)) ->
        print_function_file_prelude interface_v out out_name_camel imps;
        [n]
      )
      []
      (List.combine import_files (List.combine import_names_camel import_refs_camel))
  in
  let funcs_file_imports = main_import_refs_camel @ last_import_name in
  print_function_file_prelude interface_v funcs_file out_name_camel funcs_file_imports;
  { out_name; out_name_camel; sail_dir; types_file; funcs_file; import_files; lakefile; lakemanifest }

let close_context ctx =
  close_out ctx.types_file;
  close_out ctx.funcs_file;
  close_out ctx.lakefile;
  close_out ctx.lakemanifest

let output_support_lib ctx =
  output_string ctx.lakefile "\n\n[[require]]\n";
  output_string ctx.lakefile "name = \"Sail\"\n";
  let revision () = match !opt_lean_lib_rev with Some r -> r | None -> lib_default_rev in
  let path_and_rev =
    match (!opt_lean_lib_git, !opt_lean_lib_path) with
    | Some _, Some _ -> failwith "--lean-lib-git and --lean-lib-path cannot be set simultaneously"
    | None, Some p -> Printf.sprintf "path = \"%s\"\n" p
    | Some r, None -> Printf.sprintf "git = \"%s\"\nrev = \"%s\"" r (revision ())
    | None, None -> Printf.sprintf "git = \"%s\"\nrev = \"%s\"" lib_default_git (revision ())
  in
  output_string ctx.lakefile path_and_rev

let create_lake_project (ctx : lean_context) executable =
  (* Change the base directory if the option '--lean-output-dir' is set *)
  output_string ctx.lakefile
    ("name = \"" ^ ctx.out_name ^ "\"\ndefaultTargets = [\"" ^ ctx.out_name_camel
   ^ "\"]\nmoreLeanArgs = [\"--tstack=400000\"]\n\n[[lean_lib]]\nname = \"" ^ ctx.out_name_camel ^ "\""
    );
  output_string ctx.lakefile "\nleanOptions.weak.linter.style.nameCheck = false";
  output_string ctx.lakefile "\nmoreLeancArgs= [\"-fbracket-depth=500\"]";
  output_support_lib ctx;
  if !opt_lean_real_numbers then (
    output_string ctx.lakefile "\n\n[[require]]\n";
    output_string ctx.lakefile "name = \"mathlib\"\n";
    output_string ctx.lakefile "git = \"https://github.com/leanprover-community/mathlib4-nightly-testing\"";
    output_string ctx.lakefile (Printf.sprintf "rev = \"%s\"" mathlib_version)
  );
  if executable then (
    output_string ctx.lakefile "\n\n[[lean_exe]]\n";
    output_string ctx.lakefile "name = \"run\"\n";
    output_string ctx.lakefile ("root = \"" ^ ctx.out_name_camel ^ "\"\n")
  );
  output_string ctx.lakemanifest
    ("{\"version\": \"1.1.0\",\n \"packagesDir\": \".lake/packages\",\n \"packages\": [],\n \"name\": \"" ^ ctx.out_name
   ^ "\",\n \"lakeDir\": \".lake\"}\n"
    )

let rec dedup_files (files : string list) (acc : string list) =
  match files with
  | [] -> acc
  | f :: fs -> (
      match List.fold_left (fun n y -> if y = f then n + 1 else n) 0 acc with
      | 0 -> dedup_files fs (acc @ [f])
      | n -> dedup_files fs (acc @ [f ^ Int.to_string (n - 1)])
    )

let output (out_name : string) symbols env effect_info ({ defs; _ } as ast : Libsail.Type_check.typed_ast)
    default_sail_dir single_file noncomputable =
  let interface_v = if Preprocess.have_symbol "CONCURRENCY_INTERFACE_V2" symbols then 2 else 1 in
  let cg = Callgraph.graph_of_ast ast in
  let files, import_sets, main_import_set =
    if single_file then ([], [], [])
    else (
      let import_sets = Pretty_print_lean.collect_imports cg defs in
      (* Collect all non-empty slices between include pragmas in the file *)
      let import_files = Pretty_print_lean.collect_import_files defs (out_name ^ ".sail") in
      let import_files = List.map file_to_module import_files in
      (* Discard the last import file, as we will use the main file instead *)
      let import_files = Util.butlast import_files in
      (* Disambiguate import files *)
      let import_files = dedup_files import_files [] in
      (* Convert the integers in import_sets into Lean module names *)
      let import_refs : string list list =
        List.map
          (fun is ->
            let is = Pretty_print_lean.IntSet.elements is in
            List.filter_map (List.nth_opt import_files) is
          )
          import_sets
      in

      (import_files, Util.butlast import_refs, Util.last import_refs)
    )
  in
  let ctx = start_lean_output interface_v out_name files import_sets main_import_set default_sail_dir in
  let out_name_camel = Libsail.Util.to_upper_camel_case out_name in
  let executable =
    Pretty_print_lean.pp_ast_lean symbols env effect_info ast out_name_camel ctx.types_file ctx.import_files
      ctx.funcs_file
  in
  create_lake_project ctx (executable && !opt_lean_executable)
(* Uncomment for debug output of the Sail code after the rewrite passes *)
(* Pretty_print_sail.output_ast stdout (Type_check.strip_ast ast) *)

let lean_target out_name { default_sail_dir; symbols; ctx; ast; effect_info; env; _ } =
  let out_name = match out_name with Some f -> f | None -> "out" in
  output out_name symbols env effect_info ast default_sail_dir !opt_single_file !opt_lean_noncomputable

let _ = Target.register ~name:"lean" ~options:lean_options ~rewrites:lean_rewrites ~asserts_termination:true lean_target
