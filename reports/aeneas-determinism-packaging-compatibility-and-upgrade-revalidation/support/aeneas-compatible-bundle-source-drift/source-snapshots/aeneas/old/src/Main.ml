open Aeneas.LlbcOfJson
open Aeneas.Logging
open Aeneas.LlbcAst
open Aeneas.Interp
module EL = Easy_logging.Logging
open Aeneas.Config
open Aeneas

(** The local logger *)
let log = main_log

let _ =
  (* Set up the logging - for now we use default values - TODO: use the
   * command-line arguments *)
  (* By setting a level for the main_logger_handler, we filter everything.
     To have a good trace: one should switch between Info and Debug.
     TODO: remove
  *)
  Easy_logging.Handlers.set_level main_logger_handler EL.Debug;
  (* Set the level for the Charon loggers (for the ones internal to Aeneas,
     the level was set up at creation time) *)
  main_log#set_level EL.Info;
  llbc_of_json_logger#set_level EL.Info

(* This is necessary to have a backtrace when raising exceptions - for some
 * reason, the -g option doesn't work.
 * TODO: run with OCAMLRUNPARAM=b=1? *)
let () = Printexc.record_backtrace true

let usage =
  Printf.sprintf
    {|Aeneas: verification of Rust programs by translation to pure lambda calculus

Usage: %s [OPTIONS] FILE
|}
    Sys.argv.(0)

let matches_name (c : crate) (name : Types.name)
    (m : 'a ExtractName.NameMatcherMap.t) : bool =
  let mctx = Charon.NameMatcher.ctx_from_crate c in
  let open ExtractBuiltin in
  NameMatcherMap.mem mctx name m

let matches_name_with_generics (c : crate) (name : Types.name)
    (generics : Types.generic_args) (m : 'a ExtractName.NameMatcherMap.t) : bool
    =
  let mctx = Charon.NameMatcher.ctx_from_crate c in
  let open ExtractBuiltin in
  Option.is_some (NameMatcherMap.find_with_generics_opt mctx name generics m)

let activated_loggers : (EL.level * string) list ref = ref []

let add_activated_loggers level (name_list : string) =
  let names = String.split_on_char ',' name_list in
  activated_loggers := List.map (fun n -> (level, n)) names @ !activated_loggers

let marked_ids : string list ref = ref []

let add_marked_ids (ids : string) =
  let ids = String.split_on_char ',' ids in
  marked_ids := ids @ !marked_ids

let () =
  (* Measure start time *)
  let start_time = Unix.gettimeofday () in

  (* Read the command line arguments *)
  let dest_dir = ref "" in

  (* Print the imported llbc *)
  let print_llbc = ref false in

  let set_max_heartbeats = ref false in
  let set_max_recdepth = ref false in

  let spec_ls =
    [
      ( "-version",
        Arg.Unit
          (fun () ->
            let v =
              match GitVersion.commit with
              | Some h -> h
              | None -> "unknown"
            in
            print_endline ("aeneas " ^ v);
            exit 0),
        " Print the version (git commit) and exit" );
      ( "-print-error-emitters",
        Arg.Set print_error_emitters,
        " Whenever reporting an error, print the span of the source code of \
         Aeneas which emitted the error" );
      ( "-borrow-check",
        Arg.Set borrow_check,
        " Only borrow-check the program and do not generate any translation" );
      ( "-backend",
        Arg.Symbol (backend_names, set_backend),
        " Specify the target backend (" ^ String.concat ", " backend_names ^ ")"
      );
      ( "-namespace",
        Arg.String set_namespace,
        " Set the namespace of the definitions in the pure model" );
      ("-dest", Arg.Set_string dest_dir, " Specify the output directory");
      ( "-subdir",
        Arg.String set_subdir,
        " Extract the files in a sub-folder; this option has an impact on the \
         import paths of the generated files" );
      ( "-test-units",
        Arg.Set test_unit_functions,
        " Test the unit functions with the concrete (i.e., not symbolic) \
         interpreter" );
      ( "-decreases-clauses",
        Arg.Set extract_decreases_clauses,
        " Use decreases clauses/termination measures for the recursive \
         definitions" );
      ( "-use-fuel",
        Arg.Set use_fuel,
        " Use a fuel parameter to control divergence" );
      ( "-no-template-clauses",
        Arg.Clear extract_template_decreases_clauses,
        " Do not generate templates for the required decreases \
         clauses/termination measures, in a dedicated file, if you also put \
         the option -decreases-clauses" );
      ( "-split-files",
        Arg.Set split_files,
        " Split the definitions between different files for types, functions, \
         etc." );
      ( "-checks",
        Arg.Set sanity_checks,
        " Activate extensive sanity checks (warning: causes a ~100 times slow \
         down)." );
      ( "-gen-lib-entry",
        Arg.Set generate_lib_entry_point,
        " Add an entry point file to the generated library (only valid if the \
         crate is split between different files)" );
      ( "-lean-default-lakefile",
        Arg.Clear lean_gen_lakefile,
        " Generate a default lakefile.lean (Lean only)" );
      ("-print-llbc", Arg.Set print_llbc, " Print the imported LLBC");
      ( "-abort-on-error",
        Arg.Set fail_hard,
        " Abort on the first encountered error" );
      ( "-warnings-as-errors",
        Arg.Set warnings_as_errors,
        " Treat warnings as errors" );
      ( "-tuple-nested-proj",
        Arg.Set use_nested_tuple_projectors,
        " Use nested projectors for tuples (e.g., (0, 1, 2).snd.fst instead of \
         (0, 1, 2).1)." );
      ( "-print-unknown-externals",
        Arg.Set print_unknown_externals,
        " Print all the external definitions which are not listed in the \
         builtin functions" );
      ( "-log",
        Arg.String (add_activated_loggers EL.Trace),
        " Activate trace log for a given logger designated by its name. It is \
         possible to specifiy a list of names if they are separated by commas \
         without spaces; for instance: '-log Interp,SymbolicToPure'. The \
         existing loggers are: {"
        ^ String.concat ", " (Collections.StringMap.keys !loggers)
        ^ "}" );
      ( "-log-debug",
        Arg.String (add_activated_loggers EL.Debug),
        " Same as '-log' but sets the level to the more verbose 'debug' rather \
         than 'trace'" );
      ( "-log-error",
        Arg.String (add_activated_loggers EL.Error),
        " Activate error log for a given logger designated by its name. It is \
         possible to specifiy a list of names if they are separated by commas \
         without spaces; for instance: '-log Interp,SymbolicToPure'. The \
         existing loggers are: {"
        ^ String.concat ", " (Collections.StringMap.keys !loggers)
        ^ "}" );
      ( "-mark-ids",
        Arg.String add_marked_ids,
        " For developers: mark some identifiers to throw an exception if we \
         generate them; this is useful to insert breakpoints when debugging by \
         using the log. For example, one can mark the symbolic value ids 1 and \
         2 with '-mark-ids s1,s2', or '-mark-ids s@1, s@2. The supported \
         prefixes are: 's' (symbolic value id), 'b' (borrow id), 'a' \
         (abstraction id), 'r' (region id), 'f' (pure free variable id)." );
      ("-sequential", Arg.Clear parallel, " Execute sequentially");
      ( "-no-progress-bar",
        Arg.Clear progress_bar,
        " Do not display a progress bar" );
      ( "-max-error-spans",
        Arg.Int (fun x -> max_error_spans := x),
        " Maximum number of local uses of an external definition which \
         triggered an error that we print (if < 0 we print them all)" );
      ( "-strict-joins",
        Arg.Clear recover_joins,
        " Report an error whenever joining contexts fails rather than \
         duplicating the code after the branching statement" );
      ( "-color",
        Arg.Set log_with_colors,
        " Use colors when printing log messages" );
      ( "-borrow-check-globals",
        Arg.Set borrow_check_globals,
        " Borrow-check globals - an over-simplification in the LLBC provided \
         by Charon for the global initialization functions currently prevents \
         us from borrow-checking globals which contain static references" );
      ( "-print-error-diagnostics",
        Arg.Set print_error_diagnostics,
        " Print additional diagnostics about the kind of errors encountered" );
      ( "-impl-namespace",
        Arg.Set method_names_in_impl_namespace,
        " For Lean: always prefix method names with \"impl\" to avoid \
         collisions with field projectors. Example: the `len` method in `impl \
         Struct { fn len(&self) -> usize { ... } }` would be named \
         `Struct.impl.len`." );
      ( "-all-computable",
        Arg.Set all_computable,
        " For Lean: do not insert `noncomputable section` at the top of the \
         extracted files if there are external definitions not covered by the \
         standard library." );
      ( "-loops-to-rec",
        Arg.Set loops_to_recursive_functions,
        " Always extract loops to recursive functions." );
      ( "-loops-no-rec",
        Arg.Set no_recursive_loops,
        " Never attempt to extract loops to recursive functions." );
      ( "-max-heartbeats",
        Arg.Int
          (fun x ->
            set_max_heartbeats := true;
            max_heartbeats := x),
        "For Lean: set the value of the `set_option maxHeartBeats ...` command \
         at the top of the generated files" );
      ( "-max-recdepth",
        Arg.Int
          (fun x ->
            set_max_recdepth := true;
            max_recdepth := x),
        "For Lean: set the value of the `set_option maxRecDepth ...` command \
         at the top of the generated files" );
      ( "-eval-drops",
        Arg.Clear drop_as_no_op,
        "Evaluate the drops. By default we do not borrow-check them by \
         treating them as no-ops." );
      ( "-diagnose-translation",
        Arg.Set diagnose_translation,
        " Measure the time it takes to translate every function and print the \
         results sorted from longest to shortest" );
      ( "-diagnose-micro-passes",
        Arg.Set diagnose_micro_passes,
        " Measure the time it takes to apply the micro-passes on every \
         function and print them from longest to shortest" );
      ( "-diagnose-detailed",
        Arg.Set diagnose_detailed,
        " In combination with -diagnose-micro-passes, compute per-function, \
         per -micro-pass time measurements" );
      ( "-diagnose-limit",
        Arg.Int (fun x -> diagnose_limit := x),
        " Upper bound on the number of lines printed for the -diagnose \
         options. If positive, print at most this many lines. If negative, \
         print everything" );
    ]
  in

  let spec = Arg.align spec_ls in
  let filenames = ref [] in
  let add_filename f = filenames := f :: !filenames in
  Arg.parse spec add_filename usage;
  let fail (print_doc : bool) =
    if print_doc then print_string usage;
    exit 1
  in

  (* Small helper to check the validity of the input arguments and print
     an error if necessary *)
  let check_arg_name name =
    assert (List.exists (fun (n, _, _) -> n = name) spec_ls)
  in

  let fail_with_error (msg : string) =
    log#serror msg;
    fail true
  in
  let fail_with_error_no_doc (msg : string) =
    log#serror msg;
    fail false
  in

  let check_arg_implies (arg0 : bool) (name0 : string) (arg1 : bool)
      (name1 : string) : unit =
    check_arg_name name0;
    check_arg_name name1;
    if (not arg0) || arg1 then ()
    else (
      log#error "Invalid command-line arguments: the use of %s requires %s"
        name0 name1;
      fail true)
  in

  let check_arg_not (arg0 : bool) (name0 : string) (arg1 : bool)
      (name1 : string) : unit =
    check_arg_name name0;
    check_arg_name name1;
    if (not arg0) || not arg1 then ()
    else (
      log#error
        "Invalid command-line arguments: the use of %s is incompatible with %s"
        name0 name1;
      fail true)
  in

  let check (cond : bool) (msg : string) =
    if not cond then fail_with_error msg
  in
  let check_no_doc (cond : bool) (msg : string) =
    if not cond then fail_with_error_no_doc msg
  in

  let check_not (cond : bool) (msg : string) =
    if cond then fail_with_error msg
  in

  (* Activate the loggers *)
  let activated_loggers_set = ref Collections.StringSet.empty in
  List.iter
    (fun (level, name) ->
      match Collections.StringMap.find_opt name !loggers with
      | None ->
          (* Find the loggers with the closest names *)
          let distances =
            List.map
              (fun s -> (StringUtils.levenshtein_distance name s, s))
              (Collections.StringMap.keys !loggers)
          in
          let min_dist =
            let min = ref (fst (List.hd distances)) in
            List.iter
              (fun (d, _) -> if d < !min then min := d else ())
              distances;
            !min
          in
          let closest =
            List.filter_map
              (fun (d, s) ->
                if d = min_dist then Some ("'" ^ s ^ "'") else None)
              distances
          in
          log#serror
            ("The logger '" ^ name
           ^ "' does not exist.\n\nThe existing loggers are: {"
            ^ String.concat ", " (Collections.StringMap.keys !loggers)
            ^ "}\n\n"
            ^
            match closest with
            | [ s ] -> "Did you mean " ^ s ^ "?\n"
            | _ ->
                "The closest logger names we found are:\n"
                ^ String.concat ", " closest ^ "\n");
          fail false
      | Some logger ->
          (* Check that we haven't activated the logger twice *)
          if Collections.StringSet.mem name !activated_loggers_set then begin
            log#serror
              ("The logger '" ^ name
             ^ "' is used twice in the '-log' and/or '-log-debug' option(s)");
            fail false
          end
          else begin
            activated_loggers_set :=
              Collections.StringSet.add name !activated_loggers_set;
            logger#set_level level
          end)
    !activated_loggers;

  (* Properly register the marked ids *)
  let marked_symbolic_value_ids = ref Values.SymbolicValueId.Set.empty in
  let marked_borrow_ids = ref Values.BorrowId.Set.empty in
  let marked_abs_ids = ref Values.AbsId.Set.empty in
  let marked_region_ids = ref Types.RegionId.Set.empty in
  let marked_fvar_ids = ref Pure.FVarId.Set.empty in
  let marked_meta_ids = ref Values.MetaId.Set.empty in
  let symbolic_expr_ids = ref SymbolicAst.SymbolicExprId.Set.empty in
  List.iter
    (fun id ->
      let i = if String.length id >= 2 && String.get id 1 = '@' then 2 else 1 in
      let sub = String.sub id i (String.length id - i) in
      match int_of_string_opt sub with
      | None ->
          log#serror
            ("Invalid identifier provided to option `-mark-ids`: '" ^ id
           ^ "': '" ^ sub ^ "' can't be parsed as an int");
          fail false
      | Some i -> (
          let open ContextsBase in
          match String.get id 0 with
          | 's' ->
              marked_symbolic_value_ids :=
                Values.SymbolicValueId.Set.add
                  (Values.SymbolicValueId.of_int i)
                  !marked_symbolic_value_ids
          | 'b' ->
              marked_borrow_ids :=
                Values.BorrowId.Set.add (Values.BorrowId.of_int i)
                  !marked_borrow_ids
          | 'a' ->
              marked_abs_ids :=
                Values.AbsId.Set.add (Values.AbsId.of_int i) !marked_abs_ids
          | 'r' ->
              marked_region_ids :=
                Types.RegionId.Set.add (Types.RegionId.of_int i)
                  !marked_region_ids
          | 'f' ->
              marked_fvar_ids :=
                Pure.FVarId.Set.add (Pure.FVarId.of_int i) !marked_fvar_ids
          | 'm' ->
              marked_meta_ids :=
                Values.MetaId.Set.add (Values.MetaId.of_int i) !marked_meta_ids
          | 'e' ->
              symbolic_expr_ids :=
                SymbolicAst.SymbolicExprId.Set.add
                  (SymbolicAst.SymbolicExprId.of_int i)
                  !symbolic_expr_ids
          | _ ->
              log#serror
                ("Invalid identifier provided to option: '" ^ id
               ^ "': the first character should be in {'s', 'b', 'a', 'r'}");
              fail false))
    !marked_ids;
  let marked_ids : ContextsBase.marked_ids =
    {
      symbolic_value_ids = !marked_symbolic_value_ids;
      borrow_ids = !marked_borrow_ids;
      abs_ids = !marked_abs_ids;
      region_ids = !marked_region_ids;
      pure_fvar_ids = !marked_fvar_ids;
      fun_call_ids = Values.FunCallId.Set.empty;
      dummy_var_ids = Values.DummyVarId.Set.empty;
      shared_borrow_ids = Values.SharedBorrowId.Set.empty;
      abs_fvar_ids = Values.AbsFVarId.Set.empty;
      loop_ids = Values.LoopId.Set.empty;
      meta_ids = !marked_meta_ids;
      symbolic_expr_ids = !symbolic_expr_ids;
    }
  in

  (* Sanity check (now that the arguments are parsed!) *)
  check_arg_implies
    (not !extract_template_decreases_clauses)
    "-no-template-clauses" !extract_decreases_clauses "-decreases-clauses";
  if not !extract_decreases_clauses then
    extract_template_decreases_clauses := false;
  (* Sanity check: the use of decrease clauses is not compatible with the use of fuel *)
  check_arg_not !use_fuel "-use-fuel" !extract_decreases_clauses
    "-decreases-clauses";
  check_arg_implies !generate_lib_entry_point "-gen-lib-entry" !split_files
    "-split-files";
  check_arg_not !generate_lib_entry_point "-gen-lib-entry"
    (Option.is_some !subdir) "-subdir";
  if !lean_gen_lakefile && not (backend () = Lean) then
    fail_with_error
      "The -lean-default-lakefile option is valid only for the Lean backend";
  if !set_max_heartbeats && not (backend () = Lean) then
    fail_with_error
      "The -max-heartbeats option is valid only for the Lean backend";
  if !set_max_recdepth && not (backend () = Lean) then
    fail_with_error
      "The -max-recdepth option is valid only for the Lean backend";

  check_arg_implies !diagnose_detailed "-diagnose-detailed"
    !diagnose_micro_passes "-diagnose-micro-passes";

  if !borrow_check then (
    check (!dest_dir = "") "Options -borrow-check and -dest are not compatible";
    check_not !split_files
      "Options -borrow-check and -split-files are not compatible";
    check_not !test_unit_functions
      "Options -borrow-check and -test-unit-functions are not compatible";
    check_not !extract_decreases_clauses
      "Options -borrow-check and -decreases-clauses are not compatible";
    check_not !use_fuel "Options -borrow-check and -use-fuel are not compatible";
    check_not !split_files
      "Options -borrow-check and -split-files are not compatible");
  check_arg_not
    !loops_to_recursive_functions
    "-loops-to-rec" !no_recursive_loops "-loops-no-rec";

  (* Check that the user specified a backend *)
  let _ =
    match !opt_backend with
    | Some _ ->
        check_not !borrow_check
          "Arguments `-backend` and `-borrow-check` are not compatible"
    | None ->
        check !borrow_check "Missing `-backend` or `-borrow-check` argument"
  in

  (* Set some options depending on the backend *)
  let _ =
    match !opt_backend with
    | None -> ()
    | Some backend -> (
        match backend with
        | FStar ->
            (* F* can disambiguate the field names *)
            record_fields_short_names := true;
            (* Introducing [massert] leads to type inferencing issues *)
            intro_massert := false
        | Coq ->
            (* Some patterns are not supported *)
            decompose_monadic_let_bindings := true;
            decompose_nested_let_patterns := true
        | Lean ->
            (* We don't support fuel for the Lean backend *)
            check_not !use_fuel
              "The Lean backend doesn't support the -use-fuel option";
            (* Lean can disambiguate the field names *)
            record_fields_short_names := true;
            (* We exploit the fact that the variant name should always be
               prefixed with the type name to prevent collisions *)
            variant_concatenate_type_name := false;
            (* *) merge_let_app_decompose_tuple := true;
            lift_pure_function_calls := true
        | HOL4 ->
            (* We don't support fuel for the HOL4 backend *)
            if !use_fuel then (
              log#error "The HOL4 backend doesn't support the -use-fuel option";
              fail true))
  in

  (* If running in parallel mode there can be racing conditions on the memoized
     elements. Precompute them so that it doesn't happen. *)
  let _ = ExtractBuiltin.builtin_globals_map () in
  let _ = ExtractBuiltin.builtin_types_map () in
  let _ = ExtractBuiltin.builtin_trait_decls_map () in
  let _ = ExtractBuiltin.builtin_trait_impls_map () in
  let _ = ExtractBuiltin.builtin_funs_map () in
  let _ = ExtractBuiltin.builtin_fun_effects_map () in

  (* Retrieve and check the filename *)
  let filename =
    match !filenames with
    | [ f ] ->
        (* TODO: update the extension *)
        if not (Filename.check_suffix f ".llbc") then (
          print_string ("Unrecognized file extension: " ^ f ^ "\n");
          fail true)
        else if not (Sys.file_exists f) then (
          print_string ("File not found: " ^ f ^ "\n");
          fail true)
        else f
    | _ ->
        (* For now, we only process one file at a time *)
        print_string usage;
        exit 1
  in
  (* Check the destination directory *)
  let dest_dir =
    if !dest_dir = "" then Filename.dirname filename else !dest_dir
  in

  (* Load the module *)
  match crate_of_json_file filename with
  | Error s ->
      log#error "error: %s\n" s;
      exit 1
  | Ok m ->
      (* Clear short names to make printing more deterministic. *)
      let m = { m with short_names = [] } in
      (* Logging *)
      log#linfo (lazy ("Imported: " ^ filename));
      if !print_llbc then
        log#linfo (lazy ("\n" ^ Print.crate_to_string m ^ "\n"))
      else log#ldebug (lazy ("\n" ^ Print.crate_to_string m ^ "\n"));

      (* Check that Charon was called with the `--preset=aeneas` option *)
      check_no_doc
        (m.options.preset = Some Aeneas)
        "Invalid option detected: the serialized crate was generated by Charon \
         without the `--preset=aeneas` option. Please regenerate the crate by \
         calling Charon with `--preset=aeneas`.\n";

      (* We don't support mutually recursive definitions with decreases clauses in Lean *)
      if
        !opt_backend = Some Lean && !extract_decreases_clauses
        && List.exists
             (function
               | Aeneas.LlbcAst.FunGroup (RecGroup (_ :: _)) -> true
               | _ -> false)
             m.declarations
      then (
        log#error
          "The Lean backend doesn't support the use of \
           decreasing_by/termination_by clauses with mutually recursive \
           definitions";
        fail true);

      (* Print the external definitions which are not listed in the builtin functions *)
      if !print_unknown_externals then (
        let open TranslateCore in
        let { type_decls; fun_decls; global_decls; trait_decls; trait_impls; _ }
            =
          m
        in
        (* Filter the definitions *)
        let type_decls =
          Types.TypeDeclId.Map.filter
            (fun _ (d : Types.type_decl) ->
              let names_map = ExtractBuiltin.builtin_types_map () in
              (not d.item_meta.is_local)
              && not (matches_name m d.item_meta.name names_map))
            type_decls
        in
        let fun_decls =
          LlbcAst.FunDeclId.Map.filter
            (fun _ (d : LlbcAst.fun_decl) ->
              let names_map = ExtractBuiltin.builtin_funs_map () in
              (not d.item_meta.is_local)
              && (not (matches_name m d.item_meta.name names_map))
              (* We also ignore the trait method declarations *)
              &&
              match d.src with
              | TraitDeclItem _ -> false
              | _ -> true)
            fun_decls
        in
        let global_decls =
          LlbcAst.GlobalDeclId.Map.filter
            (fun _ (d : LlbcAst.global_decl) ->
              let globals_map = ExtractBuiltin.builtin_globals_map () in
              (not d.item_meta.is_local)
              && not (matches_name m d.item_meta.name globals_map))
            global_decls
        in
        let trait_decls =
          LlbcAst.TraitDeclId.Map.filter
            (fun _ (d : LlbcAst.trait_decl) ->
              let names_map = ExtractBuiltin.builtin_trait_decls_map () in
              (not d.item_meta.is_local)
              && not (matches_name m d.item_meta.name names_map))
            trait_decls
        in
        let trait_impls =
          List.filter_map
            (fun (d : LlbcAst.trait_impl) ->
              let names_map = ExtractBuiltin.builtin_trait_impls_map () in
              match
                LlbcAst.TraitDeclId.Map.find_opt d.impl_trait.id m.trait_decls
              with
              | None -> None (* Just ignore it *)
              | Some trait_decl ->
                  if
                    (not d.item_meta.is_local)
                    && not
                         (matches_name_with_generics m trait_decl.item_meta.name
                            d.impl_trait.generics names_map)
                  then Some (d, trait_decl)
                  else None)
            (LlbcAst.TraitImplId.Map.values trait_impls)
        in
        (* Print *)
        let fmt_env = Print.crate_to_fmt_env m in
        let type_decls =
          List.map
            (fun (d : Types.type_decl) ->
              let pattern =
                LlbcAstUtils.name_with_crate_to_pattern_string
                  (Some d.item_meta.span) m d.item_meta.name
              in
              "Type decl (pattern: [" ^ pattern ^ "]]):\n"
              ^ Print.type_decl_to_string fmt_env d)
            (Types.TypeDeclId.Map.values type_decls)
        in
        let fun_decls =
          List.map
            (fun (d : LlbcAst.fun_decl) ->
              let pattern =
                LlbcAstUtils.name_with_crate_to_pattern_string
                  (Some d.item_meta.span) m d.item_meta.name
              in
              let d =
                (* FIXME: there is a bug in the formatter when splitting the predicates
                   and trait clauses between the inherited ones and the others (the
                   index is sometimes out of bounds).
                   See: https://github.com/AeneasVerif/charon/issues/482
                *)
                try Print.fun_decl_to_string fmt_env "" "  " d
                with _ -> "UNKNOWN"
              in
              "Fun decl (pattern: [" ^ pattern ^ "]]):\n" ^ d)
            (LlbcAst.FunDeclId.Map.values fun_decls)
        in
        let global_decls =
          List.map
            (fun (d : LlbcAst.global_decl) ->
              let pattern =
                LlbcAstUtils.name_with_crate_to_pattern_string
                  (Some d.item_meta.span) m d.item_meta.name
              in
              "Global decl (pattern: [" ^ pattern ^ "]]):\n"
              ^ Print.global_decl_to_string fmt_env "" "  " d)
            (LlbcAst.GlobalDeclId.Map.values global_decls)
        in
        let trait_decls =
          List.map
            (fun (d : LlbcAst.trait_decl) ->
              let pattern =
                LlbcAstUtils.name_with_crate_to_pattern_string
                  (Some d.item_meta.span) m d.item_meta.name
              in
              "Trait decl (pattern: [" ^ pattern ^ "]]):\n"
              ^ Print.trait_decl_to_string fmt_env "" "  " d)
            (LlbcAst.TraitDeclId.Map.values trait_decls)
        in
        let trait_impls =
          List.map
            (fun ((d, trait_decl) : LlbcAst.trait_impl * LlbcAst.trait_decl) ->
              let pattern =
                LlbcAstUtils.trait_impl_with_crate_to_pattern_string
                  (Some d.item_meta.span) m trait_decl d
              in
              "Trait impl (pattern: [" ^ pattern ^ "]]):\n"
              ^ Print.trait_impl_to_string fmt_env "" "  " d)
            trait_impls
        in

        log#linfo
          (lazy
            (String.concat "\n\n"
               (type_decls @ fun_decls @ global_decls @ trait_decls
              @ trait_impls)));
        ());

      (* Apply the pre-passes *)
      let m = Aeneas.PrePasses.apply_passes m in

      (* Test the unit functions with the concrete interpreter *)
      if !test_unit_functions then Test.test_unit_functions m;

      (* Translate or borrow-check the crate *)
      let extracted_opaque = ref false in
      if !borrow_check then Aeneas.BorrowCheck.borrow_check_crate m marked_ids
      else
        Aeneas.Translate.translate_crate filename dest_dir !Config.subdir m
          extracted_opaque marked_ids;

      let has_errors =
        if !Errors.error_list <> [] then true
        else (
          if !borrow_check then
            log#linfo (lazy "Crate successfully borrow-checked");
          false)
      in

      (* Print a warning if we had to extract opaque definitions and the option
         [-split-file] is not on *)
      if !extracted_opaque && not !split_files then
        log#lwarning
          (lazy
            "The crate contains extracted external, unknown definitions: we \
             advise using the option -split-files to allow manually providing \
             these definitions in separate files.");

      (* Print error diagnostics *)
      (if !print_error_diagnostics && !Errors.error_list <> [] then
         let
         (* Sort the unique errors by decreasing number of occurrences *)
         open
           Errors in
         log#linfo
           (lazy
             (let unique_errors = FileLineMap.to_list !unique_errors in
              let unique_errors =
                List.sort (fun (_, n) (_, n') -> n' - n) unique_errors
              in
              "Unique errors by decreasing number of occurrences:\n"
              ^ String.concat "\n"
                  (List.map
                     (fun ((file, line), num) ->
                       "file: " ^ file ^ ", line: " ^ string_of_int line
                       ^ ", occurrences: " ^ string_of_int num)
                     unique_errors))));

      (* Print total elapsed time *)
      log#linfo
        (lazy
          (Printf.sprintf "Total execution time: %f seconds"
             (Unix.gettimeofday () -. start_time)));

      (* *)
      if has_errors then exit 1
