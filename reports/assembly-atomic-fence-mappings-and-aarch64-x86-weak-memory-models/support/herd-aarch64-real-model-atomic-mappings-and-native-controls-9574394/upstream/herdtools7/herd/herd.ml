(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2013-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

(** Entry point to Herd  *)

open Herd_core
open Printf
open Archs
open Opts
open OptNames


(* exit codes *)

let exit_code_of_exn = function
  | Misc.Exit | Misc.UserError _ | Misc.Fatal _ -> 2
  | _ -> 1

(* Command line arguments *)
let args = ref []
let get_cmd_arg s = args := s :: !args

(* Helpers *)

open ArgUtils


(* Option list *)

let load_config s =
  LexConf_herd.lex
    (Opts.libfind !includes !debug.Debug_herd.files s)

let pp_default_model a =
  sprintf "%s=%s" (Archs.pp a)
    (Model.pp (Model.get_default_model !Opts.variant a))

let gen_model_opt s =
  parse_tag
    s
    (fun tag -> match Model.parse tag with
    | None -> false
    | Some _ as m -> model :=  m ; true)
    Model.tags
    (sprintf " Select model, defaults %s, %s, %s, %s, %s, %s, %s"
       (pp_default_model x86)
       (pp_default_model x86_64)
       (pp_default_model ppc)
       (pp_default_model arm)
       (pp_default_model aarch64)
       (pp_default_model riscv)
       (pp_default_model Archs.c))


(*Common options*)
let variant_option =
  begin
    let module ParseVariant = ParseTag.MakeS(Opts.OptS) in
    ParseVariant.parse "-variant" variant
      "<tags> select an architecture variation. Use '-help variant' for the list of tags" end 
let showevents_option =
  parse_tag "-showevents"
    (fun tag -> match PrettyConf.parse_showevents tag with
    | None -> false
    | Some t -> PP.showevents := t ; true)
     PrettyConf.tags_showevents
     (sprintf "Select events shown in figures, default %s"
       (PrettyConf.pp_showevents !PP.showevents)) 
let show_option =
  parse_tag "-show"
    (fun tag -> match PrettyConf.parse_show tag with
    | None -> false
    | Some t -> show := t ; true)
    PrettyConf.tags_show
    (sprintf "Executions shown in figure, default %s"
       (PrettyConf.pp_show !show)) 
let through_option =
  parse_tag
    "-through"
    (fun tag -> match Model.parse_through tag with
    | None -> false
    | Some t -> through :=  t ; true)
    Model.tags_through
    (sprintf
       "Allow additional executions to reach the final stage of the simulation in addition to valid ones, default %s"
       (Model.pp_through !through)) 
let v_option =
  ("-v", Arg.Unit (fun _ -> incr verbose), " show various diagnostics. Repeat to increase verbosity")

let view_option =
  begin 
    let module ParseView = ParseTag.Make(View) in
    ParseView.parse_opt "-view" PP.view
    "fork specified viewer to show output graphs" end 
let o_option =
  ("-o", Arg.String
     (fun s -> match s with
     | "-" -> outputdir := PrettyConf.StdoutOutput
     | _ -> outputdir := PrettyConf.Outputdir s),
   " select the <dir> in which output files are saved. If not set, then files are not generated.") 
let hexa_option =
  parse_bool "-hexa" PP.hexa "print numbers in hexadecimal"
let doshow_option =
  parse_stringsetfun "-doshow" PP.add_doshow "show those edges"
let unshow_option =
  parse_stringsetfun "-unshow" PP.add_unshow "do not show those edges" 
let skipcheck_option =
  ("-skipcheck",
   Arg.String (fun tag -> skipchecks := StringSet.add tag !skipchecks),
   "<name> do not apply check, cumulates") 
let conf_option =
  ("-conf", Arg.String load_config, 
  "<name> read configuration file <name>. Example: -conf herd/libdir/file.cfg") 
let cat_option =
  gen_model_opt "-cat"

let common_options = Arg.align ~limit:40 [
  variant_option ;
  showevents_option ;
  show_option ;
  through_option ;
  v_option ;
  view_option ;
  o_option ;
  hexa_option ;
  doshow_option ;
  unshow_option ;
  skipcheck_option ;
  conf_option ;
  cat_option ;
  "-help", Arg.Unit Fun.id, "" ;
  "--help", Arg.Unit Fun.id, "";
]
let runmode_options = Arg.align ~limit:40 [
  "-help", Arg.Unit Fun.id, "" ;
  "--help", Arg.Unit Fun.id, "" ;
  parse_tag "-speedcheck"
    (fun tag -> match Speed.parse tag with
    | None -> false
    | Some t -> speedcheck := t ; true)
    Speed.tags
    "Aim at checking condition in place of listing final states" ;
  variant_option ;
  begin 
    let module ParseMachSize = ParseTag.Make(MachSize.Tag) in
  ParseMachSize.parse "-machsize" byte "set basic machine size" end ;
  begin 
    let module ParseEndian = ParseTag.Make(Endian) in
  ParseEndian.parse_opt "-endian" endian "set endianness" end ;
  parse_float_opt "-timeout" Opts.timeout "timeout (CPU time)";
  ("-unroll",
   Arg.Int (fun x -> unroll := Some x),
   sprintf "<int> branch unrolling upper limit, default ASL: %i, others: %i"
     (unroll_default `ASL)  (unroll_default `Others));
  parse_tag "-optace"
    (fun tag -> match OptAce.parse tag with
    | None -> false
    | Some t -> optace := Some t ; true)
    OptAce.tags
    "Optimize axiomatic candidate generation, default is iico";
  parse_int_opt
    "-maxphantom" maxphantom "maximum phantom update (per variable)";
  parse_bool "-archcheck" archcheck "check compatibility of test and cat model architectures" ;
    ("-switch",
   Arg.Unit (fun () -> Misc.switch := true),
   " switch something") ;
  parse_tag "-restrict"
    (fun tag -> match Restrict.parse tag with
    | None -> false
    | Some t -> restrict := t ; true)
    Restrict.tags
    (sprintf "Restrict outcomes, default %s" (Restrict.pp !restrict));
    ]  

let filter_options = Arg.align ~limit:40 [
  "-help", Arg.Unit Fun.id, "" ;
  "--help", Arg.Unit Fun.id, "" ;
  gen_model_opt "-model";
  cat_option ;
  through_option;
  parse_string_opt
    "-throughflag"
    throughflag
    "let through executions flagged with string, and only those" ;
  skipcheck_option ;
  parse_stringset "-skipchecks" skipchecks "do not apply listed checks, cumulative" ;
  parse_bool "-strictskip" strictskip "retain outcomes allowed by ALL skipped checks" ;
  show_option;
  "-showflag",
  Arg.String  (fun flag -> show := PrettyConf.ShowFlag flag),
  "<string>  show executions flagged by string in figure" ;
  parse_bool "-badexecs" badexecs "give output for tests that have bad executions (see -badflag)" ;
  parse_string_opt "-badflag" badflag "executions with flag <string> are bad" ;
  "-statelessrc11",
  Arg.Bool (fun b -> if b then statelessrc11 := true),
  "<bool> enable stateless RC11 model checking, use with -variant normw, SC check can be skipped";
  "-dumpallfaults",
  Arg.Bool (fun b -> dumpallfaults := b),
  "<bool> show all faults in the output regardless of the post-condition";
  "-nshow",
  Arg.Int (fun n -> nshow := Some n),
  "<n> generate at most <n> execution graph. By default all execution graphs specified by -show are generated.";
  "-showone",
  Arg.Bool (fun b -> if b then nshow := Some 1),
  "<bool> alias for -nshow 1";
  parse_bool "-checkfilter" check_filter "discard outcomes that negate filter proposition (if any)" ;
  ]

let graph_content_options = Arg.align ~limit:40 [
  "-help", Arg.Unit (Fun.id), "" ;
  "--help", Arg.Unit (Fun.id), "" ;
  (* Edges *)
  ("\nEdge options:", Arg.Unit Fun.id, "\n");
  parse_bool "-showinitrf" PP.showinitrf "show read-from edges from initial state in pictures" ;
  parse_bool "-showfinalrf" PP.showfinalrf "show read-from edges to final state in pictures" ;
  doshow_option ;
  parse_bool "-showpo" PP.showpo "show po edges in pictures" ;
  unshow_option ;
  parse_stringset "-symetric" PP.symetric "declare those edges as symetric" ;
  parse_stringset "-noid" PP.noid "like -symetric, additionally do not show identity edges" ;
  parse_stringset "-showraw" PP.showraw "do not perform transitivity removal on those edges" ;

  (* Events *)
  ("\nEvent options:", Arg.Unit Fun.id, "\n");
  parse_bool "-oneinit" PP.oneinit "show an init writes pseudo-event, with all initial writes grouped" ;
  showevents_option;
  parse_bool "-showinitwrites" PP.showinitwrites
    "show init write events in pictures" ;
  parse_stringset "-cycles" cycles  "<name1,...,nameN> show failing checks as cycles, cumulates" ;
  parse_bool "-dumpes" Opts.dumpes "dump event structures";
 "-initwrites", Arg.Bool (fun b -> initwrites := Some b),
    "<bool> represent init writes as write events. This option should not be used except for debugging model options";
  parse_string_opt "-classes" PP.classes "show classes of this equivalence (do not cumulate)" ;
]
let graph_presentation_options = Arg.align ~limit:40 [
  "-help", Arg.Unit Fun.id, "" ;
  "--help", Arg.Unit Fun.id, "" ;
  parse_bool "-showobserved" PP.showobserved
    "highlight observed memory reads in execution graphs" ;
  parse_bool "-edgemerge" PP.edgemerge "merge edges, cppmem style" ;
  parse_bool "-showlegend" PP.showlegend  "show legend in pictures" ;
  parse_bool "-showkind" PP.showkind  "show test kind in legends" ;
  parse_bool "-shortlegend" PP.shortlegend "show test name only in legends";
  parse_bool "-labelinit" PP.labelinit "show labels on the init node" ;
  parse_bool "-showthread" PP.showthread "show thread numbers in execution graphs" ;
  parse_bool "-squished" PP.squished "limit information in graph nodes" ;
  parse_bool "-fixedsize" PP.fixedsize
    "fixedsize attribute for nodes in graph" ;
  parse_float "-extrachars" PP.extrachars
    "additional space for computing node width, can be negative" ;
  parse_bool "-brackets" PP.brackets
    "show brackets around locations in pictures" ;
  parse_pos "-initrfpos" PP.initdotpos
    "position of pseudo source event for initial rf" ;
  parse_pos "-finalrfpos" PP.initdotpos
    "position of pseudo target event for final rf" ;
  parse_pos_opt "-initpos" PP.initpos
    "position of the init writes pseudo-event" ;
  parse_tag "-splines"
    (fun tag -> match Splines.parse tag with
    | None -> false
    | Some Splines.No -> PP.splines := None; true
    | Some t -> PP.splines := Some t ; true)
    Splines.tags
    "Specify splines graph attribute, default none" ;
  parse_float_opt "-margin" PP.margin "margin attribute of graphs";
  parse_float_opt "-pad" PP.pad "pad attribute of graphs";
  parse_string_opt "-sep" PP.sep "specify graph sep attribute" ;
  parse_string_opt "-fontname" PP.fontname "fontname attribute in graphs" ;
  parse_int_opt "-fontsize" PP.fontsize "fontsize attribute in graphs" ;
  parse_int "-edgefontsizedelta" PP.edgedelta "value to add to edge fontsize" ;
  parse_float_opt "-penwidth" PP.penwidth "penwidth attribute in graphs" ;
  parse_float_opt "-arrowsize" PP.arrowsize "arrowsize attribute in graphs" ;
  "-edgeattr",
  Arg.String
    (fun tag -> match Misc.split_comma tag with
    | [lbl;a;v;] -> PP.add_edgeattr lbl a v
    | _ ->
        raise
          (Arg.Bad
             (sprintf "bad argument for option -edgeattr: '%s'" tag))),
  "<label,attribute,value> specify an attribute for edges labelled by label";
  parse_string_opt "-overlap" PP.overlap "specify graph overlap attribute" ;
   parse_tag "-graph"
    (fun tag -> match Graph.parse tag with
    | None -> false
    | Some t -> PP.graph := t ; true)
     Graph.tags
     (sprintf "Select sort of graph, default %s" (Graph.pp !PP.graph)) ;
  parse_tag "-dotmode"
    (fun tag -> match PrettyConf.parse_dotmode tag with
    | None -> false
    | Some t -> PP.dotmode := t ; true)
    PrettyConf.tags_dotmode
    (sprintf "Control text in dot figures, default %s"
       (PrettyConf.pp_dotmode !PP.dotmode)) ;
  parse_bool "-mono" PP.mono "monochrome figures" ;
  parse_float "-scale" PP.scale "global scale factor for graphs" ;
  parse_float "-xscale" PP.xscale
    "global scale factor for graphs, x direction" ;
  parse_float "-yscale" PP.yscale
    "global scale factor for graphs, y direction" ;
  parse_float "-dsiy" PP.dsiy "vertical variation for events generated by the same instruction" ;
  parse_float "-siwidth" PP.siwidth "width occupied by events generated by the same instruction" ;
  parse_float "-ptscale" PP.ptscale "scale factor for points" ;
  parse_float "-boxscale" PP.ptscale "scale factor box width" ;
  "-shift",
  Arg.String
    (fun tag ->
      let fs = Misc.split_comma tag in
      let fs =
        List.map
          (fun f ->
            try float_of_string f with
            | _ ->
                raise
                  (Arg.Bad
                     (sprintf "bad argument for option -shift: '%s'" tag)))
          fs in
      PP.shift := Array.of_list fs),
  "<float,...,float> add vertical space at thread start (column mode only)";
 parse_float "-threadposy" PP.threadposy
    "thread number position in the y direction" ;
  parse_bool "-relabel" PP.relabel
    "merge power/arm labels(e.g sync -> sync/dmb)" ;
  parse_bool "-withbox" PP.withbox
    "box together events generated by the same instruction" ;
  parse_bool "-labelbox" PP.labelbox
    "label instruction instruction boxes with instruction" ;
  parse_bool "-movelabel" PP.movelabel
    "apply various tricks to enhance edge label placement in pictures" ;
  ]

let setup_options = Arg.align ~limit:40 ([
   "-help", Arg.Unit Fun.id, "" ;
  "--help", Arg.Unit Fun.id, "";
  ("-version", Arg.Unit
     (fun () -> printf "%s, Rev: %s\n" Version.version Version.rev ; exit 0),
   " ") ;
  ("-libdir", Arg.Unit (fun () -> print_endline !Opts.libdir; exit 0),
    " show the default search path for .cat files and ASL pseudocode files");
  ("-set-libdir", Arg.String (fun s -> Opts.libdir := s),
    "<path> set the default search path for .cat files and ASL pseudocode files to <path>");
  v_option ;
  ("-q", Arg.Unit (fun _ -> verbose := -1; debug := Debug_herd.none),
   "<default> do not show diagnostics");
  ("-I", Arg.String (fun s -> includes := !includes @ [s]),
   "<dir> add <dir> to the search path for .cat files and ASL pseudocode files, takes precedence over libdir ");
  parse_bool "-exit" Opts.exit_if_failed "exit in case of failure";
  conf_option ;
  ("-web",
   Arg.Unit (fun () -> load_config "web.cfg")," alias for -conf web.cfg");
  ("-c11",
   Arg.Unit (fun () -> load_config "cpp11.cfg")," alias for -conf cpp11.cfg");
  ("-bell",
   Arg.String (fun x -> Opts.bell := (Some x)),
   "<name> read bell file <name>") ;
  ("-macros",
   Arg.String (fun x -> Opts.macros := (Some x)),
   "<name> read macro (.def) file <name>") ;
  o_option ;
  view_option ;
  ( "-gv",
    Arg.Unit (fun _ -> PP.view := Some View.GV),
    " alias for -view gv") ;
  ( "-evince",
    Arg.Unit (fun _ -> PP.view := Some View.Evince),
    " alias for -view evince") ;
  ( "-preview",
    Arg.Unit (fun _ -> PP.view := Some View.Preview),
    " alias for -view preview") ;
  parse_tag "-dotcom"
    (fun tag -> match PrettyConf.parse_dotcom tag with
    | None -> false
    | Some _ as t -> PP.dotcom := t ; true)
    PrettyConf.tags_dotcom
    "Select command to translate dot, default depends on other modes " ;
  parse_tags
    "-debug"
    (fun tag -> match Debug_herd.parse !debug tag with
    | None -> false
    | Some t -> debug := t ; true)
    Debug_herd.tags
    "Show debug messages for specific parts" ;

  (* Input *)
  ("\nInput options:", Arg.Unit Fun.id, "\n");

  ( "-kinds",
    Arg.String (fun s -> kinds := !kinds @ [s]),
    "<name> specify kind of tests (can be repeated)");
  LibOpts.parse_conds conds;
  ] @ parse_noselect @ [
  (* Output *)
  ("\nOutput options:", Arg.Unit Fun.id, "\n");

  ("-dotheader",Arg.String (fun s -> PP.dotheader := Some s),
   "<name> insert the contents of <name> at the beginning of generated dot files");
  parse_bool "-tikz" PP.tikz "generate dot files suitable for processing with TikZ";
  parse_bool "-texmacros" PP.texmacros "use latex commands in output";
  ("-suffix", Arg.String (fun s -> suffix := s),
   "<suf> add <suf> at the end of the base of generated files");
  parse_bool "-candidates" candidates
  "show complete candidate count in output" ;
  parse_bool "-outcomereads" outcomereads "include all memory reads in outcomes" ;
  hexa_option ;
   ])
  let help_options = Arg.align ~limit:40 [
  ("-help", Arg.Unit Fun.id, " alias of --help");
  ("--help", Arg.Unit Fun.id, " show help. Optional arguments: short or category" )
]
(*Usage messages*)
let usg_setup = (sprintf "\n Control the command environment: paths, config, input and output handling \n")
let usg_runmode = (sprintf "\n Configure herd \n")
let usg_filter = (sprintf"\n Select model and control which executions are filtered or allowed \n")
let usg_graph_content = (sprintf "\n Control what events and edges are included in the graph")
let usg_graph_presentation = (sprintf "\n Control graph layout, sizing, annotations and visual clarity \n")

let help_footer =
  "Use --help short for commonly used options and introduction to --help <category>."

let usage_line = "Usage: herd7 [options] [test]*"

let usg_default =
  String.concat "\n"
    [
      usage_line;
      "";
      Arg.usage_string common_options "Commonly-used options:\n";
"For advanced options, use `--help <category>`, where <category> is one of the following options:
  setup               Control the command environment: paths, config, input and
                      output handling
  runmode             Configure herd
  filter              Select model and control which executions are filtered or
                      allowed
  graph_content       Control what events and edges are included in the
                      graph
  graph_presentation  Control graph layout, sizing, annotations, and visual
                      clarity
  variant             List available variant tags

Help commands
  --help              Show all available options
  --help short        Show commonly-used options
  --help <category>   Show options for <category>
  -help               Alias of --help
";
    ]

let show_short_help () =
  print_endline usg_default;
  exit 0

let show_long_help () =
  print_endline usage_line;
  print_endline "";
  print_endline "Available options:";
  Printf.printf "%s" (Arg.usage_string setup_options usg_setup);
  Printf.printf "\n";
  Printf.printf "%s" (Arg.usage_string runmode_options usg_runmode);
  Printf.printf "\n";
  Printf.printf "%s" (Arg.usage_string filter_options usg_filter);
  Printf.printf "\n";
  Printf.printf "%s" (Arg.usage_string graph_content_options usg_graph_content);
  Printf.printf "\n";
  Printf.printf "%s" (Arg.usage_string graph_presentation_options usg_graph_presentation);
  Printf.printf "\n";
  Printf.printf "%s" (Arg.usage_string help_options "\n Help commands");
  print_endline "";
  print_endline help_footer;
  exit 0

let options = setup_options @
  runmode_options @
  filter_options @
  graph_content_options @
  graph_presentation_options @
  help_options

let is_known_category = function
  | "setup"
  | "runmode"
  | "filter"
  | "graph_content"
  | "graph_presentation"
  | "variant" -> true
  | _ -> false

let display_help = function
  | "setup" ->
      print_endline usage_line;
      Printf.printf "%s" (Arg.usage_string setup_options usg_setup); exit 0
  | "runmode" ->
      print_endline usage_line;
      Printf.printf "%s" (Arg.usage_string runmode_options usg_runmode); exit 0
  | "filter" ->
      print_endline usage_line;
      Printf.printf "%s" (Arg.usage_string filter_options usg_filter); exit 0
  | "graph_content" ->
      print_endline usage_line;
     Printf.printf "%s" (Arg.usage_string graph_content_options usg_graph_content); exit 0
  | "graph_presentation" ->
      print_endline usage_line;
     Printf.printf "%s" (Arg.usage_string graph_presentation_options usg_graph_presentation); exit 0
  | "variant" ->
      print_endline usage_line;
     Printf.printf "%s" (Variant.variants_help_page); exit 0
  | _ ->
     show_short_help ()

let handle_help_or_return () =
  let rec find_help = function
    | [] -> None
    | "-help" :: rest -> Some rest
    | "--help" :: rest -> Some rest
    | _ :: tl -> find_help tl
  in
  let inputs = Array.to_list Sys.argv |> List.tl in
  match find_help inputs with
  | None -> ()
  | Some [] -> show_long_help ()
  | Some (arg :: _) ->
      (match arg with
      | "-help" | "--help" -> show_long_help ()
      | "short" -> show_short_help ()
      | categ when is_known_category categ -> display_help categ
      | _ -> show_short_help ())

(* Parse command line *)
let () =
  try
    handle_help_or_return ();
    let current = ref 0 in
    Arg.parse_argv ~current Sys.argv (Arg.align options) get_cmd_arg usg_default;
  with
  | Arg.Bad msg -> 
    begin
      let first_line = String.trim msg |> String.split_on_char '\n' |> List.hd in
        Printf.eprintf "Error: %s\n %s \n" first_line usg_default;
        exit 2
      end
  | Misc.Fatal msg as e ->
      eprintf "%s: %s\n" prog msg ;
      exit (exit_code_of_exn e)

(* Read generic model, if any *)

let libfind = Opts.libfind !includes !debug.Debug_herd.files

module ParserConfig = struct
  let debug = !debug.Debug_herd.lexer
  let libfind =  libfind
end

let model,model_opts = match !model with
| Some (Model.File fname) ->
    let module P = ParseModel.Make(ParserConfig) in
    begin try
      let (fname,((b,_,_) as r)) = P.find_parse ~opt:true fname in
      Some (Model.Generic (fname,r)),b
    with
    | (Misc.Fatal msg | Misc.UserError msg) as e ->
        eprintf "%s: %s\n" prog msg ;
        exit (exit_code_of_exn e)
    | Misc.Exit as e ->
        eprintf "Failure of generic model parsing\n" ;
        exit (exit_code_of_exn e) end
| Some _ as m -> m,ModelOption.compat
| None -> None,ModelOption.default

(* Check names, NB no select argument! *)

module Verbose =
  struct let verbose = if !debug.Debug_herd.lexer  then !verbose else 0 end

module Check =
  CheckName.Make
    (struct
      include Verbose
      let rename = []
      let select = []
      let names = !names
      let oknames = !oknames
      let excl = !excl
      let nonames = !nonames
    end)

(* Read kinds/conds files *)
module LR = LexRename.Make(Verbose)

let kinds = LR.read_from_files !kinds ConstrGen.parse_kind

let conds = LR.read_from_files !conds (fun s -> Some s)

(* Configure parser/models/etc. *)
let () =
  let timer_module =
    if !debug.Debug_herd.timers then (module Timer.Ok:Timer.S)
    else (module Timer.No:Timer.S) in
  let module Config = struct
    let timeout = !timeout
    let candidates = !candidates
    let nshow = !nshow
    let restrict = !restrict
    let model = model
    let archcheck = !archcheck
    let through = !through
    let skipchecks = !skipchecks
    let strictskip = !strictskip
    let cycles = !cycles
    let outcomereads = !outcomereads
    let show = !show
    let badexecs = !badexecs
    let badflag = !badflag
    let throughflag = !throughflag
    let maxphantom = !maxphantom
    let statelessrc11 = !statelessrc11
    let dumpallfaults = !dumpallfaults

    let hash = HashInfo.Std
    let check_name = Check.ok
    let check_kind = TblRename.find_value_opt kinds
    let check_cond =  TblRename.find_value_opt conds
    let libfind = libfind
    let macros = !macros

    let model_enumco = model_opts.ModelOption.co
    let observed_finals_only = not model_enumco
    let initwrites = match !initwrites with
    | None -> model_opts.ModelOption.init
    | Some b -> b
    let check_filter = !check_filter
    let debug = !debug
    let debuglexer = debug.Debug_herd.lexer
    module Timer = (val timer_module : Timer.S)
    let verbose = !verbose
    let hexa = !PP.hexa
    let unroll = !unroll
    let speedcheck = !speedcheck
    let optace = match !optace with
    | Some b -> b
    | None -> match model with
      | Some (Model.Generic _|Model.File _)|None -> OptAce.Iico
      | Some (Model.CAV12 _) -> OptAce.False
    let variant = !variant
    let fault_handling = !Refs.fault_handling
    let mte_precision = !Refs.mte_precision
    let mte_store_only = !Refs.mte_store_only
    let sve_vector_length = !Refs.sve_vector_length
    let sme_vector_length = !Refs.sme_vector_length
    let byte = !byte
    let endian = !endian
    let outputdir = !outputdir
    let suffix = !suffix
    let dumpes = !dumpes

    module PC = struct
      let debug = debug.Debug_herd.pretty
      let verbose = verbose
      let dotmode = !PP.dotmode
      let dotcom = !PP.dotcom
      let view = !PP.view
      let showevents = !PP.showevents
      let showkind = !PP.showkind
      let shortlegend = !PP.shortlegend
      let texmacros = !PP.texmacros
      let tikz = !PP.tikz
      let hexa = !PP.hexa
      let mono = !PP.mono
      let fontname = !PP.fontname
      let fontsize = !PP.fontsize
      let edgedelta = !PP.edgedelta
      let penwidth = !PP.penwidth
      let arrowsize = !PP.arrowsize
      let splines = !PP.splines
      let overlap = !PP.overlap
      let sep = !PP.sep
      let margin = !PP.margin
      let pad = !PP.pad
      let scale = !PP.scale
      let xscale = !PP.xscale
      let yscale = !PP.yscale
      let dsiy = !PP.dsiy
      let siwidth = !PP.siwidth
      let boxscale = !PP.boxscale
      let ptscale = !PP.ptscale
      let squished = !PP.squished
      let graph = !PP.graph
      let showpo = !PP.showpo
      let relabel = !PP.relabel
      let withbox = !PP.withbox
      let labelbox = !PP.labelbox
      let showthread = !PP.showthread
      let showlegend = !PP.showlegend
      let showfinalrf = !PP.showfinalrf
      let showinitrf = !PP.showinitrf
      let finaldotpos = !PP.finaldotpos
      let initdotpos = !PP.initdotpos
      let oneinit = !PP.oneinit
      let initpos = !PP.initpos
      let threadposy = !PP.threadposy
      let showinitwrites = !PP.showinitwrites
      let brackets = !PP.brackets
      let showobserved = !PP.showobserved
      let movelabel = !PP.movelabel
      let fixedsize = !PP.fixedsize
      let extrachars = !PP.extrachars
      let edgeattrs = PP.get_edgeattrs ()
      let doshow = !PP.doshow
      let unshow = !PP.unshow
      let noid = !PP.noid
      let symetric = !PP.symetric
      let classes = !PP.classes
      let showraw = !PP.showraw

      let dotheader = match !PP.dotheader with
      | None -> None
      | Some f ->
          let fname = libfind f in
          try
            Misc.input_protect
              (fun chan ->
                let xs =
                  MySys.read_by_line chan (fun x xs -> x::xs) [] in
                Some (String.concat "\n" (List.rev xs)))
              fname
          with Sys_error msg ->
            eprintf "Cannot read %s: %s\n" f msg ;
            exit 2
      let shift = !PP.shift
      let edgemerge = !PP.edgemerge
      let labelinit = !PP.labelinit
      let variant = variant
    end

  end in

  let bi = match !Opts.bell with
  | None -> None
  | Some fname ->
      let module R =
        ReadBell.Make
          (struct
            let debug_lexer = Config.debug.Debug_herd.lexer
            let debug_model = Config.debug.Debug_herd.barrier
            let debug_files = Config.debug.Debug_herd.files
            let verbose = Config.verbose
            let libfind = libfind
            let compat = Config.variant Variant.BackCompat
            let prog = prog
            let variant = Misc.delay_parse Config.variant Variant.parse
          end) in
      let bi = R.read fname in
      Some (fname,bi) in

  let from_file f =
    let module T =
      Cli.Make
        (struct
          include GenParser.DefaultConfig
          let bell_model_info = bi
          include Config end) in
    SymbValue.reset_gensym () ;
    T.from_file f in


(* Just go *)

  let tests = !args in

  let check_exit exn =
    let b = !Opts.exit_if_failed in
    fun seen ->
      let e = exit_code_of_exn exn in
      if b then exit e else e, seen in

  let check_pos0 s =
    String.length s > 5 &&
    begin match s.[0],s.[1],s.[2],s.[3],s.[4] with
    | 'F','i','l','e',' ' -> true
    | _ -> false
    end  in

  let dbg_exc = !Opts.debug.Debug_herd.exc in

  let exit_code, _seen =

(* If interval timer enabled and triggered,
   then stop test with not output at all *)
    Itimer.set_signal
      Config.timeout
      (fun _ -> raise Misc.Timeout)
      !debug.Debug_herd.timeout;
    Misc.fold_argv_or_stdin
      (fun name ((exit_code, seen) as r) ->
        try exit_code, from_file name seen
        with
        | Misc.Timeout -> r
        | Misc.Exit as e ->
           if dbg_exc then raise e ;
           check_exit e seen
        | Misc.Fatal msg as e  ->
           if dbg_exc then raise e ;
           Warn.warn_always "%a: %s" Pos.pp_pos0 name msg ;
           check_exit e seen
        | Misc.UserError msg as e ->
           if dbg_exc then raise e ;
           begin if check_pos0 msg then
             Warn.warn_always "%s (User error)" msg
           else
             Warn.warn_always "%a: %s (User error)" Pos.pp_pos0 name msg
           end ;
           check_exit e seen
        | Asllib.Error.ASLException e as exc ->
           if dbg_exc then raise exc ;
           Warn.warn_always "%s" (Asllib.Error.error_to_string e);
           check_exit exc seen
        | e ->
           Printf.eprintf "\nFatal: %a Adios\n" Pos.pp_pos0 name ;
           raise e)
      tests (0, StringMap.empty) in
  exit exit_code
