open Utils
(*--------------------------------------------------------------------- *)
let version_string = "Jasmin Compiler @VERSION@"
(*--------------------------------------------------------------------- *)
let outfile = ref ""
let dwarf = ref false
let debug = ref false
let timings = ref false
let print_list = ref []
let print_liveness = ref false
let slice = ref []
let stop_after = ref None
let trust_aligned = ref false

let help_version = ref false
let help_intrinsics = ref false
type color = | Auto | Always | Never
let color = ref Auto

let print_stack_alloc = ref false
let print_export_info_json = ref false
let introduce_export_renaming = ref true
let print_dependencies = ref false
let lazy_regalloc = ref false
let function_sections = ref false

(* Whether every function is laid out in a section of its own. Mach-O has no
   ELF sections, and the directives that go with them do not exist there, so
   the option is silently ignored on that system: the output of a macOS
   target never depends on it. *)
let use_function_sections () =
  !function_sections && not (is_target_system_macos ())

let verbosity = ref 1

let linting_level = ref 1

let set_linting_level i =
  if 0 <= i && i <= 2 then begin
      linting_level := i;
      if i = 0 then
        remove_warning Linter
      else
        add_warning Linter ()
    end
  else
    hierror ~loc:Lnone ~kind:"parsing arguments"
      "unknown linting level (should be 0, 1, or 2)"

let enable_all_warnings () =
  linting_level := 2;
  set_all_warnings ()

let do_auto_spill = ref None
let set_auto_spill () = do_auto_spill := Some AutoSpill.OptIn
let set_auto_spill_all () = do_auto_spill := Some AutoSpill.OptOut

let stack_zero_strategy = ref None
let stack_zero_strategies =
  let open Stack_zero_strategy in
  let assoc = function
    | SZSloop -> "loop"
    | SZSloopSCT -> "loopSCT"
    | SZSunrolled -> "unrolled"
  in
  List.map (fun s -> (assoc s, s)) stack_zero_strategy_list
let set_stack_zero_strategy s =
  stack_zero_strategy := Some (List.assoc s stack_zero_strategies)
let stack_zero_size = ref None
let set_stack_zero_size s = stack_zero_size := Some (Annot.ws_of_string s)

let callee_saved_strategy_options =
  [ "tight", CSS_Tight; "pessimistic", CSS_Pessimistic; "optimistic", CSS_Optimistic ]

let callee_saved_strategy = ref CSS_Tight

let set_callee_saved_strategy s =
  callee_saved_strategy := List.assoc s callee_saved_strategy_options

let target_arch = ref X86_64

let set_target_arch a =
  let a' =
    match a with
    | "x86-64" -> X86_64
    | "arm-m4" -> ARM_M4
    | "armv8a" -> ARMv8A
    | "riscv" -> RISCV
    | _ -> assert false
  in target_arch := a'

type x86_assembly_style = [`ATT | `Intel ]
let assembly_style : x86_assembly_style ref = ref `ATT

let set_syntax style () = assembly_style := style

let set_printing p () =
  print_list := p :: !print_list

let set_stop_after p () = 
  stop_after := Some p

let set_all_print () =
  print_list := Compiler.compiler_step_list

let set_slice f =
  slice := f :: !slice

let set_color c =
  let assoc = function
    | "auto"   -> Auto
    | "always" -> Always
    | "never"  -> Never
    | _        -> assert false
  in
  color := assoc c

let idirs = ref []

let set_idirs s =
  let colons = String.count_char s ':' in
  let equals = String.count_char s '=' in
  let idir =
    match (equals, colons) with
    | 1, 0 -> String.split ~by:"=" s
    | 0, 1 ->
       warning Deprecated Location.i_dummy
         "Use of colon in path:ident is deprecated: use an equal sign instead";
       String.split ~by:":" s
    | _, _ ->
       hierror ~loc:Lnone ~kind:"parsing arguments"
         "bad format for -I : ident=path expected"
  in
  idirs := idir :: !idirs

type call_conv = Linux | Windows

let call_conv = ref Linux (* Default value is chosen on start-up in `main_compiler` *)

let set_cc cc = 
  let cc = 
    match cc with
    | "windows" -> Windows
    | "linux" -> Linux
    | _ -> assert false
  in call_conv := cc

let print_strings = function
  | Compiler.RemoveAssertion             -> "rmassert", "remove logical assertion"
  | Compiler.Typing                      -> "typing"   , "typing"
  | Compiler.ParamsExpansion             -> "cstexp"   , "param expansion"
  | Compiler.InsertRenaming              -> "rename"   , "add renaming assignments at export function boundaries"
  | Compiler.WintWord                    -> "wintword" , "replace wint by word"
  | Compiler.ArrayCopy                   -> "arraycopy", "array copy"
  | Compiler.AddArrInit                  -> "addarrinit", "add array initialisation"
  | Compiler.LowerSpill                  -> "lowerspill", "lower spill/unspill instructions"
  | Compiler.Inlining                    -> "inline"   , "inlining"
  | Compiler.RemoveUnusedFunction        -> "rmfunc"   , "remove unused function"
  | Compiler.Unrolling                   -> "unroll"   , "unrolling"
  | Compiler.Splitting                   -> "splitting", "liverange splitting"
  | Compiler.Renaming                    -> "renaming" , "variable renaming to remove copies"
  | Compiler.RemovePhiNodes              -> "rmphi"    , "remove phi nodes introduced by splitting"
  | Compiler.DeadCode_Renaming           -> "renamingd", "dead code after variable renaming to remove copies"
  | Compiler.RemoveArrInit               -> "rmarrinit", "remove array initialisation"
  | Compiler.RegArrayExpansion           -> "arrexp"   , "expansion of register arrays"
  | Compiler.RemoveGlobal                -> "rmglobals", "remove globals variables"
  | Compiler.MakeRefArguments            -> "makeref"  , "add assignments before and after call to ensure that arguments and results are ref ptr"
  | Compiler.LoadConstantsInCond         -> "loadconst", "introduce registers for constants appearing in conditions (RISC-V only)"
  | Compiler.LowerInstruction            -> "lowering" , "lowering of instructions"
  | Compiler.PropagateInline             -> "propagate", "propagate inline variables"
  | Compiler.SLHLowering                 -> "slhlowering" , "lowering of selective load hardening instructions"
  | Compiler.LowerAddressing             -> "loweraddr", "lowering of complex addressing modes (RISC-V only)"
  | Compiler.StackAllocation             -> "stkalloc" , "stack allocation"
  | Compiler.RemoveReturn                -> "rmreturn" , "remove unused returned values"
  | Compiler.RegAllocation               -> "ralloc"   , "register allocation"
  | Compiler.DeadCode_RegAllocation      -> "rallocd"  , "dead code after register allocation"
  | Compiler.Linearization               -> "linear"   , "linearization"
  | Compiler.StackZeroization            -> "stackzero", "stack zeroization"
  | Compiler.Tunneling                   -> "tunnel"   , "tunneling"
  | Compiler.Assembly                    -> "asm"      , "generation of assembly"

let compiler_step_symbol =
  List.map (fun s -> fst (print_strings s)) Compiler.compiler_step_list

let symbol2pass =
  let tbl = Hashtbl.create 101 in
  List.iter (fun s -> Hashtbl.add tbl (fst (print_strings s)) s) Compiler.compiler_step_list;
  fun s -> Hashtbl.find tbl s

let print_option p =
  let s, msg = print_strings p in
  ("-p"^s, Arg.Unit (set_printing p), " Print program after "^msg)

let stop_after_option p = 
  let s, msg = print_strings p in
  ("-until_"^s, Arg.Unit (set_stop_after p), " Stop after "^msg)

let options = [
    "-version" , Arg.Set help_version  , " Display version information about this compiler (and exit)";
    "-o"       , Arg.Set_string outfile, "[filename] Name of the output file";
    "-g"       , Arg.Set dwarf         , " Emit DWARF2 line number information";
    "-debug"   , Arg.Set debug         , " Print debug information";
    "-timings" , Arg.Set timings       , " Print a timestamp and elapsed time after each pass";
    "-I"       , Arg.String set_idirs  , "[ident=path] Bind ident to path for from ident require ...";
    "-slice"    , Arg.String set_slice  , "[f] Keep function [f] and everything it needs";
    "-wlea", Arg.Unit (add_warning UseLea), " Print warning when lea is used";
    "-wea", Arg.Unit (add_warning ExtraAssignment), " Print warning when extra assignment is introduced";
    "-winsertarraycopy", Arg.Unit (add_warning IntroduceArrayCopy), " Print warning when array copy is introduced";
    "-wduplicatevar", Arg.Unit (add_warning DuplicateVar), " Print warning when two variables share the same name";
    "-wunusedvar", Arg.Unit (add_warning UnusedVar), " Print warning when a variable is not used";
    "-noinsertrenaming", Arg.Clear introduce_export_renaming, " Do not automatically insert renaming assignments at export function boundaries";
    "-wall", Arg.Unit enable_all_warnings, " Enable all warnings";
    "-nowarning", Arg.Unit (nowarning), " Do no print warnings";
    "-linting-level", Arg.Int set_linting_level, "[n] Set linting level to n (defaults to 1; disable linting when set to 0)";
    "-color", Arg.Symbol (["auto"; "always"; "never"], set_color), " Print messages with color";
    "-help-intrinsics", Arg.Set help_intrinsics, " List the set of intrinsic operators (and exit)";
    "-auto-spill", Arg.Unit set_auto_spill, " Enable naive spilling of #[spill]-annotated variables";
    "-auto-spill-all", Arg.Unit set_auto_spill_all, " Enable naive spilling of all reg variables";
    "-print-stack-alloc", Arg.Set print_stack_alloc, " Print the results of the stack allocation OCaml oracle";
    "-print-export-info-json", Arg.Set print_export_info_json, " Print information about exported functions in json";
    "-lazy-regalloc", Arg.Set lazy_regalloc, " Allocate variables to registers in program order";
    "-callee-saved",
      Arg.Symbol (List.map fst callee_saved_strategy_options, set_callee_saved_strategy),
      " Configure how callee-saved registers are spilled in export functions";
    "-pall"    , Arg.Unit set_all_print, " Print program after each compilation steps";
    "-print-dependencies", Arg.Set print_dependencies, " Print dependencies and exit";
    "-intel", Arg.Unit (set_syntax `Intel), " Use intel syntax (default is AT&T)"; 
    "-ATT", Arg.Unit (set_syntax `ATT), " Use AT&T syntax (default is AT&T)"; 
    "-call-conv", Arg.Symbol (["windows"; "linux"], set_cc), " Select calling convention (default depends on host architecture)";
    "-arch", Arg.Symbol (["x86-64"; "arm-m4"; "armv8a"; "riscv"], set_target_arch), " Select target arch (default is x86-64)";
    "-system", Arg.Symbol (["macosx"; "linux"], set_target_system), " Select target system (default is "^ Config.target_system^")";
    "-function-sections", Arg.Set function_sections, " Place each function in its own section (ELF only)";
    "-stack-zero",
      Arg.Symbol (List.map fst stack_zero_strategies, set_stack_zero_strategy),
      " Select stack zeroization strategy for export functions";
    "-stack-zero-size",
      Arg.Symbol (List.map fst Annot.ws_strings, set_stack_zero_size),
      " Select stack zeroization size for export functions";
    "-pliveness", Arg.Set print_liveness, " Print liveness information during register allocation"
  ] @  List.map print_option Compiler.compiler_step_list @ List.map stop_after_option Compiler.compiler_step_list

let usage_msg = "Usage : jasminc [option] filename"



(* -------------------------------------------------------------------- *)
let eprint step pp_prog p =
  if !timings then
    Format.eprintf "%t after %s@." pp_now (fst (print_strings step));
  if List.mem step !print_list then begin
    let (_, msg) = print_strings step in
    Format.printf
"/* -------------------------------------------------------------------- */@.";
    Format.printf "/* After %s */@.@." msg;
    Format.printf "%a@.@.@." pp_prog p
    end;
  if !stop_after = Some step then exit 0
