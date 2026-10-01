(*
   The easiest way of using the helpers below is to use the PPX macros that are
   introduced in the [aeneas-ppx] library. For example, [[%craise]] expands to
   [craise __FILE__ __LINE__].

   The convention is simple: if a function has name [NAME], then [[%NAME]]
   expands to [NAME __FILE__ __LINE__].
 *)

let log = Logging.errors_log
let error_mutex = Mutex.create ()

let span_data_to_string (span_data : Meta.span_data) =
  let file =
    match span_data.file.name with
    | Virtual s | Local s | NotReal s -> s
  in
  let loc_to_string (l : Meta.loc) : string =
    string_of_int l.line ^ ":" ^ string_of_int l.col
  in
  "'" ^ file ^ "', lines "
  ^ loc_to_string span_data.beg_loc
  ^ "-"
  ^ loc_to_string span_data.end_loc

let raw_span_to_string (span : Meta.span) =
  let generated_from =
    match span.generated_from_span with
    | None -> ""
    | Some span ->
        "; this code is generated from a macro invocation at: "
        ^ span_data_to_string span
  in
  span_data_to_string span.data ^ generated_from

let span_to_string (span : Meta.span) = "Source: " ^ raw_span_to_string span

let format_error_message (span : Meta.span option) (msg : string) =
  let span =
    match span with
    | None -> ""
    | Some span -> "\n" ^ span_to_string span
  in
  msg ^ span

let format_error_message_with_file_line (file : string) (line : int)
    (span : Meta.span option) (msg : string) =
  format_error_message span msg
  ^ "\nCompiler source: " ^ file ^ ", line " ^ string_of_int line

type cfailure = {
  span : Meta.span option;
  file : string;
  line : int;
  msg : string;
}
[@@deriving show]

exception CFailure of cfailure

(** Recoverable failure *)
exception RFailure

type unique_error = string * int [@@deriving show, eq, ord]

module FileLineOrderedType :
  Collections.OrderedType with type t = unique_error = struct
  type t = unique_error

  let compare = compare_unique_error
  let to_string = show_unique_error
  let pp_t = pp_unique_error
  let show_t = show_unique_error
end

module FileLineSet = Collections.MakeSet (FileLineOrderedType)
module FileLineMap = Collections.MakeMap (FileLineOrderedType)

let error_list : (string * int * Meta.span option * string) list ref = ref []
let unique_errors = ref FileLineMap.empty

(** Save an error and print it at the same time.

    We prefer printing errors gradually rather than reporting everyting at the
    very end. *)
let push_error (file : string) (line : int) (span : Meta.span option)
    (msg : string) =
  Mutex.protect error_mutex (fun _ ->
      error_list := (file, line, span, msg) :: !error_list;
      unique_errors :=
        FileLineMap.update (file, line)
          (function
            | None -> Some 1
            | Some n -> Some (n + 1))
          !unique_errors);
  if !Config.print_error_emitters then
    log#serror (format_error_message_with_file_line file line span msg)
  else log#serror (format_error_message span msg)

(** Register an error, and throw an exception if [throw] is true *)
let save_error_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) =
  push_error file line span msg;
  if !Config.fail_hard then (
    let msg = format_error_message_with_file_line file line span msg in
    log#serror (msg ^ "\n");
    raise (Failure msg))

let save_error (file : string) (line : int) (span : Meta.span) (msg : string) =
  save_error_opt_span file line (Some span) msg

let add_loc (file : string) (line : int) (x : string -> int -> 'a) : 'a =
  x file line

let craise_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) =
  if !Config.fail_hard then (
    let msg = format_error_message_with_file_line file line span msg in
    log#serror (msg ^ "\n");
    raise (Failure msg))
  else
    let () = push_error file line span msg in
    raise (CFailure { span; file; line; msg })

let craise (file : string) (line : int) (span : Meta.span) (msg : string) =
  craise_opt_span file line (Some span) msg

(** Throw an exception, but do not register an error *)
let craise_opt_span_silent (file : string) (line : int)
    (span : Meta.span option) (msg : string) =
  if !Config.fail_hard then
    let msg = format_error_message_with_file_line file line span msg in
    raise (Failure msg)
  else raise (CFailure { span; file; line; msg })

let craise_silent (file : string) (line : int) (span : Meta.span) (msg : string)
    =
  craise_opt_span_silent file line (Some span) msg

(** Lazy assert *)
let classert_opt_span (file : string) (line : int) (span : Meta.span option)
    (b : bool) (msg : string Lazy.t) =
  if not b then craise_opt_span file line span (Lazy.force msg)

(** Lazy assert *)
let classert (file : string) (line : int) (span : Meta.span) (b : bool)
    (msg : string Lazy.t) =
  classert_opt_span file line (Some span) b msg

let cassert_opt_span (file : string) (line : int) (span : Meta.span option)
    (b : bool) (msg : string) =
  if not b then craise_opt_span file line span msg

let cassert (file : string) (line : int) (span : Meta.span) (b : bool)
    (msg : string) =
  cassert_opt_span file line (Some span) b msg

let craise_recover_opt_span (file : string) (line : int) (recover : bool)
    (span : Meta.span option) (msg : string) =
  if recover then raise RFailure else craise_opt_span file line span msg

let craise_recover (file : string) (line : int) (recover : bool)
    (span : Meta.span) (msg : string) =
  craise_recover_opt_span file line recover (Some span) msg

let cassert_recover_opt_span (file : string) (line : int) (recover : bool)
    (span : Meta.span option) (b : bool) (msg : string) =
  if not b then craise_recover_opt_span file line recover span msg

let cassert_recover (file : string) (line : int) (recover : bool)
    (span : Meta.span) (b : bool) (msg : string) =
  cassert_recover_opt_span file line recover (Some span) b msg

let sanity_check (file : string) (line : int) span b =
  cassert file line span b "Internal error, please file an issue"

let sanity_check_recover (file : string) (line : int) recover span b =
  cassert_recover file line recover span b
    "Internal error, please file an issue"

let sanity_check_opt_span (file : string) (line : int) span b =
  cassert_opt_span file line span b "Internal error, please file an issue"

let internal_error_opt_span (file : string) (line : int)
    (span : Meta.span option) =
  craise_opt_span file line span "Internal error, please file an issue"

let internal_error (file : string) (line : int) (span : Meta.span) =
  internal_error_opt_span file line (Some span)

let warn_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) =
  if !Config.warnings_as_errors then craise_opt_span file line span msg
  else
    let msg = format_error_message_with_file_line file line span msg in
    log#swarning (msg ^ "\n")

let warn (file : string) (line : int) (span : Meta.span) (msg : string) =
  warn_opt_span file line (Some span) msg

let cassert_warn_opt_span (file : string) (line : int) (span : Meta.span option)
    (b : bool) (msg : string) =
  if not b then warn_opt_span file line span msg

let cassert_warn (file : string) (line : int) (span : Meta.span) (b : bool)
    (msg : string) =
  if not b then warn_opt_span file line (Some span) msg

let unwrap_opt_span (file : string) (line : int) (span : Meta.span option)
    (x : 'a option) (msg : string) : 'a =
  match x with
  | Some x -> x
  | None -> craise_opt_span file line span msg

let unwrap_with_span (file : string) (line : int) (span : Meta.span)
    (x : 'a option) (msg : string) : 'a =
  unwrap_opt_span file line (Some span) x msg

let silent_unwrap_opt_span (file : string) (line : int)
    (span : Meta.span option) (x : 'a option) : 'a =
  match x with
  | Some x -> x
  | None ->
      craise_opt_span file line span "Internal error: please file an issue"

let try_unwrap (file : string) (line : int) (span : Meta.span) (x : 'a option) :
    'a =
  match x with
  | Some x -> x
  | None -> craise file line span "Internal error: please file an issue"

let silent_unwrap (file : string) (line : int) (span : Meta.span)
    (x : 'a option) : 'a =
  silent_unwrap_opt_span file line (Some span) x

let opt_raise_opt_span (file : string) (line : int) (span : Meta.span option)
    (msg : string) : unit =
  if !Config.fail_hard then (
    let msg = format_error_message_with_file_line file line span msg in
    log#serror (msg ^ "\n");
    raise (Failure msg))

let opt_raise (file : string) (line : int) (span : Meta.span) (msg : string) :
    unit =
  opt_raise_opt_span file line (Some span) msg

let option_get (file : string) (line : int) (span : Meta.span) (x : 'a option) :
    'a =
  match x with
  | None -> internal_error file line span
  | Some x -> x
