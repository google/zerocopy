(************************************************************************)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+     *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1+ / GPL3+     *)
(* Copyright 2024-2025 Emilio J. Gallego Arias -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                    -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & rocq-lsp contributors          *)
(************************************************************************)
(* Flèche => document manager: document                                 *)
(************************************************************************)

module SM = Lang.Compat.String.Map

(* Should be moved to the right place *)
module Util = struct
  let hd_opt l =
    match l with
    | [] -> None
    | h :: _ -> Some h

  let rec last l =
    match l with
    | [] -> None
    | [ x ] -> Some x
    | _ :: xs -> last xs

  let build_span start_loc end_loc =
    Coq.Loc_t.
      { start_loc with
        line_nb_last = end_loc.line_nb_last
      ; bol_pos_last = end_loc.bol_pos_last
      ; ep = end_loc.ep
      }

  let print_stats () =
    (if !Config.v.mem_stats then
       let size = Memo.all_size () in
       Io.Log.trace "stats" "%d" size);
    let stats = Stats.Global.dump () in
    Io.Log.trace "cache" "%s" (Stats.Global.to_string stats);
    Io.Log.trace "cache" "%s" (Memo.GlobalCacheStats.stats ());
    (* this requires patches to Coq *)
    (* Io.Log.error "coq parsing" (CoqParsingStats.dump ()); *)
    (* CoqParsingStats.reset (); *)
    Memo.GlobalCacheStats.reset ();
    Stats.reset ()

  let safe_sub s pos len =
    if pos < 0 || len < 0 || pos > String.length s - len then (
      let s = String.sub s 0 (Stdlib.min 20 String.(length s - 1)) in
      Io.Log.trace "string_sub" "error for pos: %d len: %d str: %s" pos len s;
      None)
    else Some (String.sub s pos len)
end

module DDebug = struct
  let parsed_sentence ~ast =
    let loc = Coq.Ast.loc ast |> Option.get in
    let line = loc.Coq.Loc_t.line_nb - 1 in
    Io.Log.trace "coq" "parsed sentence: [l: %d] | %a" line Coq.Pp_t.pp_with
      (Coq.Ast.print ast)

  let resume (last_tok : Lang.Range.t) version =
    Io.Log.trace "check" "resuming [v: %d], from: %d l: %d" version
      last_tok.end_.offset last_tok.end_.line
end

(* [node list] is a very crude form of a meta-data map "loc -> data" , where for
   now [data] is only the goals. *)
module Node = struct
  module Ast = struct
    type t =
      { v : Coq.Ast.t
      ; ast_info : Lang.Ast.Info.t list option
      }

    let to_coq { v; _ } = Coq.Ast.to_coq v
  end

  module Info = struct
    type t =
      { parsing_time : float
      ; stats : Memo.Stats.t option
      ; global_stats : Stats.Global.t  (** Info about cumulative stats *)
      }

    let make ~parsing_time ?stats ~global_stats () =
      { parsing_time; stats; global_stats }

    let pp_cache_hit fmt = function
      | None -> Format.fprintf fmt "N/A"
      | Some hit -> Format.fprintf fmt "%b" hit

    let pp_time fmt = function
      | None -> Format.fprintf fmt "N/A"
      | Some time -> Format.fprintf fmt "%.3f" time

    let pp_words fmt = function
      | None -> Format.fprintf fmt "N/A"
      | Some memory -> Stats.pp_words fmt memory

    let osplit = function
      | None -> (None, None, None)
      | Some (x, y, z) -> (Some x, Some y, Some z)

    let print { parsing_time; stats; global_stats } =
      let cptime = Stats.Global.get_f global_stats ~kind:Stats.Kind.Parsing in
      let cetime = Stats.Global.get_f global_stats ~kind:Stats.Kind.Exec in
      let cache_hit, time, memory =
        Option.map
          (fun (s : Memo.Stats.t) ->
            (s.cache_hit, s.stats.time, s.stats.memory))
          stats
        |> osplit
      in
      Format.asprintf
        "Cached: %a | P: %.3f / %.2f | E: %a / %.2f | Mem-Diff: %a" pp_cache_hit
        cache_hit parsing_time cptime.time pp_time time cetime.time pp_words
        memory
  end

  module Message = struct
    type t = Lang.Range.t Coq.Message.t

    let feedback_to_message ~lines message =
      let f = Coq.Utils.to_range ~lines in
      Coq.Message.map ~f message
  end

  type t =
    { range : Lang.Range.t
    ; prev : t option
    ; ast : Ast.t option  (** Ast of node *)
    ; state : Coq.State.t  (** (Full) State of node *)
    ; diags : Coq.Pp_t.t Lang.Diagnostic.t list
    ; messages : Message.t list
    ; info : Info.t
    }

  let range { range; _ } = range
  let ast { ast; _ } = ast
  let state { state; _ } = state
  let diags { diags; _ } = diags
  let messages { messages; _ } = messages
  let info { info; _ } = info
  (* let with_state f n = Option.map (fun x -> (x, n.state)) (f n) *)
end

(** Diagnostics helper module *)
module Diags : sig
  val err : Lang.Diagnostic.Severity.t

  (** Build simple diagnostic *)
  val make :
       ?data:Lang.Diagnostic.Data.t
    -> Lang.Range.t
    -> Lang.Diagnostic.Severity.t
    -> Coq.Pp_t.t
    -> Coq.Pp_t.t Lang.Diagnostic.t

  (** Build advanced diagnostic with AST analysis *)
  val error :
       err_range:Lang.Range.t
    -> quickFix:Lang.Range.t Lang.Qf.t list option
    -> msg:Coq.Pp_t.t
    -> stm_range:Lang.Range.t (* range for the sentence *)
    -> ?ast:Node.Ast.t
    -> unit
    -> Coq.Pp_t.t Lang.Diagnostic.t

  (** [of_messages drange msgs] process feedback messages, and convert some to
      diagnostics based on user-config. Default range [drange] is used for
      messages that have no range, usually this is set to the full node range. *)
  val of_messages :
       drange:Lang.Range.t
    -> Node.Message.t list
    -> Coq.Pp_t.t Lang.Diagnostic.t list * Node.Message.t list
end = struct
  let err = Lang.Diagnostic.Severity.error

  let make ?data range severity message =
    Lang.Diagnostic.{ range; severity; message; data }

  (* ast-dependent error diagnostic generation *)
  let extra_diagnostics_of_ast quickFix stm_range ast =
    let sentenceRange = Some stm_range in
    let failedRequire =
      match
        Option.bind ast (fun (ast : Node.Ast.t) ->
            Coq.Ast.Require.extract ast.v)
      with
      | Some _ ->
        Some []
        (* | Some { Coq.Ast.Require.from; mods; _ } -> *)
        (* let refs = List.map fst mods in *)
        (* Some [ { Lang.Diagnostic.FailedRequire.prefix = from; refs } ] *)
      | _ -> None
    in
    Some { Lang.Diagnostic.Data.sentenceRange; failedRequire; quickFix }

  (* XXX: This needs rework, as of today we gotta be careful. *)
  let extra_diagnostics_of_ast qf stm_range ast =
    if !Config.v.send_diags_extra_data then
      extra_diagnostics_of_ast qf stm_range ast
    else
      Option.map
        (fun qf ->
          let sentenceRange, failedRequire, quickFix = (None, None, Some qf) in
          { Lang.Diagnostic.Data.sentenceRange; failedRequire; quickFix })
        qf

  let error ~err_range ~quickFix ~msg ~stm_range ?ast () =
    let data = extra_diagnostics_of_ast quickFix stm_range ast in
    make ?data err_range Lang.Diagnostic.Severity.error msg

  let of_feed ~drange (severity, payload) =
    let { Coq.Message.Payload.range; quickFix; msg } = payload in
    let range = Stdlib.Option.value ~default:drange range in
    (* Be careful to avoid defining data if quickFix = None *)
    let data =
      Option.map
        (fun qf ->
          let sentenceRange, failedRequire, quickFix = (None, None, Some qf) in
          Lang.Diagnostic.Data.{ sentenceRange; failedRequire; quickFix })
        quickFix
    in
    make ?data range severity msg

  type partition_kind =
    | Left
    | Both
    | Right

  let partition ~f l =
    let rec part l r = function
      | [] -> (List.rev l, List.rev r)
      | x :: xs -> (
        match f x with
        | Left -> part (x :: l) r xs
        | Both -> part (x :: l) (x :: l) xs
        | Right -> part l (x :: r) xs)
    in
    part [] [] l

  let of_messages ~drange fbs =
    (* TODO, replace this by a cutoff level *)
    let cutoff =
      if !Config.v.show_coq_info_messages then 5
      else if !Config.v.show_notices_as_diagnostics then 4
      else 3
    in
    let f (lvl, _) =
      (* warning = 2 *)
      if lvl = Lang.Diagnostic.Severity.warning then Both
      else if lvl < cutoff then Left
      else Right
    in
    let diags, messages = partition ~f fbs in
    (List.map (of_feed ~drange) diags, messages)
end

module Completion = struct
  type t =
    | Yes of Lang.Range.t  (** Location of the last token in the document *)
    | Stopped of Lang.Range.t
        (** Location of the last valid token before stopping *)
    | WorkspaceUpdated of Lang.Range.t
        (** Location of the last valid token before the workspace update *)
    | Failed of Lang.Range.t  (** Critical failure, like an anomaly *)

  let range = function
    | Yes range | Stopped range | Failed range | WorkspaceUpdated range -> range

  let to_string = function
    | Yes _ -> "fully checked"
    | Stopped _ -> "stopped"
    | WorkspaceUpdated _ -> "workspace was updated"
    | Failed _ -> "failed"

  let is_completed = function
    | Yes _ | Failed _ -> true
    | _ -> false
end

(** Enviroment external to the document, this includes for now the [init] Coq
    state and the [workspace], which are used to build the first state of the
    document, usually by importing the prelude and other libs implicitly. *)
module Env = struct
  type t =
    { init : Coq.State.t
    ; workspace : Coq.Workspace.t
    ; files : Coq.Files.t
    }

  let make ~init ~workspace ~files = { init; workspace; files }

  let inject_requires ~extra_requires { init; workspace; files } =
    let workspace = Coq.Workspace.inject_requires ~extra_requires workspace in
    { init; workspace; files }
end

(** A Flèche document is basically a [node list], which is a crude form of a
    meta-data map [Range.t -> data], where for now [data] is the contents of
    [Node.t]. *)
type t =
  { uri : Lang.LUri.File.t  (** [uri] of the document *)
  ; languageId : string  (** [languageId] of the document *)
  ; version : int  (** [version] of the document *)
  ; contents : Contents.t  (** [contents] of the document *)
  ; nodes : Node.t list  (** List of document nodes *)
  ; comments : ((int * int) * string) list
        (** List of all comments found up to [completed] *)
  ; completed : Completion.t
        (** Status of the document, usually either completed, suspended, or
            waiting for some IO / external event *)
  ; toc : Node.t SM.t  (** table of contents *)
  ; env : Env.t  (** External document enviroment *)
  ; root : Coq.State.t
        (** [root] contains the first state document state, obtained by applying
            a workspace to Coq's initial state *)
  ; diags_dirty : bool
        (** internal field, used to optimize `eager_diagnostics` *)
  }

(* Flatten the list of document asts *)
let asts doc = List.filter_map Node.ast doc.nodes
let diags doc = List.concat_map Node.diags doc.nodes
let lines doc = doc.contents.lines

(* TOC handling *)
let rec add_toc_info node toc { Lang.Ast.Info.name; children; _ } =
  let toc =
    match name.v with
    | None -> toc
    | Some id -> SM.add id node toc
  in
  Stdlib.Option.fold
    ~some:(List.fold_left (add_toc_info node) toc)
    ~none:toc children

let update_toc_info toc ast_info node =
  List.fold_left (add_toc_info node) toc ast_info

let update_toc_node toc node =
  match Node.ast node with
  | None -> toc
  | Some { Node.Ast.ast_info = None; _ } -> toc
  | Some { Node.Ast.ast_info = Some ast_info; _ } ->
    update_toc_info toc ast_info node

let rebuild_toc nodes = List.fold_left update_toc_node SM.empty nodes

let init_fname ~uri =
  let file = Lang.LUri.File.to_string_file uri in
  Coq.Loc_t.InFile { dirpath = None; file }

let init_loc ~uri = Coq.Loc_t.initial (init_fname ~uri)

(* default range for the node that contains the init feedback errors *)
let drange ~lines =
  let open Lang in
  let llen = if Array.length lines > 0 then String.length lines.(0) else 1 in
  let start = Point.{ line = 0; character = 0; offset = 0 } in
  let end_ = Point.{ line = 0; character = llen; offset = llen } in
  Range.{ start; end_ }

let process_init_feedback ~lines ~stats ~global_stats state feedback =
  let messages = List.map (Node.Message.feedback_to_message ~lines) feedback in
  if not (Lang.Compat.List.is_empty messages) then
    let drange = drange ~lines in
    let diags, messages = Diags.of_messages ~drange messages in
    let parsing_time = 0.0 in
    let info = Node.Info.make ~parsing_time ?stats ~global_stats () in
    let range = drange in
    let prev = None in
    [ { Node.range; prev; ast = None; state; diags; messages; info } ]
  else []

(* Memoized call to [Coq.Init.doc_init] *)
let mk_doc ~token ~env ~uri =
  Memo.Init.evalS ~token (env.Env.init, env.workspace, env.files, uri)

(* Create empty doc, in state [~completed] *)
let empty_doc ~uri ~languageId ~contents ~version ~env ~root ~nodes ~completed =
  let lines = contents.Contents.lines in
  let init_loc = init_loc ~uri in
  let init_range = Coq.Utils.to_range ~lines init_loc in
  let comments = [] in
  let toc = SM.empty in
  let diags_dirty = not (Lang.Compat.List.is_empty nodes) in
  let completed = completed init_range in
  { uri
  ; languageId
  ; contents
  ; toc
  ; version
  ; env
  ; root
  ; nodes
  ; comments
  ; diags_dirty
  ; completed
  }

let error_doc ~range ~message ~uri ~languageId ~contents ~version ~env =
  let payload = Coq.Message.Payload.make ?range (Coq.Pp_t.str message) in
  let feedback = [ (Diags.err, payload) ] in
  let root = env.Env.init in
  let nodes = [] in
  let completed range = Completion.Failed range in
  ( empty_doc ~uri ~languageId ~version ~contents ~env ~root ~nodes ~completed
  , feedback )

let conv_error_doc ~raw ~uri ~languageId ~version ~env ~root err =
  let contents = Contents.make_raw ~raw in
  let lines = contents.lines in
  let err =
    let msg = Coq.Pp_t.(str "Error in document conversion: " ++ str err) in
    (Diags.err, Coq.Message.Payload.make msg)
  in
  (* No execution to add *)
  let stats = None in
  let global_stats = Stats.Global.dump () in
  let nodes = process_init_feedback ~lines ~stats ~global_stats root [ err ] in
  let completed range = Completion.Failed range in
  empty_doc ~uri ~languageId ~version ~env ~root ~nodes ~completed ~contents

let create ~token ~env ~uri ~languageId ~version ~contents =
  let () = Stats.reset () in
  let root, stats = mk_doc ~token ~env ~uri in
  ( Coq.Protect.E.map root ~f:(fun root ->
        let nodes = [] in
        let completed range = Completion.Stopped range in
        empty_doc ~uri ~languageId ~contents ~version ~env ~root ~nodes
          ~completed)
  , stats )

(** Try to create a doc, if Coq execution fails, create a failed doc with the
    corresponding errors; for now we refine the contents step as to better setup
    the initial document. *)
let handle_doc_creation_exec ~token ~env ~uri ~languageId ~version ~contents =
  let { Coq.Protect.E.r; feedback }, stats =
    create ~token ~env ~uri ~languageId ~version ~contents
  in
  let doc, extra_feedback =
    match r with
    | Interrupted ->
      let message = "Document Creation Interrupted!" in
      let range = None in
      error_doc ~range ~message ~uri ~languageId ~version ~contents ~env
    | Completed (Error (User { range; msg = err_msg; quickFix = _ }))
    | Completed (Error (Anomaly { range; msg = err_msg; quickFix = _ })) ->
      let message =
        Format.asprintf "Doc.create, internal error: @[%a@]" Coq.Pp_t.pp_with
          err_msg
      in
      error_doc ~range ~message ~uri ~languageId ~version ~contents ~env
    | Completed (Ok doc) -> (doc, [])
  in
  let state = doc.root in
  let stats = Some stats in
  let global_stats = Stats.Global.dump () in
  let nodes =
    let lines = contents.Contents.lines in
    process_init_feedback ~lines ~stats ~global_stats state
      (feedback @ extra_feedback)
    @ doc.nodes
  in
  let diags_dirty = not (Lang.Compat.List.is_empty nodes) in
  { doc with nodes; diags_dirty }

let handle_contents_creation ~env ~uri ~version ~languageId ~raw f =
  match Contents.make ~uri ~languageId ~raw with
  | Contents.R.Error err ->
    let root = env.Env.init in
    conv_error_doc ~raw ~uri ~languageId ~version ~env ~root err
  | Contents.R.Ok contents -> f ~env ~uri ~languageId ~version ~contents

let create ~token ~env ~uri ~languageId ~version ~raw =
  handle_contents_creation ~env ~uri ~version ~languageId ~raw
    (handle_doc_creation_exec ~token)

let create ~token ~env ~uri ~languageId ~version ~raw =
  NewProfile.profile "Doc.create"
    (fun () -> create ~token ~env ~uri ~languageId ~version ~raw)
    ()

(* Used in bump, we should consolidate with create *)
let recreate ~token ~doc ~version ~contents =
  let env, uri, languageId = (doc.env, doc.uri, doc.languageId) in
  handle_doc_creation_exec ~token ~env ~uri ~languageId ~version ~contents

let recover_up_to_offset ~init_range doc offset =
  Io.Log.trace "prefix" "common prefix offset found at %d" offset;
  let rec find acc_nodes acc_range nodes =
    match nodes with
    | [] -> (List.rev acc_nodes, acc_range)
    | n :: ns ->
      if Debug.scan then
        Io.Log.trace "scan" "consider node at %a" Lang.Range.pp n.Node.range;
      if n.range.end_.offset >= offset then (List.rev acc_nodes, acc_range)
      else find (n :: acc_nodes) n.range ns
  in
  find [] init_range doc.nodes

(* Simple commment filter, we drop the comments before the start of the last
   valid token *)
let filter_comments comments (range : Lang.Range.t) =
  let cutoff = range.start.offset in
  (* We could optimize this, also verify what the math is here *)
  List.filter (fun ((_, e), _) -> e <= cutoff) comments

let compute_common_prefix ~init_range ~contents (prev : t) =
  let s1 = prev.contents.raw in
  let l1 = prev.contents.last.offset in
  let s2 = contents.Contents.raw in
  let l2 = contents.last.offset in
  let rec match_or_stop i =
    if i = l1 || i = l2 then i
    else if Char.equal s1.[i] s2.[i] then match_or_stop (i + 1)
    else i
  in
  let common_idx = match_or_stop 0 in
  let nodes, range = recover_up_to_offset ~init_range prev common_idx in
  let comments = filter_comments prev.comments range in
  let toc = rebuild_toc nodes in
  Io.Log.trace "prefix" "resuming from %a" Lang.Range.pp range;
  let completed = Completion.Stopped range in
  (nodes, comments, completed, toc)

let bump_version ~init_range ~version ~contents doc =
  (* When a new document, we resume checking from a common prefix *)
  let nodes, comments, completed, toc =
    compute_common_prefix ~init_range ~contents doc
  in
  (* Important: uri, root remain the same *)
  let uri = doc.uri in
  let languageId = doc.languageId in
  let root = doc.root in
  let env = doc.env in
  { uri
  ; languageId
  ; version
  ; root
  ; nodes
  ; comments
  ; contents
  ; toc
  ; diags_dirty = true (* EJGA: Is it worth to optimize this? *)
  ; completed
  ; env
  }

let bump_version ~token ~version ~(contents : Contents.t) doc =
  let init_loc = init_loc ~uri:doc.uri in
  let init_range = Coq.Utils.to_range ~lines:contents.lines init_loc in
  match doc.completed with
  (* We can do better, but we need to handle the case where the anomaly is when
     restoring / executing the first sentence *)
  | WorkspaceUpdated _ | Failed _ ->
    (* re-create the document on failed, as the env may have changed *)
    recreate ~token ~doc ~version ~contents
  | Stopped _ | Yes _ -> bump_version ~init_range ~version ~contents doc

let bump_version ~token ~version ~raw doc =
  let uri, languageId = (doc.uri, doc.languageId) in
  match Contents.make ~uri ~languageId ~raw with
  | Contents.R.Error e ->
    conv_error_doc ~raw ~uri ~languageId ~version ~env:doc.env ~root:doc.root e
  | Contents.R.Ok contents -> bump_version ~token ~version ~contents doc

let bump_version ~token ~version ~raw doc =
  NewProfile.profile "Doc.bump_version"
    (fun () -> bump_version ~token ~version ~raw doc)
    ()

let update_env ~doc ~env =
  let range = Completion.range doc.completed in
  { doc with completed = WorkspaceUpdated range; env }

let add_node ~node doc =
  let diags_dirty = if node.Node.diags <> [] then true else doc.diags_dirty in
  let toc = update_toc_node doc.toc node in
  { doc with nodes = node :: doc.nodes; toc; diags_dirty }

let send_eager_diagnostics ~io ~uri ~version ~doc =
  (* this is too noisy *)
  (* let proc_diag = mk_diag loc 3 (Pp.str "Processing") in *)
  (* Io.Report.diagnostics ~uri ~version (proc_diag :: doc.diags)); *)
  if doc.diags_dirty && !Config.v.eager_diagnostics then (
    let diags = diags doc in
    Io.Report.diagnostics ~io ~uri ~version diags;
    { doc with diags_dirty = false })
  else doc

let set_completion ~completed pa doc =
  let new_comments = List.rev (Coq.Parsing.Parsable.comments pa) in
  let loc = Coq.Parsing.Parsable.loc pa in
  Io.Log.trace "set_completion" "setting new comments %d"
    (List.length new_comments);
  Io.Log.trace "set_completion" "parsable at position %a" Coq.Pp_t.pp_with
    (Coq.Loc_t.pp loc);
  let comments = List.append doc.comments new_comments in
  { doc with comments; completed }

(* We approximate the remnants of the document. It would be easier if instead of
   reporting what is missing, we would report what is done, but for now we are
   trying this paradigm.

   As we are quite dynamic (for now) in terms of what we observe of the document
   (basically we observe it linearly), we must compute the final position with a
   bit of a hack. *)
let compute_progress end_ (last_done : Lang.Range.t) =
  let start = last_done.end_ in
  let range = Lang.Range.{ start; end_ } in
  { Progress.Info.range; kind = 1 }

let report_progress ~io ~doc (last_tok : Lang.Range.t) =
  let progress = compute_progress doc.contents.last last_tok in
  Io.Report.fileProgress ~io ~uri:doc.uri ~version:doc.version [ progress ]

let send_execinfo ~io ~uri ~version ~range =
  if !Config.v.send_execinfo then Io.Report.execInfo ~io ~uri ~version ~range

(* XXX: Save on close? *)
(* let close_doc _modname = () *)

let parse_stm ~token ~st ps =
  let f ps = Coq.Parsing.parse ~token ~st ps in
  Stats.record ~kind:Stats.Kind.Parsing ~f ps

module Recovery_context = struct
  type t =
    { contents : Contents.t
          (** Contents of the document (for syntax-based recovery) *)
    ; last_tok : Lang.Range.t  (** Position of the last token parsed *)
    ; nodes : Node.t list
          (** All nodes of the document (to be replaced by the structural
              solution *)
    ; ast : Coq.Ast.t option
          (** Ast of the sentence that failed, if available *)
    }

  let make ~contents ~last_tok ~nodes ?ast () =
    { contents; last_tok; nodes; ast }
end

module Analysis : sig
  (** [find_proof_start node] returns [Some pnode] where [pnode] is the node
      that contains the start of the proof. [node] is the node to start the
      search from, which will proceed using the [prev] field. *)
  val find_proof_start : Node.t -> Node.t option
  (* This is useful in meta-commands, and other plugins actually! *)

  (** Version of [find_proof_start] that takes a list of nodes (for
      convenience), and will start the search from the first node in the list. *)
  val find_proof_start_nodes : Node.t list -> Node.t option
end = struct
  (* Returns node before / after, will be replaced by the right structure, we
     can also do dynamic by looking at proof state *)
  let rec find_proof_start (node : Node.t option) =
    match node with
    | None -> None
    | Some ({ Node.ast = None; _ } as node) -> find_proof_start node.prev
    | Some ({ ast = Some ast; _ } as node) -> (
      match (Node.Ast.to_coq ast).CAst.v.Vernacexpr.expr with
      | Vernacexpr.VernacSynPure (VernacStartTheoremProof _)
      | VernacSynPure (VernacDefinition (_, _, ProveBody _)) -> Some node
      | _ -> find_proof_start node.prev)

  let find_proof_start node = find_proof_start (Some node)

  let find_proof_start_nodes nodes =
    match nodes with
    | [] -> None
    | n :: _ -> find_proof_start n
end

(* This is not in its own module because we don't want to move the definition of
   [Node.t] out (yet) *)
module Recovery : sig
  val handle :
       token:Coq.Limits.Token.t
    -> context:Recovery_context.t
    -> st:Coq.State.t
    -> Coq.State.t
end = struct
  let recovery_for_failed_qed ~token ~default nodes =
    match Analysis.find_proof_start_nodes nodes with
    | None -> Coq.Protect.E.ok (default, None)
    | Some { range; state; prev; _ } -> (
      if !Config.v.admit_on_bad_qed then
        Memo.Admit.eval ~token state
        |> Coq.Protect.E.map ~f:(fun state -> (state, Some range))
      else
        match prev with
        | None -> Coq.Protect.E.ok (default, None)
        | Some { state; range; _ } -> Coq.Protect.E.ok (state, Some range))

  let log_qed_recovery v =
    Coq.Protect.E.map ~f:(fun (st, range) ->
        let loc_msg =
          Stdlib.Option.fold ~some:Lang.Range.to_string ~none:"no loc" range
        in
        Io.Log.trace "recovery" "success %s %s" loc_msg
          (Memo.Interp.input_info (st, v));
        st)

  (* Contents-based recovery heuristic, special 'Qed.' case when `Qed.` is part
     of the error *)

  (* This function extracts the last [size] chars from the error, omitting the
     point *)
  let extract_token Lang.Range.{ end_; _ } { Contents.lines; _ } size =
    let Lang.Point.{ line; character; _ } = end_ in
    let line = Array.get lines line in
    if character > size && String.length line > size then
      let coff = character - (size + 1) in
      Some (String.init size (fun idx -> line.[idx + coff]))
    else None

  let lex_recovery_heuristic ~token last_tok contents nodes st =
    let et = extract_token last_tok contents in
    match (et 3, et 7, et 8) with
    | Some ("Qed" as txt), _, _
    | _, Some ("Defined" as txt), _
    | _, _, Some ("Admitted" as txt) ->
      Io.Log.trace "lex recovery" "%s detected" txt;
      recovery_for_failed_qed ~token ~default:st nodes
      |> Coq.Protect.E.map ~f:fst
    | _, _, _ -> Coq.Protect.E.ok st

  (* AST-based heuristics: Qed, bullets, ... *)
  let ast_recovery_heuristic ~token last_tok contents nodes st v =
    match (Coq.Ast.to_coq v).CAst.v.Vernacexpr.expr with
    (* Drop the top proof state if we reach a faulty Qed. *)
    | Vernacexpr.VernacSynPure (VernacEndProof _) ->
      Io.Log.trace "recovery" "qed";
      recovery_for_failed_qed ~token ~default:st nodes |> log_qed_recovery v
    (* If a new focus (or unfocusing) fails, admit the proof and try again *)
    | Vernacexpr.VernacSynPure (VernacBullet _ | Vernacexpr.VernacEndSubproof)
      ->
      Io.Log.trace "recovery" "bullet";
      Coq.State.admit_goal ~token ~st
      |> Coq.Protect.E.bind ~f:(fun st ->
             (* We skip the cache here, but likely we don't want to do that. *)
             let intern = Vernacinterp.fs_intern in
             Coq.Interp.interp ~token ~intern ~st v)
    | _ ->
      (* Fallback to qed special lex case *)
      lex_recovery_heuristic ~token last_tok contents nodes st

  (* XXX: This should be refined. *)
  let handle ~token ~context ~st =
    let { Recovery_context.contents; last_tok; nodes; ast } = context in
    let { Coq.Protect.E.r; feedback } =
      match ast with
      | None -> lex_recovery_heuristic ~token last_tok contents nodes st
      | Some ast -> ast_recovery_heuristic ~token last_tok contents nodes st ast
    in
    Io.Log.feedback "Recovery_context.handle" feedback;
    match r with
    | Interrupted -> st
    | Completed (Ok st) -> st
    | Completed (Error _) -> st
end
(* end [module Recovery = struct...] *)

let interp_and_info ~token ~st ~files ast =
  match Coq.Ast.Require.extract ast with
  | None -> Memo.Interp.evalS ~token (st, ast)
  | Some ast -> Memo.Require.evalS ~token (st, files, ast)

(* Support for meta-commands, a bit messy, but cool in itself *)
let search_node ~command ~doc ~st =
  let nstats (node : Node.t option) =
    let some (node : Node.t) =
      Stdlib.Option.value ~default:Memo.Stats.zero node.info.stats
    in
    Stdlib.Option.fold ~some ~none:Memo.Stats.zero node
  in
  let back_overflow num =
    let ll = List.length doc.nodes in
    Coq.Pp_t.(
      str "not enough nodes: [" ++ int num ++ str " > " ++ int ll
      ++ str "] available document nodes")
  in
  match command with
  | Coq.Ast.Meta.Command.Back num -> (
    match List.nth_opt doc.nodes num with
    | None ->
      let message = back_overflow num in
      (Coq.Protect.E.error message, nstats None)
    | Some node -> (Coq.Protect.E.ok node.state, nstats (Some node)))
  | Restart -> (
    match Analysis.find_proof_start_nodes doc.nodes with
    | None ->
      (Coq.Protect.E.error Coq.Pp_t.(str "no proof to restart"), Memo.Stats.zero)
    | Some node -> (Coq.Protect.E.ok node.state, nstats None))
  | ResetName id -> (
    let toc = doc.toc in
    let id = Names.Id.to_string id.v in
    match SM.find_opt id toc with
    | None ->
      ( Coq.Protect.E.error
          Coq.Pp_t.(str "identifier " ++ str id ++ str " not found")
      , Memo.Stats.zero )
    | Some node ->
      let node = Stdlib.Option.value ~default:node node.prev in
      (Coq.Protect.E.ok node.state, nstats (Some node)))
  | ResetInitial -> (Coq.Protect.E.ok doc.root, nstats None)
  | AbortAll ->
    let st = Coq.State.drop_all_proofs ~st in
    (Coq.Protect.E.ok st, nstats None)

let interp_and_info ~token ~st ~files ~doc ast =
  match Coq.Ast.Meta.extract ast with
  | None -> interp_and_info ~token ~st ~files ast
  | Some { command; loc = _; attrs = _; control = _ } ->
    (* That's an interesting point, for now we don't measure time Flèche is
       spending on error recovery and meta stuff, we should record that time
       actually at some point too. In this case, maybe we could recover the
       cache hit from the original node? *)
    search_node ~command ~doc ~st

let interp_and_info ~token ~parsing_time ~st ~files ~doc ast =
  let res, stats = interp_and_info ~token ~st ~files ~doc ast in
  let global_stats = Stats.Global.dump () in
  let info = Node.Info.make ~parsing_time ~stats ~global_stats () in
  (res, info)

type parse_action =
  | EOF of Completion.t (* completed *)
  | Skip of
      Lang.Range.t
      * Lang.Range.t (* span of the skipped sentence + last valid token *)
  | Process of Coq.Ast.t (* success! *)

(* Returns parse_action, diags, parsing_time *)
let parse_action ~token ~lines ~st last_tok doc_handle =
  let start_loc = Coq.Parsing.(Parsable.loc doc_handle |> Lexer.after) in
  let parse_res, stats = parse_stm ~token ~st doc_handle in
  let f = Coq.Utils.to_range ~lines in
  let { Coq.Protect.E.r; feedback } = Coq.Protect.E.map_loc ~f parse_res in
  let { Stats.time; memory = _ } = stats in
  match r with
  | Coq.Protect.R.Interrupted -> (EOF (Stopped last_tok), [], feedback, time)
  | Coq.Protect.R.Completed res -> (
    match res with
    | Ok None ->
      (* We actually need to fix Coq to return the location of the true file
         EOF, the below trick seems to work tho. Coq fix involves updating the
         type of `Pcoq.main_entry` *)
      let last_tok = Coq.Parsing.Parsable.loc doc_handle in
      let last_tok = Coq.Utils.to_range ~lines last_tok in
      (EOF (Yes last_tok), [], feedback, time)
    | Ok (Some ast) ->
      let () = if Debug.parsing then DDebug.parsed_sentence ~ast in
      (Process ast, [], feedback, time)
    | Error (Anomaly { range = _; quickFix; msg })
    | Error (User { range = None; quickFix; msg }) ->
      (* We don't have a better alternative :(, usually missing error loc here
         means an anomaly, so we stop *)
      let err_range = last_tok in
      let parse_diags =
        [ Diags.error ~err_range ~quickFix ~msg ~stm_range:err_range () ]
      in
      (EOF (Failed last_tok), parse_diags, feedback, time)
    | Error (User { range = Some err_range; quickFix; msg }) ->
      Coq.Parsing.discard_to_dot doc_handle;
      let last_tok = Coq.Parsing.Parsable.loc doc_handle in
      let last_tok_range = Coq.Utils.to_range ~lines last_tok in
      let span_loc = Util.build_span start_loc last_tok in
      let span_range = Coq.Utils.to_range ~lines span_loc in
      let parse_diags =
        [ Diags.error ~err_range ~quickFix ~msg ~stm_range:span_range () ]
      in
      (Skip (span_range, last_tok_range), parse_diags, feedback, time))

let parse_action ~token ~lines ~st last_tok doc_handle =
  NewProfile.profile "Doc.parse_action"
    (fun () -> parse_action ~token ~lines ~st last_tok doc_handle)
    ()

(* Result of node-building action *)
type document_action =
  | Stop of Completion.t * Node.t
  | Continue of
      { state : Coq.State.t
      ; last_tok : Lang.Range.t
      ; node : Node.t
      }
  | Interrupted of Lang.Range.t

let unparseable_node ~range ~prev ~parsing_diags ~parsing_feedback ~state
    ~parsing_time =
  let fb_diags, messages = Diags.of_messages ~drange:range parsing_feedback in
  let diags = fb_diags @ parsing_diags in
  let stats = None in
  let global_stats = Stats.Global.dump () in
  let info = Node.Info.make ~parsing_time ?stats ~global_stats () in
  { Node.range; prev; ast = None; diags; messages; state; info }

let assemble_diags ~range ~parsing_diags ~parsing_feedback ~diags ~feedback =
  let parsing_fb_diags, parsing_messages =
    Diags.of_messages ~drange:range parsing_feedback
  in
  let fb_diags, fb_messages = Diags.of_messages ~drange:range feedback in
  let diags = parsing_diags @ parsing_fb_diags @ fb_diags @ diags in
  let messages = parsing_messages @ fb_messages in
  (diags, messages)

let parsed_node ~range ~prev ~ast ~state ~parsing_diags ~parsing_feedback ~diags
    ~feedback ~info =
  let diags, messages =
    assemble_diags ~range ~parsing_diags ~parsing_feedback ~diags ~feedback
  in
  { Node.range; prev; ast = Some ast; diags; messages; state; info }

let strategy_of_coq_err ~node ~state ~last_tok = function
  | Coq.Protect.Error.Anomaly _ -> Stop (Failed last_tok, node)
  | User _ -> Continue { state; last_tok; node }

let node_of_coq_result ~token ~doc ~range ~prev ~ast ~st ~parsing_diags
    ~parsing_feedback ~feedback ~info last_tok res =
  match res with
  | Ok state ->
    let node =
      parsed_node ~range ~prev ~ast ~state ~parsing_diags ~parsing_feedback
        ~diags:[] ~feedback ~info
    in
    Continue { state; last_tok; node }
  | Error
      (Coq.Protect.Error.Anomaly { range = err_range; quickFix; msg } as coq_err)
  | Error (User { range = err_range; quickFix; msg } as coq_err) ->
    let err_range = Stdlib.Option.value ~default:range err_range in
    let err_diags =
      [ Diags.error ~err_range ~quickFix ~msg ~stm_range:range ~ast () ]
    in
    let contents, nodes = (doc.contents, doc.nodes) in
    let context =
      Recovery_context.make ~contents ~last_tok ~nodes ~ast:ast.v ()
    in
    let recovery_st = Recovery.handle ~token ~context ~st in
    let node =
      parsed_node ~range ~prev ~ast ~state:recovery_st ~parsing_diags
        ~parsing_feedback ~diags:err_diags ~feedback ~info
    in
    strategy_of_coq_err ~node ~state:recovery_st ~last_tok coq_err

(* Build a document node, possibly executing *)
let document_action ~token ~io ~st ~parsing_diags ~parsing_feedback
    ~parsing_time ~prev ~doc last_tok doc_handle action =
  match action with
  (* End of file *)
  | EOF completed ->
    let range = Completion.range completed in
    let node =
      unparseable_node ~range ~prev ~parsing_diags ~parsing_feedback ~state:st
        ~parsing_time
    in
    Stop (completed, node)
  (* Parsing error *)
  | Skip (span_range, last_tok) ->
    let context =
      Recovery_context.make ~contents:doc.contents ~last_tok ~nodes:doc.nodes ()
    in
    let st = Recovery.handle ~token ~context ~st in
    let node =
      unparseable_node ~range:span_range ~prev ~parsing_diags ~parsing_feedback
        ~state:st ~parsing_time
    in
    Continue { state = st; last_tok; node }
  (* We can interpret the command now *)
  | Process ast -> (
    (* Prepare the Ast range and send execinfo *)
    let lines, files = (doc.contents.lines, doc.env.files) in
    let ast_loc = Coq.Ast.loc ast |> Option.get in
    let ast_range = Coq.Utils.to_range ~lines ast_loc in
    send_execinfo ~io ~uri:doc.uri ~version:doc.version ~range:ast_range;
    (* Execute the command *)
    let process_res, info =
      interp_and_info ~token ~parsing_time ~st ~files ~doc ast
    in
    let f = Coq.Utils.to_range ~lines in
    let { Coq.Protect.E.r; feedback } = Coq.Protect.E.map_loc ~f process_res in
    match r with
    | Coq.Protect.R.Interrupted ->
      (* Exit *)
      Interrupted last_tok
    | Coq.Protect.R.Completed res ->
      let ast =
        Node.Ast.{ v = ast; ast_info = Coq.Ast.make_info ~lines ~st ast }
      in
      (* The evaluation by Coq fully completed, then we can resume checking from
         this point then, hence the new last valid token last_tok_new *)
      let last_tok_new = Coq.Parsing.Parsable.loc doc_handle in
      let last_tok_new = Coq.Utils.to_range ~lines last_tok_new in
      node_of_coq_result ~token ~doc ~range:ast_range ~prev ~ast ~st
        ~parsing_diags ~parsing_feedback ~feedback ~info last_tok_new res)

let document_action ~token ~io ~st ~parsing_diags ~parsing_feedback
    ~parsing_time ~prev ~doc last_tok doc_handle action =
  NewProfile.profile "Doc.document_action"
    (fun () ->
      document_action ~token ~io ~st ~parsing_diags ~parsing_feedback
        ~parsing_time ~prev ~doc last_tok doc_handle action)
    ()

module Target = struct
  type t =
    | End
    | Position of int * int

  let pp fmt = function
    | End -> Format.fprintf fmt "{target: end}"
    | Position (l, c) -> Format.fprintf fmt "{target: l: %02d | c: %02d}" l c

  let reached ~(range : Lang.Range.t) (line, col) =
    let reached_line = range.end_.line in
    let reached_col = range.end_.character in
    line < reached_line || (line = reached_line && col <= reached_col)
end

let beyond_target (range : Lang.Range.t) target =
  match target with
  | Target.End -> false
  | Position (cut_line, cut_col) -> Target.reached ~range (cut_line, cut_col)

let log_beyond_target last_tok target =
  Io.Log.trace "beyond_target" "target reached %a" Lang.Range.pp last_tok;
  Io.Log.trace "beyond_target" "target is %a" Target.pp target

let max_errors_node ~state ~range ~prev =
  let msg = Coq.Pp_t.str "Maximum number of errors reached" in
  let parsing_diags = [ Diags.make range Diags.err msg ] in
  unparseable_node ~range ~prev ~parsing_diags ~parsing_feedback:[] ~state
    ~parsing_time:0.0

module Stop_cond = struct
  type t =
    | Target
    | Max_errors
    | Continue

  let should_stop acc_errors last_tok target =
    if acc_errors > !Config.v.max_errors then Max_errors
    else if beyond_target last_tok target then Target
    else Continue
end

(* main interpretation loop *)
let process_and_parse ~io ~token ~target ~uri ~version doc last_tok doc_handle =
  let rec stm doc st (last_tok : Lang.Range.t) prev acc_errors =
    (* Reporting of progress and diagnostics (if dirty) *)
    let doc = send_eager_diagnostics ~io ~uri ~version ~doc in
    report_progress ~io ~doc last_tok;
    match Stop_cond.should_stop acc_errors last_tok target with
    | Max_errors ->
      let completed = Completion.Failed last_tok in
      let node = max_errors_node ~state:st ~range:last_tok ~prev in
      let doc = add_node ~node doc in
      set_completion ~completed doc_handle doc
    | Target ->
      let () = log_beyond_target last_tok target in
      (* We set to Completed.Yes when we have reached the EOI *)
      let completed =
        if last_tok.end_.offset >= doc.contents.last.offset then
          Completion.Yes last_tok
        else Completion.Stopped last_tok
      in
      set_completion ~completed doc_handle doc
    | Continue -> (
      (* Parsing *)
      if Debug.parsing then Io.Log.trace "coq" "parsing sentence";
      let lines = doc.contents.lines in
      let action, parsing_diags, parsing_feedback, parsing_time =
        parse_action ~token ~lines ~st last_tok doc_handle
      in
      (* Execution *)
      let action =
        document_action ~token ~io ~st ~parsing_diags ~parsing_feedback
          ~parsing_time ~prev ~doc last_tok doc_handle action
      in
      match action with
      | Interrupted last_tok ->
        set_completion ~completed:(Stopped last_tok) doc_handle doc
      | Stop (completed, node) ->
        let doc = add_node ~node doc in
        (* See #445 *)
        report_progress ~io ~doc (Completion.range completed);
        set_completion ~completed doc_handle doc
      | Continue { state; last_tok; node } ->
        let n_errors =
          Lang.Compat.List.count Lang.Diagnostic.is_error node.Node.diags
        in
        let doc = add_node ~node doc in
        stm doc state last_tok (Some node) (acc_errors + n_errors))
  in
  (* Set the document to "internal" mode, stm expects the node list to be in
     reversed order *)
  let doc = { doc with nodes = List.rev doc.nodes } in
  (* Note that nodes and diags are in reversed order here *)
  let last_node, st, stats =
    match Util.hd_opt doc.nodes with
    | None -> (None, doc.root, Stats.Global.zero ())
    | Some { Node.state; range; info = { global_stats; _ }; _ } as last_node ->
      Io.Log.trace "resume / process_and_parse" "last node: %a" Lang.Range.pp
        range;
      (last_node, state, global_stats)
  in
  Stats.Global.restore stats;
  let doc = stm doc st last_tok last_node 0 in
  (* Set the document to "finished" mode: reverse the node list *)
  let doc = { doc with nodes = List.rev doc.nodes } in
  doc

let process_and_parse ~io ~token ~target ~uri ~version doc last_tok doc_handle =
  NewProfile.profile "Doc.process_and_parse"
    (fun () ->
      process_and_parse ~io ~token ~target ~uri ~version doc last_tok doc_handle)
    ()

let log_doc_completion (completed : Completion.t) =
  let timestamp = Unix.gettimeofday () in
  let range = Completion.range completed in
  let status = Completion.to_string completed in
  Io.Log.trace "check" "done [%.2f]: document %s with pos %a" timestamp status
    Lang.Range.pp range

(* Rebuild a Coq loc from a range, this used to be done using [CLexer.after] but
   due to Fleche now being 100% based on unicode locations we implement our
   own *)
let debug_loc_after line (r : Lang.Range.t) =
  if Debug.unicode then
    Io.Log.trace "loc_after" "str: '%s' | char: %d" line r.end_.character

let loc_after ~lines ~uri (r : Lang.Range.t) =
  let line_nb_last = r.end_.line + 1 in
  let end_index =
    let line = Array.get lines r.end_.line in
    debug_loc_after line r;
    Lang.Utf.utf8_offset_of_utf16_offset ~line ~offset:r.end_.character
  in
  let bol_pos_last = r.end_.offset - end_index in
  { Coq.Loc_t.fname = init_fname ~uri
  ; line_nb = line_nb_last
  ; bol_pos = bol_pos_last
  ; line_nb_last
  ; bol_pos_last
  ; bp = r.end_.offset
  ; ep = r.end_.offset
  }

(** Setup parser and call the main routine *)
let resume_check ~io ~token ~(last_tok : Lang.Range.t) ~doc ~target =
  let uri, version, contents = (doc.uri, doc.version, doc.contents) in
  (* Compute resume point, basically [CLexer.after] + stream setup *)
  let lines = doc.contents.lines in
  let resume_loc = loc_after ~lines ~uri last_tok in
  let offset = resume_loc.Coq.Loc_t.bp in
  let pcontent_len = contents.last.offset in
  match Util.safe_sub contents.text offset (pcontent_len - offset) with
  | None ->
    (* Guard against internal tricky eof errors *)
    let completed = Completion.Failed last_tok in
    let fake_pa = Coq.Parsing.(Parsable.make (Stream.of_string "")) in
    set_completion ~completed fake_pa doc
  | Some processed_content ->
    let handle =
      Coq.Parsing.(
        Parsable.make ~loc:resume_loc
          Stream.(of_string ~offset processed_content))
    in
    process_and_parse ~io ~token ~target ~uri ~version doc last_tok handle

(** Check a document, if it was not completed already *)
let check ~io ~token ~target ~doc () =
  match doc.completed with
  | Yes _ ->
    Io.Log.trace "check" "resuming, completed=yes, nothing to do";
    doc
  | Failed _ ->
    Io.Log.trace "check" "can't resume, failed=yes, nothing to do";
    doc
  | WorkspaceUpdated _ ->
    Io.Log.trace "check" "recreating document due to full workspace update";
    let version, contents = (doc.version, doc.contents) in
    recreate ~token ~doc ~version ~contents
  | Stopped last_tok ->
    DDebug.resume last_tok doc.version;
    let doc = resume_check ~io ~token ~last_tok ~doc ~target in
    log_doc_completion doc.completed;
    Util.print_stats ();
    doc

let check ~io ~token ~target ~doc () =
  NewProfile.profile "Doc.check" (fun () -> check ~io ~token ~target ~doc ()) ()

let save ~token ~doc =
  match doc.completed with
  | Yes _ ->
    let st =
      Util.last doc.nodes |> Stdlib.Option.fold ~some:Node.state ~none:doc.root
    in
    let uri = doc.uri in
    let ldir = Coq.Workspace.dirpath_of_uri ~uri in
    let in_file = Lang.LUri.File.to_string_file uri in
    Coq.State.in_stateM ~token ~st
      ~f:(fun () -> Coq.Save.save_vo ~token ~st ~ldir ~in_file)
      ()
  | _ ->
    let error = Coq.Pp_t.(str "Can't save document that failed to check") in
    Coq.Protect.E.error error

let doc_to_disk ~doc ~in_file : unit =
  let out_vof = Filename.(remove_extension in_file) ^ ".vof" in
  Coq.Compat.Ocaml_414.Out_channel.with_open_bin out_vof (fun oc ->
      Marshal.to_channel oc doc [])

let doc_of_disk ~in_file : t =
  let out_vof = Filename.(remove_extension in_file) ^ ".vof" in
  Coq.Compat.Ocaml_414.In_channel.with_open_bin out_vof (fun ic ->
      Marshal.from_channel ic)

let save_vof ~token ~doc =
  match doc.completed with
  | Yes _ ->
    let st =
      Util.last doc.nodes |> Stdlib.Option.fold ~some:Node.state ~none:doc.root
    in
    let uri = doc.uri in
    let in_file = Lang.LUri.File.to_string_file uri in
    Coq.State.in_state ~token ~st ~f:(fun () -> doc_to_disk ~doc ~in_file) ()
  | _ ->
    let error = Coq.Pp_t.(str "Can't save document that failed to check") in
    Coq.Protect.E.error error

(* run api, experimental *)

(* Adaptor, should be supported in memo directly *)
let eval_no_memo ~token (st, cmd) =
  Coq.Interp.interp ~token ~intern:Vernacinterp.fs_intern ~st cmd

(* TODO, what to do with feedback, what to do with errors *)
let rec parse_execute_loop ~token ~memo pa st =
  let open Coq.Protect.E.O in
  let eval = if memo then Memo.Interp.eval else eval_no_memo in
  let* ast = Coq.Parsing.parse ~token ~st pa in
  match ast with
  | Some ast ->
    let* st = eval ~token (st, ast) in
    parse_execute_loop ~token ~memo pa st
  (* On EOF we return the previous state, the command was the empty string or a
     comment *)
  | None -> Coq.Protect.E.ok st

let parse_and_execute_in ~token ~loc tac st =
  let str = Coq.Parsing.Stream.of_string tac in
  let pa = Coq.Parsing.Parsable.make ?loc str in
  parse_execute_loop ~token pa st

let run ~token ?loc ?(memo = true) ~st cmds =
  Coq.State.in_stateM ~token ~st
    ~f:(parse_and_execute_in ~token ~loc ~memo cmds)
    st
