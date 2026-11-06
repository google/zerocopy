(** Emit translation.json which contains the Aeneas data which connects the Lean
    translation to the Rust code. *)

(** Rust source location of a declaration, taken from LLBC [item_meta.span]. *)
type source = {
  file : string;  (** Path to the Rust source file. *)
  begin_line : int;  (** First line of the declaration. *)
  end_line : int;  (** Last line of the declaration. *)
}
[@@deriving to_yojson]

type loop_info = {
  loop_id_idx : int; [@key "id"]
  loop_pos : int list; [@key "pos"]
  is_body : bool;
}
[@@deriving to_yojson]

(** Lean function declaration. *)
type function_entry = {
  def_id : int;  (** Charon [FunDeclId] reified to a plain int. *)
  lean_name : string;  (** Fully-qualified Lean name. *)
  lean_file : string;  (** Path relative to this manifest's directory. *)
  rust_name : string;  (** Fully-qualified Rust name (from [item_meta.name]). *)
  is_local : bool;
      (** [true] if defined in the current crate, [false] if external. *)
  source : source;  (** Rust source location (from [item_meta.span]). *)
  is_opaque : bool;
      (** [true] when Aeneas extracted the declaration as an axiom. *)
  can_fail : bool;
      (** [true] when the function's return type is wrapped in [Result]. *)
  can_diverge : bool;  (** [true] when the function may not terminate. *)
  is_rec : bool;
      (** [true] when the function is part of a mutually recursive group. *)
  reducible : bool;
      (** [true] when Aeneas marks the Lean def with [@[reducible]]. *)
  loop : loop_info option; [@default None] [@key "loop"]
      (** Present only on loop-wrapper / loop-body entries *)
  parent_lean_name : string option; [@default None]
      (** Present only on loop-wrapper / loop-body entries *)
}
[@@deriving to_yojson]

(** Lean type declaration. *)
type type_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  rust_name : string;
  is_local : bool;
  source : source;
}
[@@deriving to_yojson]

(** Lean global declaration. *)
type global_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  rust_name : string;
  is_local : bool;
  source : source;
  can_fail : bool;
}
[@@deriving to_yojson]

(** Lean trait declaration. *)
type trait_decl_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  rust_name : string;
  is_local : bool;
  source : source;
}
[@@deriving to_yojson]

(** Lean trait implementation. *)
type trait_impl_entry = {
  def_id : int;
  lean_name : string;
  lean_file : string;
  rust_name : string;
  is_local : bool;
  source : source;
  impl_trait_def_id : int;
      (** [TraitDeclId] of the implemented trait. A valid LLBC trait decl but
          has entry in [trait_decls] iff the trait is not builtin. *)
  impl_trait_rust_name : string;
      (** Full Rust path of the implemented trait. *)
  impl_trait_is_builtin : bool;
      (** [true] when the implemented trait is builtin. *)
}
[@@deriving to_yojson]

type envelope = {
  aeneas_version : string;
  charon_version : string;
      (** The version of charon that emitted the [.llbc] input. *)
  crate_name : string; [@key "crate"]
      (** Identifier of the source Rust crate. *)
  functions : function_entry list;
  types : type_entry list;
  globals : global_entry list;
  trait_decls : trait_decl_entry list;
  trait_impls : trait_impl_entry list;
}
[@@deriving to_yojson]

(* ------------------------------------------------------------------------ *)
(* Mutable accumulator state                                                *)
(*                                                                          *)
(* Lifecycle: [init_if_enabled] at the start of [extract_translated_crate], *)
(* [begin_file_if_enabled] at the top of every [extract_file],              *)
(* [record_*_if_enabled] called from the export-* hooks,                    *)
(* [write_if_enabled] once at the end.                                      *)
(* ------------------------------------------------------------------------ *)

type state = {
  mutable function_entries : function_entry list;
  mutable type_entries : type_entry list;
  mutable global_entries : global_entry list;
  mutable trait_decl_entries : trait_decl_entry list;
  mutable trait_impl_entries : trait_impl_entry list;
  mutable current_lean_file : string;
  mutable current_lean_namespace : string;
  mutable current_in_namespace : bool;
  mutable dest_dir : string;
}

let make_state () : state =
  {
    function_entries = [];
    type_entries = [];
    global_entries = [];
    trait_decl_entries = [];
    trait_impl_entries = [];
    current_lean_file = "";
    current_lean_namespace = "";
    current_in_namespace = true;
    dest_dir = "";
  }

(* One Aeneas process translates one crate, so a module-local singleton. *)
let state : state = make_state ()

let init_if_enabled ~(dest_dir : string) : unit =
  if !Config.emit_json then state.dest_dir <- dest_dir

(* ------------------------------------------------------------------------ *)
(* Entry construction                                                       *)
(* ------------------------------------------------------------------------ *)

(** Add the Lean namespace to a short name to form the full Lean name. *)
let full_lean_name (basename : string) : string =
  if state.current_in_namespace then
    state.current_lean_namespace ^ "." ^ basename
  else basename

(** Extract the Rust source location (file + line range) from a span. *)
let source_of_span (span : Meta.span) : source =
  let data = span.data in
  let file =
    match data.file.name with
    | Virtual s | Local s | NotReal s -> s
  in
  { file; begin_line = data.beg_loc.line; end_line = data.end_loc.line }

let function_entry_of_fun_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.fun_decl) : function_entry =
  let span = def.item_meta.span in
  let lean_name =
    full_lean_name
      (ExtractBase.ctx_get_local_function span def.def_id def.loop_id ctx)
  in
  let parent_lean_name =
    match def.loop_id with
    | None -> None
    | Some _ ->
        Some
          (full_lean_name
             (ExtractBase.ctx_get_local_function span def.def_id None ctx))
  in
  let loop =
    match def.loop_id with
    | None -> None
    | Some (lid, is_body) ->
        Some
          {
            loop_id_idx = Pure.LoopId.to_int lid;
            loop_pos = def.loop_pos;
            is_body;
          }
  in
  let eff = def.signature.fwd_info.effect_info in
  {
    def_id = Pure.FunDeclId.to_int def.def_id;
    lean_name;
    lean_file = state.current_lean_file;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
    is_opaque = Option.is_none def.body;
    can_fail = eff.can_fail;
    can_diverge = eff.can_diverge;
    is_rec = eff.is_rec;
    reducible = def.backend_attributes.reducible;
    loop;
    parent_lean_name;
  }

let type_entry_of_type_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.type_decl) : type_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.TypeDeclId.to_int def.def_id;
    lean_name =
      full_lean_name (ExtractBase.ctx_get_local_type span def.def_id ctx);
    lean_file = state.current_lean_file;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
  }

let global_entry_of_global_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.global_decl) : global_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.GlobalDeclId.to_int def.def_id;
    lean_name = full_lean_name (ExtractBase.ctx_get_global span def.def_id ctx);
    lean_file = state.current_lean_file;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
    can_fail = def.can_fail;
  }

let trait_decl_entry_of_trait_decl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_decl) : trait_decl_entry =
  let span = def.item_meta.span in
  {
    def_id = Pure.TraitDeclId.to_int def.def_id;
    lean_name =
      full_lean_name (ExtractBase.ctx_get_trait_decl span def.def_id ctx);
    lean_file = state.current_lean_file;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
  }

let trait_impl_entry_of_trait_impl (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_impl) : trait_impl_entry =
  let span = def.item_meta.span in
  let impl_trait_id = def.impl_trait.trait_decl_id in
  let impl_trait_decl =
    Pure.TraitDeclId.Map.find impl_trait_id ctx.trans_trait_decls
  in
  {
    def_id = Pure.TraitImplId.to_int def.def_id;
    lean_name =
      full_lean_name (ExtractBase.ctx_get_trait_impl span def.def_id ctx);
    lean_file = state.current_lean_file;
    rust_name = ExtractBase.name_to_string ctx def.item_meta.name;
    is_local = def.item_meta.is_local;
    source = source_of_span span;
    impl_trait_def_id = Pure.TraitDeclId.to_int impl_trait_id;
    impl_trait_rust_name =
      ExtractBase.name_to_string ctx impl_trait_decl.item_meta.name;
    impl_trait_is_builtin = Option.is_some impl_trait_decl.builtin_info;
  }

(* ------------------------------------------------------------------------ *)
(* Pipeline hooks (no-ops when -emit-json is off)                           *)
(* ------------------------------------------------------------------------ *)

let begin_file_if_enabled ~(filename : string) ~(namespace : string)
    ~(in_namespace : bool) : unit =
  if !Config.emit_json then begin
    (* Record the Lean file relative to dest_dir. *)
    let basename = Filename.basename filename in
    let rel =
      match !Config.subdir with
      | None -> basename
      | Some subdir -> Filename.concat subdir basename
    in
    state.current_lean_file <- rel;
    state.current_lean_namespace <- namespace;
    state.current_in_namespace <- in_namespace
  end

let record_fun_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.fun_decl) : unit =
  if !Config.emit_json then
    state.function_entries <-
      function_entry_of_fun_decl ctx def :: state.function_entries

let record_type_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.type_decl) : unit =
  if !Config.emit_json then
    state.type_entries <- type_entry_of_type_decl ctx def :: state.type_entries

let record_global_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.global_decl) : unit =
  if !Config.emit_json then
    state.global_entries <-
      global_entry_of_global_decl ctx def :: state.global_entries

let record_trait_decl_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_decl) : unit =
  if !Config.emit_json then
    state.trait_decl_entries <-
      trait_decl_entry_of_trait_decl ctx def :: state.trait_decl_entries

let record_trait_impl_if_enabled (ctx : ExtractBase.extraction_ctx)
    (def : Pure.trait_impl) : unit =
  if !Config.emit_json then
    state.trait_impl_entries <-
      trait_impl_entry_of_trait_impl ctx def :: state.trait_impl_entries

(* ------------------------------------------------------------------------ *)
(* Writing                                                                  *)
(* ------------------------------------------------------------------------ *)

let write (path : string) (env : envelope) : unit =
  let out = open_out path in
  Fun.protect
    ~finally:(fun () -> close_out out)
    (fun () ->
      Yojson.Safe.pretty_to_channel out (envelope_to_yojson env);
      output_char out '\n')

let write_if_enabled ~(crate_name : string) : string option =
  if !Config.emit_json then begin
    let path = Filename.concat state.dest_dir "translation.json" in
    write path
      {
        aeneas_version = Option.value GitVersion.commit ~default:"unknown";
        charon_version = Charon.CharonVersion.supported_charon_version;
        crate_name;
        functions = List.rev state.function_entries;
        types = List.rev state.type_entries;
        globals = List.rev state.global_entries;
        trait_decls = List.rev state.trait_decl_entries;
        trait_impls = List.rev state.trait_impl_entries;
      };
    Some path
  end
  else None
