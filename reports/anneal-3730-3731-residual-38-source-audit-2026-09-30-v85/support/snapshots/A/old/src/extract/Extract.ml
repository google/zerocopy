(** The generic extraction *)
(* Turn the whole module into a functor: it is very annoying to carry the
   the formatter everywhere...
*)

open Pure
open PureUtils
open TranslateCore
open Config
open Errors
open ExtractErrors
include ExtractTypes

let binop_to_string (ctx : extraction_ctx) =
  PrintPure.binop_to_string (extraction_ctx_to_fmt_env ctx)

let fun_or_op_id_to_string (ctx : extraction_ctx) =
  PrintPure.fun_or_op_id_to_string (extraction_ctx_to_fmt_env ctx)

let generic_args_to_string (ctx : extraction_ctx) =
  PrintPure.generic_args_to_string (extraction_ctx_to_fmt_env ctx)

let texpr_to_string (ctx : extraction_ctx) =
  PrintPure.texpr_to_string (extraction_ctx_to_fmt_env ctx) false "" "  "

(** Compute the names for all the pure functions generated from a rust function.
*)
let extract_fun_decl_register_names (ctx : extraction_ctx)
    (has_decreases_clause : fun_decl -> bool) (def : pure_fun_translation) :
    extraction_ctx =
  match def.f.src with
  | TraitDeclItem (_, _, false) ->
      (* Ignore the trait methods **declarations** (rem.: we do not ignore the trait
         method implementations): we do not need to refer to them directly. We will
         only use their type for the fields of the records we generate for the trait
         declarations *)
      ctx
  | _ -> (
      (* Use the builtin names if necessary *)
      match def.f.builtin_info with
      | Some info ->
          (* Builtin function: register the filtering information, if there is *)
          let ctx =
            match info.keep_params with
            | Some keep ->
                {
                  ctx with
                  funs_filter_type_args_map =
                    FunDeclId.Map.add def.f.def_id keep
                      ctx.funs_filter_type_args_map;
                }
            | _ -> ctx
          in
          let ctx =
            match info.keep_trait_clauses with
            | Some keep ->
                {
                  ctx with
                  funs_filter_trait_clauses_map =
                    FunDeclId.Map.add def.f.def_id keep
                      ctx.funs_filter_trait_clauses_map;
                }
            | _ -> ctx
          in
          let f = def.f in
          let fun_id = (Pure.FunId (FRegular f.def_id), f.loop_id) in
          ctx_add f.item_meta.span (FunId (FromLlbc fun_id)) info.extract_name
            ctx
      | None ->
          (* Not builtin *)
          (* Register the decrease clauses, if necessary *)
          let register_decreases ctx def =
            if has_decreases_clause def then
              (* Add the termination measure *)
              let ctx = ctx_add_termination_measure def ctx in
              (* Add the decreases proof for Lean only *)
              match backend () with
              | Coq | FStar -> ctx
              | HOL4 -> [%craise] def.item_meta.span "Unexpected"
              | Lean -> ctx_add_decreases_proof def ctx
            else ctx
          in
          (* We have to register the function itself, and the loops it
             may contain (which are extracted as functions) *)
          let funs = (def.f :: def.loops) @ def.bodies in
          (* Register the decrease clauses *)
          let ctx = List.fold_left register_decreases ctx funs in
          (* Register the name of the function and the loops *)
          let register_fun ctx f = ctx_add_fun_decl f ctx in
          let register_funs ctx fl = List.fold_left register_fun ctx fl in
          register_funs ctx funs)

(** Simply add the global name to the context. *)
let extract_global_decl_register_names (ctx : extraction_ctx)
    (def : global_decl) : extraction_ctx =
  ctx_add_global_decl_and_body def ctx

(** The following function factorizes the extraction of ADT values.

    Note that patterns can introduce new variables: we thus return an extraction
    context updated with new bindings.

    [is_single_pat]: are we extracting a single pattern (a pattern for a
    let-binding or a lambda)?

    TODO: we don't need something very generic anymore (some definitions used to
    be polymorphic). *)
let extract_adt_g_value (span : Meta.span)
    (extract_value : extraction_ctx -> bool -> 'v -> extraction_ctx)
    (fmt : F.formatter) (ctx : extraction_ctx) (is_single_pat : bool)
    ~(inside : bool) (variant_id : VariantId.id option) (field_values : 'v list)
    (ty : ty) : extraction_ctx =
  let extract_as_tuple () =
    (* This is very annoying: in Coq, we can't write [()] for the value of
       type [unit], we have to write [tt]. *)
    if backend () = Coq && field_values = [] then (
      F.pp_print_string fmt "tt";
      ctx)
    else
      (* If there is exactly one value, we don't print the parentheses.
         Also, for Coq, we need the special syntax ['(...)] if we destruct
         a tuple pattern in a let-binding and the tuple has > 2 values.
      *)
      let use_parentheses, lb, rb =
        if List.length field_values = 1 then (false, "", "")
        else if
          backend () = Coq && is_single_pat && List.length field_values > 2
        then (true, "'(", ")")
        else (true, "(", ")")
      in
      F.pp_print_string fmt lb;
      (* F* doesn't parse lambdas and tuples the same way as other backends: the
         the consequence is that we need to use more parentheses... *)
      let inside =
        match backend () with
        | FStar -> true
        | _ ->
            (* We may need to insert parentheses if there is a single value (meaning
               we did not already inserted parentheses outside) *)
            (not use_parentheses) && inside && List.length field_values = 1
      in
      let ctx =
        Collections.List.fold_left_link
          (fun () ->
            F.pp_print_string fmt ",";
            F.pp_print_space fmt ())
          (fun ctx v -> extract_value ctx inside v)
          ctx field_values
      in
      F.pp_print_string fmt rb;
      ctx
  in
  match ty with
  | TAdt (TTuple, generics) ->
      (* Tuple *)
      (* For now, we only support fully applied tuple constructors *)
      [%cassert] span
        (List.length generics.types = List.length field_values)
        "Only fully applied tuple constructors are currently supported";
      [%cassert] span
        (generics.const_generics = [] && generics.trait_refs = [])
        "Only fully applied tuple constructors are currently supported";
      extract_as_tuple ()
  | TAdt (adt_id, _) -> (
      if
        (* "Regular" ADT *)
        (* We may still extract the ADT as a tuple, if none of the fields are
         named *)
        PureUtils.type_decl_from_type_id_is_tuple_struct
          ctx.trans_ctx.type_ctx.type_infos adt_id
      then
        (* Extract as a tuple *)
        extract_as_tuple ()
      else if
        (* If we are generating a pattern for a let-binding and we target Lean,
           the syntax is: `let ⟨ x0, ..., xn ⟩ := ...`.

           Otherwise, it is: `let Cons x0 ... xn = ...`

           Note that we only do so if the variant is [None]. This means that
           in case the extraction is erroneous (i.e., we did not transform
           a single let pattern into a match, like in:
           [let Some x := y ~> let x = match y with | Some x -> x | None -> ...])
           we might generate erroneous code (e.g., [let Some x := y in ...]).
           This is fine because the code would be erroneous anyway, and it's
           a lot more informative (to debug the error) to see something like
           [let Some x := y in ...] rather than [let ⟨ x ⟩ := y in ...]
        *)
        is_single_pat && backend () = Lean && variant_id = None
      then (
        F.pp_print_string fmt "⟨";
        F.pp_print_space fmt ();
        let ctx =
          Collections.List.fold_left_link
            (fun _ ->
              F.pp_print_string fmt ",";
              F.pp_print_space fmt ())
            (fun ctx v -> extract_value ctx true v)
            ctx field_values
        in
        F.pp_print_space fmt ();
        F.pp_print_string fmt "⟩";
        ctx)
      else
        (* We print something of the form: [Cons field0 ... fieldn].
           We could update the code to print something of the form:
           [{ field0=...; ...; fieldn=...; }] in case of structures.

           Also, Lean seems not to support the notation [let Cons field0 ... fieldn := ...]
           (it seems to be a bug - TODO: report) so for this backend we generate something
           of the shape:
           {[
             let ⟨ field0, ..., fieldn ⟩ := ...
           ]}
         *)
        match (is_single_pat, Config.backend ()) with
        | true, Lean ->
            F.pp_print_string fmt "⟨";
            let first = ref true in
            let ctx =
              Collections.List.fold_left
                (fun ctx v ->
                  if !first then first := false else F.pp_print_string fmt ",";
                  F.pp_print_space fmt ();
                  extract_value ctx true v)
                ctx field_values
            in
            F.pp_print_space fmt ();
            F.pp_print_string fmt "⟩";
            ctx
        | _ ->
            let cons =
              match variant_id with
              | Some vid -> ctx_get_variant span adt_id vid ctx
              | None -> ctx_get_struct span adt_id ctx
            in
            let use_parentheses = inside && field_values <> [] in
            if use_parentheses then F.pp_print_string fmt "(";
            F.pp_print_string fmt cons;
            let ctx =
              Collections.List.fold_left
                (fun ctx v ->
                  F.pp_print_space fmt ();
                  extract_value ctx true v)
                ctx field_values
            in
            if use_parentheses then F.pp_print_string fmt ")";
            ctx)
  | _ ->
      [%admit_raise] span "Inconsistently typed value" fmt;
      ctx

(* Extract globals in the same way as variables *)
let extract_global (span : Meta.span) (ctx : extraction_ctx) (fmt : F.formatter)
    ~(inside : bool) (id : A.GlobalDeclId.id) (generics : generic_args) : unit =
  let use_brackets = inside && generics <> empty_generic_args in
  F.pp_open_hvbox fmt ctx.indent_incr;
  if use_brackets then F.pp_print_string fmt "(";
  (* Extract the global name *)
  F.pp_print_string fmt (ctx_get_global span id ctx);
  (* Extract the generics.

     We have to lookup the information about the implicit/explicit parameters.
     Note that the global declaration (from which we retrieve this information)
     may be missing if there were some errors.
  *)
  let explicit =
    Option.map
      (fun (d : global_decl) -> d.explicit_info)
      (GlobalDeclId.Map.find_opt id ctx.trans_globals)
  in
  extract_generic_args span ctx fmt TypeDeclId.Set.empty ~explicit generics;
  if use_brackets then F.pp_print_string fmt ")";
  F.pp_close_box fmt ()

(* Filter the generics of a function if it is builtin *)
let fun_builtin_filter_types_trait_clauses (ty_to_string : 'a -> string)
    (clause_to_string : 'b -> string) (id : FunDeclId.id) (types : 'a list)
    (explicit : explicit_info option) (clauses : 'b list) (ctx : extraction_ctx)
    : ('a list * explicit_info option * 'b list, string) Result.result =
  let filter_f filter ls =
    List.filter_map
      (fun (b, ty) -> if b then Some ty else None)
      (List.combine filter ls)
  in
  let clauses =
    match FunDeclId.Map.find_opt id ctx.funs_filter_trait_clauses_map with
    | None -> Result.Ok clauses
    | Some filter ->
        if List.length filter <> List.length types then (
          let decl = FunDeclId.Map.find id ctx.trans_funs in
          let err =
            "Ill-formed builtin information for function "
            ^ name_to_string ctx decl.f.item_meta.name
            ^ ": "
            ^ string_of_int (List.length filter)
            ^ " filtering arguments provided for "
            ^ string_of_int (List.length clauses)
            ^ " trait clauses ("
            ^ String.concat ", " (List.map clause_to_string clauses)
            ^ ")"
          in
          [%save_error_opt_span] None err;
          Result.Error err)
        else Result.Ok (filter_f filter clauses)
  in
  let types =
    match FunDeclId.Map.find_opt id ctx.funs_filter_type_args_map with
    | None -> Result.Ok (types, explicit)
    | Some filter ->
        if List.length filter <> List.length types then (
          let decl = FunDeclId.Map.find id ctx.trans_funs in
          let err =
            "Ill-formed builtin information for function "
            ^ name_to_string ctx decl.f.item_meta.name
            ^ ": "
            ^ string_of_int (List.length filter)
            ^ " filtering arguments provided for "
            ^ string_of_int (List.length types)
            ^ " type arguments ("
            ^ String.concat ", " (List.map ty_to_string types)
            ^ ")"
          in
          [%save_error_opt_span] None err;
          Result.Error err)
        else
          let types = filter_f filter types in
          let explicit =
            Option.map
              (fun e ->
                { e with explicit_types = filter_f filter e.explicit_types })
              explicit
          in
          Result.Ok (types, explicit)
  in
  match (clauses, types) with
  | Result.Ok clauses, Result.Ok (types, explicit) ->
      Result.Ok (types, explicit, clauses)
  | Result.Error msg, _ | _, Result.Error msg -> Result.Error msg

(** [inside]: see {!extract_ty}. [with_type]: do we also generate a type
    annotation? This is necessary for backends like Coq when we write lambdas
    (Coq is not powerful enough to infer the type).

    As a pattern can introduce new variables, we return an extraction context
    updated with new bindings. *)
let rec extract_tpat (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) ~(is_let : bool) ~(inside : bool) ?(with_type = false)
    (v : tpat) : extraction_ctx =
  if with_type then F.pp_print_string fmt "(";
  let is_pattern = true in
  let inside = inside && not with_type in
  let ctx =
    match v.pat with
    | PConstant cv ->
        extract_literal span fmt ~is_pattern ~inside cv;
        ctx
    | PBound _ ->
        (* We should have opened the pattern *)
        [%internal_error] span
    | POpen (v, _) ->
        let vname = ctx_compute_var_basename span ctx v.basename v.ty in
        let ctx, vname = ctx_add_var span vname v.id ctx in
        F.pp_print_string fmt vname;
        ctx
    | PIgnored ->
        F.pp_print_string fmt "_";
        ctx
    | PAdt av ->
        let extract_value ctx inside v =
          extract_tpat span ctx fmt ~is_let ~inside v
        in
        extract_adt_g_value span extract_value fmt ctx is_let ~inside
          av.variant_id av.fields v.ty
  in
  if with_type then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    extract_ty span ctx fmt TypeDeclId.Set.empty ~inside:false v.ty;
    F.pp_print_string fmt ")");
  ctx

(** Return true if we need to wrap a succession of let-bindings in a [do ...]
    block (because some of them are monadic) *)
let lets_require_wrap_in_do (span : Meta.span)
    (lets : (bool * tpat * texpr) list) : bool =
  match backend () with
  | Lean ->
      (* For Lean, we wrap in a block iff at least one of the let-bindings is monadic *)
      List.exists (fun (m, _, _) -> m) lets
  | HOL4 ->
      (* HOL4 is similar to HOL4, but we add a sanity check *)
      let wrap_in_do = List.exists (fun (m, _, _) -> m) lets in
      if wrap_in_do then
        [%sanity_check] span (List.for_all (fun (m, _, _) -> m) lets);
      wrap_in_do
  | FStar | Coq -> false

(** HOL4 has a special treatment: because it doesn't support dependent types, we
    don't have a specific operator for the casts *)
let extract_cast_kind_hol4 (span : Meta.span)
    (extract_expr : inside:bool -> texpr -> unit) (fmt : F.formatter)
    ~(inside : bool) (kind : cast_kind) (arg : texpr) : unit =
  match kind with
  | CastLit (src, tgt) ->
      (* Casting, say, an u32 to an i32 would be done as follows:
         {[
           mk_i32 (u32_to_int x)
         ]}
      *)
      if inside then F.pp_print_string fmt "(";
      F.pp_print_string fmt ("mk_" ^ scalar_name tgt);
      F.pp_print_space fmt ();
      F.pp_print_string fmt "(";
      F.pp_print_string fmt (scalar_name src ^ "_to_int");
      F.pp_print_space fmt ();
      extract_expr ~inside:true arg;
      F.pp_print_string fmt ")";
      if inside then F.pp_print_string fmt ")"
  | CastRawPtr _ ->
      [%craise] span "Raw pointer casts are not implemented for HOL4"

(** Extract a cast when the backend is not HOL4 (which receives a special
    treatment) *)
let extract_cast_kind_gen (span : Meta.span)
    (extract_expr : inside:bool -> texpr -> unit) (fmt : F.formatter)
    ~(inside : bool) (kind : cast_kind) (arg : texpr) : unit =
  match kind with
  | CastLit (src, tgt) ->
      let integer_type_to_string (ty : integer_type) : string =
        if backend () = Lean then
          match ty with
          | Unsigned _ -> "." ^ int_name ty
          | Signed _ -> "." ^ int_name ty
        else
          StringUtils.capitalize_first_letter
            (PrintPure.integer_type_to_string ty)
      in
      if inside then F.pp_print_string fmt "(";
      (* Rem.: the source type is an implicit parameter *)
      (* Different cases depending on the conversion *)
      (let cast_str, src, tgt =
         match (src, tgt) with
         | _, _ when literal_type_is_integer src && literal_type_is_integer tgt
           ->
             let src, tgt = (literal_as_integer src, literal_as_integer tgt) in
             let cast_str =
               match backend () with
               | Coq | FStar -> "scalar_cast"
               | Lean ->
                   let signed_src = Scalars.integer_type_is_signed src in
                   let signed_tgt = Scalars.integer_type_is_signed tgt in
                   if signed_src = signed_tgt then
                     if signed_src then "IScalar.cast" else "UScalar.cast"
                   else if signed_src then "IScalar.hcast"
                   else "UScalar.hcast"
               | HOL4 -> admit_string __FILE__ __LINE__ span "Unreachable"
             in
             let src =
               if backend () <> Lean then Some (integer_type_to_string src)
               else None
             in
             let tgt = integer_type_to_string tgt in
             (cast_str, src, Some tgt)
         | TBool, TInt _ | TBool, TUInt _ ->
             let tgt = literal_as_integer tgt in
             let cast_str =
               match backend () with
               | Coq | FStar -> "scalar_cast_bool"
               | Lean ->
                   if Scalars.integer_type_is_signed tgt then
                     "IScalar.cast_fromBool"
                   else "UScalar.cast_fromBool"
               | HOL4 -> admit_string __FILE__ __LINE__ span "Unreachable"
             in
             let tgt = integer_type_to_string tgt in
             (cast_str, None, Some tgt)
         | TInt _, TBool | TUInt _, TBool ->
             (* This is not allowed by rustc: the way of doing it in Rust is: [x != 0] *)
             [%craise] span "Unexpected cast: integer to bool"
         | TBool, TBool ->
             (* There shouldn't be any cast here. Note that if
                one writes [b as bool] in Rust (where [b] is a
                boolean), it gets compiled to [b] (i.e., no cast
                is introduced). *)
             [%craise] span "Unexpected cast: bool to bool"
         | _ -> [%craise] span "Unreachable"
       in
       (* Print the name of the function *)
       F.pp_print_string fmt cast_str;
       (* Print the src type argument *)
       (match src with
       | None -> ()
       | Some src ->
           F.pp_print_space fmt ();
           F.pp_print_string fmt src);
       (* Print the tgt type argument *)
       match tgt with
       | None -> ()
       | Some tgt ->
           F.pp_print_space fmt ();
           F.pp_print_string fmt tgt);
      (* Extract the argument *)
      F.pp_print_space fmt ();
      extract_expr ~inside:true arg;
      if inside then F.pp_print_string fmt ")"
  | CastRawPtr ((_, _), (tgt_ty, tgt_mut)) ->
      [%cassert] span
        (backend () = Lean)
        "Casts between raw pointers are only supported in the Lean backend";
      if inside then F.pp_print_string fmt "(";
      (* Print the name of the function *)
      F.pp_print_string fmt "RawPtr.cast_scalar";
      (* Print the target type argument and mutability *)
      let tgt_ty : integer_type =
        match tgt_ty with
        | TInt ty -> Signed ty
        | TUInt ty -> Unsigned ty
        | _ ->
            [%craise] span "Can only generate code for casts between integers"
      in
      let integer_type_to_string (ty : integer_type) : string =
        if backend () = Lean then
          match ty with
          | Unsigned _ -> "Std." ^ int_name ty
          | Signed _ -> "Std." ^ int_name ty
        else
          StringUtils.capitalize_first_letter
            (PrintPure.integer_type_to_string ty)
      in
      let tgt = integer_type_to_string tgt_ty in
      F.pp_print_space fmt ();
      F.pp_print_string fmt tgt;
      let tgt_mut =
        match tgt_mut with
        | Mut -> ".Mut"
        | Const -> ".Const"
      in
      F.pp_print_space fmt ();
      F.pp_print_string fmt tgt_mut;
      (* Extract the argument *)
      F.pp_print_space fmt ();
      extract_expr ~inside:true arg;
      if inside then F.pp_print_string fmt ")"

let extract_cast_kind (span : Meta.span)
    (extract_expr : inside:bool -> texpr -> unit) (fmt : F.formatter)
    ~(inside : bool) (kind : cast_kind) (arg : texpr) : unit =
  (* HOL4 has a special treatment *)
  match backend () with
  | HOL4 -> extract_cast_kind_hol4 span extract_expr fmt ~inside kind arg
  | FStar | Coq | Lean ->
      extract_cast_kind_gen span extract_expr fmt ~inside kind arg

(** Format a unary operation

    Inputs:
    - a formatter for expressions (called on the argument of the unop)
    - extraction context (see below)
    - formatter
    - expression formatter
    - [inside]
    - unop
    - argument *)
let extract_unop (span : Meta.span)
    (extract_expr : inside:bool -> texpr -> unit) (fmt : F.formatter)
    ~(inside : bool) (unop : unop) (arg : texpr) : unit =
  match unop with
  | Not _ | Neg _ | ArrayToSlice ->
      let unop = unop_name unop in
      if inside then F.pp_print_string fmt "(";
      F.pp_print_string fmt unop;
      F.pp_print_space fmt ();
      extract_expr ~inside:true arg;
      if inside then F.pp_print_string fmt ")"
  | Cast kind -> extract_cast_kind span extract_expr fmt ~inside kind arg

(** Format a binary operation

    Inputs:
    - a formatter for expressions (called on the arguments of the binop)
    - extraction context (see below)
    - formatter
    - expression formatter
    - [inside]
    - binop
    - argument 0
    - argument 1 *)
let extract_binop (span : Meta.span) (ctx : extraction_ctx)
    (extract_expr : inside:bool -> texpr -> unit) (fmt : F.formatter)
    ~(inside : bool) (binop : binop) (arg0 : texpr) (arg1 : texpr) : unit =
  if inside then F.pp_print_string fmt "(";
  (* Some binary operations have a special notation depending on the backend *)
  (match (backend (), binop) with
  | HOL4, (Eq _ | Ne _)
  | (FStar | Coq | Lean), (Eq _ | Lt _ | Le _ | Ne _ | Ge _ | Gt _ | BoolOr)
  | ( Lean,
      ( Div (OPanic, _)
      | Rem (OPanic, _)
      | Add (OPanic, _)
      | Sub (OPanic, _)
      | Mul (OPanic, _)
      | Shl (OPanic, _, _)
      | Shr (OPanic, _, _)
      | BitXor _ | BitOr _ | BitAnd _ ) ) ->
      let binop_str =
        match binop with
        | Eq _ -> "="
        | Lt _ -> "<"
        | Le _ -> "<="
        | Ne _ -> if backend () = Lean then "!=" else "<>"
        | Ge _ -> ">="
        | Gt _ -> ">"
        | Div (OPanic, _) -> "/"
        | Rem (OPanic, _) -> "%"
        | Add (OPanic, _) -> "+"
        | Sub (OPanic, _) -> "-"
        | Mul (OPanic, _) -> "*"
        | Shl (OPanic, _, _) -> "<<<"
        | Shr (OPanic, _, _) -> ">>>"
        | BitXor _ -> "^^^"
        | BitOr _ -> "|||"
        | BitAnd _ -> "&&&"
        | BoolOr -> "||"
        | _ ->
            [%add_loc] admit_string span
              ("Unimplemented binary operation: " ^ binop_to_string ctx binop)
      in
      let binop_str =
        match (backend (), binop) with
        | Coq, BoolOr -> binop_str
        | Coq, _ -> "s" ^ binop_str
        | _ -> binop_str
      in
      extract_expr ~inside:true arg0;
      F.pp_print_space fmt ();
      F.pp_print_string fmt binop_str;
      F.pp_print_space fmt ();
      extract_expr ~inside:true arg1
  | ( Lean,
      ( Add (OWrap, _)
      | Sub (OWrap, _)
      | Mul (OWrap, _)
      | Div (OWrap, _)
      | Shl (OWrap, _, _)
      | Shr (OWrap, _, _) ) ) ->
      let binop =
        match binop with
        | Add _ -> "add"
        | Sub _ -> "sub"
        | Mul _ -> "mul"
        | Div _ -> "div"
        | Shl _ -> "shl"
        | Shr _ -> "shr"
        | _ ->
            [%add_loc] admit_string span "Internal error: please file an issue"
      in
      let ty = ty_as_integer span arg0.ty in
      let binop =
        "Std."
        ^ StringUtils.capitalize_first_letter (int_name ty)
        ^ ".wrapping_" ^ binop
      in
      F.pp_print_string fmt binop;
      F.pp_print_space fmt ();
      extract_expr ~inside:true arg0;
      F.pp_print_space fmt ();
      extract_expr ~inside:true arg1
  | _ ->
      let binop_is_shift =
        match binop with
        | Shl _ | Shr _ -> true
        | _ -> false
      in
      let binop = named_binop_name binop in
      F.pp_print_string fmt binop;
      (* In the case of F*, for shift operations, because machine integers
         are simply integers with a refinement, if the second argument is a
         constant we need to provide the second implicit type argument *)
      if binop_is_shift && backend () = FStar && is_const arg1 then (
        F.pp_print_space fmt ();
        let ty = ty_as_integer span arg1.ty in
        F.pp_print_string fmt
          ("#" ^ StringUtils.capitalize_first_letter (int_name ty)));
      F.pp_print_space fmt ();
      extract_expr ~inside:true arg0;
      F.pp_print_space fmt ();
      extract_expr ~inside:true arg1);
  if inside then F.pp_print_string fmt ")"

(** [inside]: controls the introduction of parentheses. See [extract_ty]

    TODO: replace the formatting boolean [inside] with something more general?
    Also, it seems we don't really use it... Cases to consider:
    - right-expression in a let: [let x = re in _] (never parentheses?)
    - next expression in a let: [let x = _ in next_e] (never parentheses?)
    - application argument: [f (exp)]
    - match/if scrutinee: [if exp then _ else _]/[match exp | _ -> _] *)

let extract_texpr_errors (fmt : F.formatter) =
  match backend () with
  | FStar | Coq -> F.pp_print_string fmt "admit"
  | Lean -> F.pp_print_string fmt "sorry"
  | HOL4 -> F.pp_print_string fmt "(* ERROR: could not generate the code *)"

(** - [inside_do]: [true] if we are inside a do block. In Lean, controls whether
      we can print let-bindings or if we need to insert a [do] first. *)
let rec extract_texpr (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) ~(inside : bool) ~(inside_do : bool) (e : texpr) : unit
    =
  let is_pattern = false in
  match e.e with
  | FVar var_id ->
      let var_name = ctx_get_var span var_id ctx in
      F.pp_print_string fmt var_name
  | BVar _ -> [%internal_error] span
  | CVar var_id ->
      let var_name = ctx_get_const_generic_var span Item var_id ctx in
      F.pp_print_string fmt var_name
  | Const cv -> extract_literal span fmt ~is_pattern ~inside cv
  | App _ ->
      let app, args = destruct_apps e in
      extract_App span ctx fmt ~inside ~inside_do app args e.ty
  | Lambda _ ->
      let xl, e = raw_destruct_lambdas e in
      extract_Lambda (span : Meta.span) ctx fmt ~inside xl e
  | Qualif _ ->
      (* We use the app case *)
      extract_App span ctx fmt ~inside ~inside_do e [] e.ty
  | Let (_, _, _, _) -> extract_lets span ctx fmt ~inside ~inside_do e
  | Switch (scrut, body) ->
      extract_Switch span ctx fmt ~inside ~inside_do scrut body
  | Meta (m, e) -> extract_meta span ctx fmt ~inside ~inside_do m e
  | StructUpdate supd -> extract_StructUpdate span ctx fmt ~inside supd e.ty
  | Loop _ ->
      (* The loop nodes should have been eliminated in {!PureMicroPasses} *)
      [%admit_raise] span "Unreachable" fmt
  | EError (_, _) -> extract_texpr_errors fmt

(* Extract an application *or* a top-level qualif (function extraction has
 * to handle top-level qualifiers, so it seemed more natural to merge the
 * two cases) *)
and extract_App (span : Meta.span) (ctx : extraction_ctx) (fmt : F.formatter)
    ~(inside : bool) ~(inside_do : bool) (app : texpr) (args : texpr list)
    (out_ty : ty) : unit =
  (* We don't do the same thing if the app is a top-level identifier (function,
   * ADT constructor...) or a "regular" expression *)
  match app.e with
  | Qualif qualif -> (
      (* Top-level qualifier *)
      match (qualif.id, out_ty) with
      | FunOrOp fun_id, _ ->
          extract_function_call span ctx fmt ~inside ~inside_do fun_id
            qualif.generics args
      | Global global_id, _ ->
          assert (args = []);
          extract_global span ctx fmt ~inside global_id qualif.generics
      | ( AdtCons { adt_id = TBuiltin TArray; _ },
          TAdt (TBuiltin TArray, { types = [ ty ]; _ }) ) ->
          extract_array_or_slice span ctx fmt ~inside ~is_array:true ty args
      | ( AdtCons { adt_id = TBuiltin TSlice; _ },
          TAdt (TBuiltin TArray, { types = [ ty ]; _ }) ) ->
          extract_array_or_slice span ctx fmt ~inside ~is_array:false ty args
      | AdtCons adt_cons_id, _ ->
          extract_adt_cons span ctx fmt ~inside ~inside_do adt_cons_id
            qualif.generics args
      | Proj proj, _ ->
          extract_field_projector span ctx fmt ~inside ~inside_do app proj
            qualif.generics args out_ty
      | ScalarValProj ty, _ ->
          extract_scalar_val_projector span ctx fmt ~inside ty args
      | TraitConst (trait_ref, const_id), _ ->
          extract_trait_ref span ctx fmt TypeDeclId.Set.empty ~inside:true
            trait_ref;
          let name =
            ctx_get_trait_const span trait_ref.trait_decl_ref.trait_decl_id
              const_id ctx
          in
          let add_brackets (s : string) =
            if backend () = Coq then "(" ^ s ^ ")" else s
          in
          F.pp_print_string fmt ("." ^ add_brackets name)
      | MkDynTrait trait_ref, _ ->
          (* Open parentheses *)
          if inside then F.pp_print_string fmt "(";
          F.pp_print_string fmt (dyn_constructor ());
          F.pp_print_space fmt ();
          F.pp_print_string fmt "_";
          F.pp_print_space fmt ();
          extract_trait_ref span ctx fmt TypeDeclId.Set.empty ~inside:true
            trait_ref;
          (* Print the arguments *)
          List.iter
            (fun ve ->
              F.pp_print_space fmt ();
              extract_texpr span ctx fmt ~inside:true ~inside_do ve)
            args;
          (* Close parentheses *)
          if inside then F.pp_print_string fmt ")"
      | LoopOp, _ ->
          (* Open a box *)
          F.pp_open_vbox fmt 2;
          (* Open parentheses *)
          if inside then F.pp_print_string fmt "(";
          (* The loop operator *)
          F.pp_print_string fmt "loop";
          (* The arguments *)
          List.iter
            (fun ve ->
              F.pp_print_space fmt ();
              F.pp_open_hovbox fmt 2;
              extract_texpr span ctx fmt ~inside:true ~inside_do:false ve;
              F.pp_close_box fmt ())
            args;
          (* Close parentheses *)
          if inside then F.pp_print_string fmt ")";
          (* Close the box *)
          F.pp_close_box fmt ())
  | _ ->
      (* "Regular" expression *)
      (* Open parentheses *)
      if inside then F.pp_print_string fmt "(";
      (* Print the app expression *)
      let app_inside = (inside && args = []) || args <> [] in
      extract_texpr span ctx fmt ~inside:app_inside ~inside_do app;
      (* Print the arguments *)
      List.iter
        (fun ve ->
          F.pp_print_space fmt ();
          extract_texpr span ctx fmt ~inside:true ~inside_do ve)
        args;
      (* Close parentheses *)
      if inside then F.pp_print_string fmt ")"

and extract_array_or_slice (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) ~(inside : bool) ~(is_array : bool) (args_ty : ty)
    (args : texpr list) : unit =
  [%cassert] span is_array "Unimplemented";
  (* Open the boxes *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  let need_paren = inside in
  if need_paren then F.pp_print_string fmt "(";

  (* In case the array is empty we use a special [Array.empty] construct -
     the reason is that otherwise it is not possible to infer the type of the
     array.Aeneas
     TODO: doing this *here* is a bit of a hack.
  *)
  if args = [] then (
    let cs =
      match backend () with
      | Lean -> "Std.Array.empty"
      | _ -> "Array_empty"
    in
    F.pp_print_string fmt cs;
    F.pp_print_space fmt ();
    extract_ty span ctx fmt TypeDeclId.Set.empty ~inside:true args_ty)
  else (
    (* Print the array constructor.

     Note that we don't need to print the type parameter, which
     is implicit. *)
    (* Open the box for `Array.replicate T N [` *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    let cs = ctx_get_struct span (TBuiltin TArray) ctx in
    F.pp_print_string fmt cs;
    (* Print the parameters *)
    F.pp_print_space fmt ();
    extract_const_generic span ctx fmt ~inside:true
      (CgValue (VScalar (UnsignedScalar (Usize, Z.of_int (List.length args)))));
    F.pp_print_space fmt ();
    F.pp_print_string fmt "[";
    (* Close the box for `Array.mk T N [` *)
    F.pp_close_box fmt ();
    (* Print the values *)
    let delimiter =
      match backend () with
      | Lean -> ","
      | Coq | FStar | HOL4 -> ";"
    in
    F.pp_print_space fmt ();
    F.pp_open_hovbox fmt 0;
    Collections.List.iter_link
      (fun () ->
        F.pp_print_string fmt delimiter;
        F.pp_print_space fmt ())
      (extract_texpr span ctx fmt ~inside:false ~inside_do:false)
      args;
    (* Close the boxes *)
    F.pp_close_box fmt ();
    if args <> [] then F.pp_print_space fmt ();
    F.pp_print_string fmt "]");
  if need_paren then F.pp_print_string fmt ")";
  F.pp_close_box fmt ()

(** Subcase of the app case: function call *)
and extract_function_call (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) ~(inside : bool) ~(inside_do : bool)
    (fid : fun_or_op_id) (generics : generic_args) (args : texpr list) : unit =
  [%ldebug
    fun_or_op_id_to_string ctx fid
    ^ "\n- generics: "
    ^ generic_args_to_string ctx generics
    ^ "\n- args: "
    ^ String.concat ", " (List.map (texpr_to_string ctx) args)];
  match (fid, args) with
  | Unop unop, [ arg ] ->
      (* A unop can have *at most* one argument (the result can't be a function!).
       * Note that the way we generate the translation, we shouldn't get the
       * case where we have no argument (all functions are fully instantiated,
       * and no AST transformation introduces partial calls). *)
      extract_unop span
        (extract_texpr span ctx fmt ~inside_do)
        fmt ~inside unop arg
  | Binop binop, [ arg0; arg1 ] ->
      (* Number of arguments: similar to unop *)
      extract_binop span ctx
        (extract_texpr span ctx fmt ~inside_do)
        fmt ~inside binop arg0 arg1
  | Fun fun_id, _ ->
      let use_brackets = inside in
      if use_brackets then F.pp_print_string fmt "(";
      (* Print the function name.

         For the function name: the id is not the same depending on whether
         we call a trait method and a "regular" function (remark: trait
         method *implementations* are considered as regular functions here;
         only calls to method of traits which are parameterized in a where
         clause have a special treatment.

         Remark: the reason why trait method declarations have a special
         treatment is that, as traits are extracted to records, we may
         allow collisions between trait item names and some other names,
         while we do not allow collisions between function names.

         # Impl trait refs:
         ==================
         When the trait ref refers to an impl, in
         [InterpreterStatement.eval_transparent_function_call_symbolic] we
         replace the call to the trait impl method to a call to the function
         which implements the trait method (that is, we "forget" that we
         called a trait method, and treat it as a regular function call).

         # Provided trait methods:
         =========================
         Calls to provided trait methods also have a special treatment.
         For now, we do not allow overriding provided trait methods (methods
         for which a default implementation is provided in the trait declaration).
         Whenever we translate a provided trait method, we translate it once as
         a function which takes a trait ref as input. We have to handle this
         case below.

         With an example, if in Rust we write:
         {[
           fn Foo {
             fn f(&self) -> u32; // Required
             fn ret_true(&self) -> bool { true } // Provided
           }
         ]}

         We generate:
         {[
           structure Foo (Self : Type) = {
             f : Self -> result u32
           }

           let ret_true (Self : Type) (self_clause : Foo Self) (self : Self) : result bool =
             true
         ]}
      *)
      (match fun_id with
      | FromLlbc (TraitMethod (trait_ref, method_name, _fun_decl_id), lp_id) ->
          let trait_decl_id = trait_ref.trait_decl_ref.trait_decl_id in
          let trait_decl =
            TraitDeclId.Map.find trait_decl_id ctx.trans_trait_decls
          in

          [%sanity_check] trait_decl.item_meta.span (lp_id = None);
          extract_trait_ref trait_decl.item_meta.span ctx fmt
            TypeDeclId.Set.empty ~inside:true trait_ref;
          let fun_name =
            ctx_get_trait_method span trait_ref.trait_decl_ref.trait_decl_id
              method_name ctx
          in
          let add_brackets (s : string) =
            if backend () = Coq then "(" ^ s ^ ")" else s
          in
          F.pp_print_string fmt ("." ^ add_brackets fun_name)
      | _ ->
          let fun_name = ctx_get_function span fun_id ctx in
          F.pp_print_string fmt fun_name);

      (* Sanity check: HOL4 doesn't support const generics *)
      [%sanity_check] span (generics.const_generics = [] || backend () <> HOL4);
      (* Compute the information about the explicit/implicit input type parameters *)
      let explicit =
        let lookup is_trait_method fun_decl_id lp_id =
          try
            (* Lookup the function to retrieve the signature information *)
            let trans_fun =
              [%silent_unwrap] span
                (A.FunDeclId.Map.find_opt fun_decl_id ctx.trans_funs)
            in
            let trans_fun =
              match lp_id with
              | None -> trans_fun.f
              | Some (lp_id, true) -> Pure.LoopId.nth trans_fun.bodies lp_id
              | Some (lp_id, false) -> Pure.LoopId.nth trans_fun.loops lp_id
            in
            let explicit = trans_fun.signature.explicit_info in
            (* If it is a trait method, we need to remove the prefix
               which accounts for the generics of the impl. *)
            let explicit =
              adjust_explicit_info explicit is_trait_method generics
            in
            (* *)
            Some explicit
          with CFailure _ ->
            (* Fallback if, for instance, we could not lookup the declaration *)
            [%save_error] span "Internal error";
            None
        in
        match fun_id with
        | FromLlbc (FunId (FRegular fun_decl_id), lp_id) ->
            lookup false fun_decl_id lp_id
        | FromLlbc (TraitMethod (_trait_ref, _method_name, fun_decl_id), lp_id)
          -> lookup true fun_decl_id lp_id
        | FromLlbc (FunId (FBuiltin aid), _) ->
            Some
              (Builtin.BuiltinFunIdMap.find aid ctx.builtin_sigs).explicit_info
        | Pure (UpdateAtIndex Array) ->
            Some
              {
                explicit_types = [ Implicit ];
                explicit_const_generics = [ Implicit ];
              }
        | Pure (UpdateAtIndex Slice) ->
            Some { explicit_types = [ Implicit ]; explicit_const_generics = [] }
        | Pure Discriminant ->
            Some { explicit_types = [ Implicit ]; explicit_const_generics = [] }
        | Pure ToResult ->
            Some { explicit_types = [ Implicit ]; explicit_const_generics = [] }
        | Pure ResultUnwrapMut ->
            Some
              {
                explicit_types = [ Implicit; Implicit ];
                explicit_const_generics = [];
              }
        | Pure _ -> None
      in
      (* Filter the generics.

         We might need to filter some of the type arguments, if the type
         is builtin (for instance, we filter the global allocator type
         argument for `Vec::new`).
      *)
      let types_explicit_traits =
        match fun_id with
        | FromLlbc (FunId (FRegular id), _) ->
            fun_builtin_filter_types_trait_clauses (ty_to_string ctx)
              (trait_ref_to_string ctx) id generics.types explicit
              generics.trait_refs ctx
        | _ -> Result.Ok (generics.types, explicit, generics.trait_refs)
      in
      (match types_explicit_traits with
      | Ok (types, explicit, trait_refs) ->
          extract_generic_args span ctx fmt TypeDeclId.Set.empty ~explicit
            { generics with types; trait_refs }
      | Error err ->
          extract_generic_args span ctx fmt TypeDeclId.Set.empty ~explicit
            generics;
          [%save_error] span err;
          F.pp_print_string fmt
            "/- ERROR: ill-formed builtin: invalid number of filtering \
             arguments -/");
      (* Print the arguments *)
      List.iter
        (fun ve ->
          F.pp_print_space fmt ();
          extract_texpr span ctx fmt ~inside:true ~inside_do ve)
        args;
      (* Close the box for the function call *)
      (*F.pp_close_box fmt ();*)
      (* Return *)
      if use_brackets then F.pp_print_string fmt ")"
  | (Unop _ | Binop _), _ ->
      [%admit_raise] span
        ("Unreachable:\n" ^ "Function: " ^ show_fun_or_op_id fid
       ^ ",\nNumber of arguments: "
        ^ string_of_int (List.length args)
        ^ ",\nArguments: "
        ^ String.concat " " (List.map show_texpr args))
        fmt

(** Subcase of the app case: ADT constructor *)
and extract_adt_cons (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) ~(inside : bool) ~(inside_do : bool)
    (adt_cons : adt_cons_id) (generics : generic_args) (args : texpr list) :
    unit =
  let e_ty = TAdt (adt_cons.adt_id, generics) in
  let is_single_pat = false in
  (* Sanity check: make sure the expr is not a tuple constructor
     with no arguments (the properly extracted expr would be a function) *)
  [%sanity_check] span
    (not (adt_cons.adt_id = TTuple && generics.types != [] && args = []));
  let _ =
    extract_adt_g_value span
      (fun ctx inside e ->
        extract_texpr span ctx fmt ~inside ~inside_do e;
        ctx)
      fmt ctx is_single_pat ~inside adt_cons.variant_id args e_ty
  in
  ()

(** Subcase of the app case: ADT field projector. *)
and extract_field_projector (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) ~(inside : bool) ~(inside_do : bool)
    (original_app : texpr) (proj : projection) (_generics : generic_args)
    (args : texpr list) (out_ty : ty) : unit =
  (* We isolate the first argument (if there is), in order to pretty print the
   * projection ([x.field] instead of [MkAdt?.field x] *)
  match args with
  | [ arg ] ->
      let is_tuple_struct =
        PureUtils.type_decl_from_type_id_is_tuple_struct
          ctx.trans_ctx.type_ctx.type_infos proj.adt_id
      in
      (* Check if we extract the type as a tuple, and it only has one field.
         In this case, there is no projection. *)
      let num_fields =
        match proj.adt_id with
        | TAdtId id -> (
            let d = TypeDeclId.Map.find id ctx.trans_types in
            match d.kind with
            | Struct fields -> Some (List.length fields)
            | _ -> None)
        | _ -> None
      in
      let has_one_field =
        match num_fields with
        | Some len -> len = 1
        | None -> false
      in
      if is_tuple_struct && has_one_field then
        extract_texpr span ctx fmt ~inside ~inside_do arg
      else
        (* Exactly one argument: pretty-print *)
        let field_name =
          (* Check if we need to extract the type as a tuple *)
          if is_tuple_struct then
            match backend () with
            | FStar | HOL4 | Coq -> FieldId.to_string proj.field_id
            | Lean ->
                (* Tuples in Lean are syntax sugar for nested products/pairs,
                   so we need to map the field id accordingly.

                   We give two possibilities:
                   - either we use the custom syntax [.#i], like in: [(0, 1).#1]
                   - or we introduce nested projections which use the field
                     projectors [.1] and [.2], like in: [(0, 1).2.1]

                     This necessary in some situations, for instance if we have
                     in Rust:
                     {[
                       struct Tuple(u32, (u32, u32));
                     ]}

                     The issue comes from the fact that in Lean [A * B * C] and [A * (B *
                     C)] are the same type.  As a result, in Rust, field 1 of [Tuple] is
                     the pair (an element of type [(u32, u32)]), however in Lean it would
                     be the first element of the pair (an element of type [u32]). If such
                     situations happen, we allow to force using the nested projectors by
                     providing the proper command line argument.  TODO: we can actually
                     check the type to determine exactly when we need to use nested
                     projectors and when we don't.

                     When using nested projectors, a field id i maps to:
                     - (.2)^i if i is the last element of the tuple
                     - (.2)^i.1 otherwise
                     where (.2)^i denotes .2 repeated i times.
                     For example, 3 maps to .2.2.2 if the tuple has 4 fields and
                     to .2.2.2.1 if it has more than 4 fields.
                     Note that the first "." is added below.
                *)
                let field_id = FieldId.to_int proj.field_id in
                if !use_nested_tuple_projectors then
                  (* Nested projection: "2.2.2..."  *)
                  if field_id = 0 then "1"
                  else
                    let twos_prefix =
                      String.concat "." (Collections.List.repeat field_id "2")
                    in
                    if field_id + 1 = Option.get num_fields then twos_prefix
                    else twos_prefix ^ ".1"
                else "#" ^ string_of_int field_id
          else ctx_get_field span proj.adt_id proj.field_id ctx
        in
        (* Open a box *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Extract the expression *)
        extract_texpr span ctx fmt ~inside:true ~inside_do arg;
        (* We allow to break where the "." appears (except Lean, it's a syntax error) *)
        if backend () <> Lean then F.pp_print_break fmt 0 0;
        F.pp_print_string fmt ".";
        (* If in Coq, the field projection has to be parenthesized *)
        (match backend () with
        | FStar | Lean | HOL4 -> F.pp_print_string fmt field_name
        | Coq -> F.pp_print_string fmt ("(" ^ field_name ^ ")"));
        (* Close the box *)
        F.pp_close_box fmt ()
  | arg :: args ->
      (* Call extract_App again, but in such a way that the first argument is
       * isolated *)
      extract_App span ctx fmt ~inside ~inside_do
        ([%add_loc] mk_app span original_app arg)
        args out_ty
  | [] ->
      (* No argument: shouldn't happen *)
      [%admit_raise] span "Unreachable" fmt

and extract_scalar_val_projector (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) ~(inside : bool) (_ : integer_type) (args : texpr list)
    : unit =
  match args with
  | [ arg ] ->
      if inside then F.pp_print_string fmt "(";
      extract_texpr span ctx fmt ~inside:true ~inside_do:false arg;
      F.pp_print_string fmt ".val";
      if inside then F.pp_print_string fmt ")"
  | _ -> [%internal_error] span

and extract_Lambda (span : Meta.span) (ctx : extraction_ctx) (fmt : F.formatter)
    ~(inside : bool) (xl : tpat list) (e : texpr) : unit =
  (* Open a box for the abs expression *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Open parentheses *)
  if inside then F.pp_print_string fmt "(";
  (* Print the lambda - note that there should always be at least one variable *)
  [%sanity_check] span (xl <> []);
  F.pp_print_string fmt "fun";
  let with_type =
    match backend () with
    | Coq -> true
    | _ -> false
  in
  let ctx =
    List.fold_left
      (fun ctx x ->
        F.pp_print_space fmt ();
        extract_tpat span ctx fmt ~is_let:true ~inside:true ~with_type x)
      ctx xl
  in
  F.pp_print_space fmt ();
  if backend () = Lean || backend () = Coq then F.pp_print_string fmt "=>"
  else F.pp_print_string fmt "->";
  F.pp_print_space fmt ();
  (* Print the body *)
  extract_texpr span ctx fmt ~inside:false ~inside_do:false e;
  (* Close parentheses *)
  if inside then F.pp_print_string fmt ")";
  (* Close the box for the abs expr *)
  F.pp_close_box fmt ()

and extract_lets (span : Meta.span) (ctx : extraction_ctx) (fmt : F.formatter)
    ~(inside : bool) ~(inside_do : bool) (e : texpr) : unit =
  (* Destruct the lets.

     Note that in the case of HOL4, we stop destructing the lets if at some point
     the "kind" (monadic or non-monadic) of the lets changes.

     We do this because in HOL4 the parsing is not very powerful:
     if we mix monadic let-bindings and non monadic let-bindings, we have to
     wrap the let-bindings inside a [do ... od] whenever we need to extract
     a monadic let-binding non immediately inside a monadic let-binding.

     Ex.:
     {[
       do
         x <- ...;
         let y = f x in
         do
           z <- g y;
           ...
         od
       od
     ]}
  *)
  let lets, next_e =
    match backend () with
    | HOL4 -> raw_destruct_lets_no_interleave span e
    | FStar | Coq | Lean -> raw_destruct_lets e
  in
  (* Extract the let-bindings *)
  let extract_let (ctx : extraction_ctx) (monadic : bool) (lv : tpat)
      (re : texpr) : extraction_ctx =
    (* Open a box for the let-binding *)
    F.pp_open_hvbox fmt 0;
    F.pp_open_hvbox fmt ctx.indent_incr;
    let ctx, end_let =
      (* There are two cases:
         - do we use a notation like [x <-- y;]
         - do we use notation with let-bindings
         Note that both notations can be used for monadic let-bindings.
         For instance, in F*, you can write:
         {[
           let* x = y in // monadic
           ...
         ]}
         TODO: cleanup
      *)
      if monadic && (backend () = Coq || backend () = HOL4) then (
        (* Box for the let .. <- *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        let ctx = extract_tpat span ctx fmt ~is_let:true ~inside:false lv in
        F.pp_print_space fmt ();
        let arrow =
          match backend () with
          | Coq | HOL4 -> "<-"
          | FStar | Lean -> [%internal_error] span
        in
        F.pp_print_string fmt arrow;
        F.pp_close_box fmt ();
        F.pp_print_space fmt ();
        (* Box for the bound expression *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        extract_texpr span ctx fmt ~inside:false ~inside_do:true re;
        F.pp_print_string fmt ";";
        F.pp_close_box fmt ();
        (ctx, fun _ -> ()))
      else
        (* Check if we can ignore the [let] - it is possible for some backends,
           if the monadic expression evaluates to [()] *)
        let ignore_let =
          monadic && is_ignored_pat lv && ty_is_unit lv.ty && backend () = Lean
        in
        (* Print the [let] *)
        let ctx, end_let =
          if not ignore_let then (
            (* Box for the let .. <- *)
            F.pp_open_hovbox fmt ctx.indent_incr;
            if monadic then
              match backend () with
              | FStar ->
                  F.pp_print_string fmt "let*";
                  F.pp_print_space fmt ()
              | Coq | Lean ->
                  F.pp_print_string fmt "let";
                  F.pp_print_space fmt ()
              | HOL4 -> ()
            else (
              F.pp_print_string fmt "let";
              F.pp_print_space fmt ());
            let ctx = extract_tpat span ctx fmt ~is_let:true ~inside:false lv in
            F.pp_print_space fmt ();
            let eq =
              match backend () with
              | FStar -> "="
              | Coq -> ":="
              | Lean -> if monadic then "←" else ":="
              | HOL4 -> if monadic then "<-" else "="
            in
            F.pp_print_string fmt eq;
            F.pp_close_box fmt ();
            F.pp_print_space fmt ();
            (* Continuation to end the let-binding *)
            let end_let () =
              match backend () with
              | Lean ->
                  (* In Lean, (monadic) let-bindings don't require to end with anything *)
                  ()
              | Coq | FStar | HOL4 ->
                  F.pp_print_space fmt ();
                  F.pp_print_string fmt "in"
            in
            (ctx, end_let))
          else (ctx, fun _ -> ())
        in
        (* Print the bound expression. *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        let inside_do_rhs =
          match backend () with
          | Lean -> false
          | _ -> monadic
        in
        extract_texpr span ctx fmt ~inside:false ~inside_do:inside_do_rhs re;
        F.pp_close_box fmt ();
        (ctx, end_let)
    in
    (* Close the boxes for the let-binding *)
    F.pp_close_box fmt ();
    (* End the let-binding *)
    end_let ();
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Return *)
    ctx
  in
  (* Open parentheses *)
  if inside then F.pp_print_string fmt "(";
  (* Open a box for the whole expression.

     In the case of Lean, we use a vbox so that line breaks are inserted
     at the end of every let-binding: let-bindings are indeed not ended
     with an "in" keyword.
  *)
  if backend () = Lean then F.pp_open_vbox fmt 0 else F.pp_open_hvbox fmt 0;
  (* Open parentheses *)
  if inside && backend () <> Lean then F.pp_print_string fmt "(";
  (* If Lean and HOL4, we rely on monadic blocks, so we insert a do and open a new box
     immediately *)
  let wrap_in_do_od =
    lets_require_wrap_in_do span lets
    &&
    (* In Lean, we need to open a do block only if we are not already inside a do block *)
    match backend () with
    | Lean -> not inside_do
    | _ -> true
  in
  if wrap_in_do_od then (
    F.pp_print_string fmt "do";
    F.pp_print_space fmt ());
  let ctx =
    List.fold_left
      (fun ctx (monadic, lv, re) -> extract_let ctx monadic lv re)
      ctx lets
  in
  (* Open a box for the next expression *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print the next expression *)
  extract_texpr span ctx fmt ~inside:false
    ~inside_do:(wrap_in_do_od || inside_do)
    next_e;
  (* Close the box for the next expression *)
  F.pp_close_box fmt ();

  (* do-box (Lean and HOL4 only) *)
  if wrap_in_do_od then
    if backend () = HOL4 then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt "od");
  (* Close parentheses *)
  if inside && backend () <> Lean then F.pp_print_string fmt ")";
  (* Close the box for the whole expression *)
  F.pp_close_box fmt ();
  (* Close parentheses *)
  if inside then F.pp_print_string fmt ")"

and extract_Switch (span : Meta.span) (ctx : extraction_ctx) (fmt : F.formatter)
    ~(inside : bool) ~(inside_do : bool) (scrut : texpr) (body : switch_body) :
    unit =
  let _ = inside in
  (* Remark: we don't use the [inside] parameter because we extract matches in
     a conservative manner: we always make sure they are parenthesized/delimited
     with keywords such as [end] *)
  (* Open a box for the whole expression.

     In the case of Lean, we rely on indentation to delimit the end of the
     branches, and need to insert line breaks: we thus use a vbox.
  *)
  if backend () = Lean then F.pp_open_vbox fmt 0 else F.pp_open_hvbox fmt 0;
  (* Extract the switch *)
  (match body with
  | If (e_then, e_else) ->
      (* Open a box for the [if e] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "if";
      if backend () = Lean && ctx.use_dep_ite then F.pp_print_string fmt " h:";
      F.pp_print_space fmt ();
      let scrut_inside = PureUtils.texpr_requires_parentheses span scrut in
      extract_texpr span ctx fmt ~inside:scrut_inside ~inside_do:false scrut;
      (* Close the box for the [if e] *)
      F.pp_close_box fmt ();

      (* Extract the branches *)
      let extract_branch (is_then : bool) (e_branch : texpr) : unit =
        F.pp_print_space fmt ();
        (* Open a box for the then/else+branch *)
        F.pp_open_hvbox fmt ctx.indent_incr;
        (* Open a box for the then/else + space + opening parenthesis *)
        F.pp_open_hovbox fmt 0;
        let then_or_else = if is_then then "then" else "else" in
        F.pp_print_string fmt then_or_else;
        let parenth = PureUtils.texpr_requires_parentheses span e_branch in
        (* Open the parenthesized expression *)
        let print_space_after_parenth =
          if parenth then (
            match backend () with
            | FStar ->
                F.pp_print_space fmt ();
                F.pp_print_string fmt "begin";
                F.pp_print_space fmt
            | Coq | Lean | HOL4 ->
                F.pp_print_space fmt ();
                F.pp_print_string fmt "(";
                F.pp_print_cut fmt)
          else F.pp_print_space fmt
        in
        (* Close the box for the then/else + space + opening parenthesis *)
        F.pp_close_box fmt ();
        print_space_after_parenth ();
        (* Open a box for the branch *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the branch expression *)
        extract_texpr span ctx fmt ~inside:false ~inside_do e_branch;
        (* Close the box for the branch *)
        F.pp_close_box fmt ();
        (* Close the parenthesized expression *)
        (if parenth then
           match backend () with
           | FStar ->
               F.pp_print_space fmt ();
               F.pp_print_string fmt "end"
           | Coq | Lean | HOL4 -> F.pp_print_string fmt ")");
        (* Close the box for the then/else+branch *)
        F.pp_close_box fmt ()
      in

      extract_branch true e_then;
      extract_branch false e_else
  | Match branches -> (
      (* Open a box for the [match ... with] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the [match ... with] *)
      let match_begin =
        match backend () with
        | FStar -> "begin match"
        | Coq -> "match"
        | Lean -> if ctx.use_dep_ite then "match h:" else "match"
        | HOL4 ->
            (* We're being extra safe in the case of HOL4 *)
            "(case"
      in
      F.pp_print_string fmt match_begin;
      F.pp_print_space fmt ();
      let scrut_inside = PureUtils.texpr_requires_parentheses span scrut in
      extract_texpr span ctx fmt ~inside:scrut_inside ~inside_do:false scrut;
      F.pp_print_space fmt ();
      let match_scrut_end =
        match backend () with
        | FStar | Coq | Lean -> "with"
        | HOL4 -> "of"
      in
      F.pp_print_string fmt match_scrut_end;
      (* Close the box for the [match ... with] *)
      F.pp_close_box fmt ();

      (* Extract the branches *)
      let extract_branch (br : match_branch) : unit =
        F.pp_print_space fmt ();
        (* Open a box for the pattern+branch *)
        F.pp_open_hvbox fmt ctx.indent_incr;
        (* Open a box for the pattern *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the pattern *)
        F.pp_print_string fmt "|";
        F.pp_print_space fmt ();
        let ctx =
          extract_tpat span ctx fmt ~is_let:false ~inside:false br.pat
        in
        F.pp_print_space fmt ();
        let arrow =
          match backend () with
          | FStar -> "->"
          | Coq | Lean | HOL4 -> "=>"
        in
        F.pp_print_string fmt arrow;
        (* Close the box for the pattern *)
        F.pp_close_box fmt ();
        F.pp_print_space fmt ();
        (* Open a box for the branch *)
        F.pp_open_hovbox fmt ctx.indent_incr;
        (* Print the branch itself *)
        extract_texpr span ctx fmt ~inside:false ~inside_do br.branch;
        (* Close the box for the branch *)
        F.pp_close_box fmt ();
        (* Close the box for the pattern+branch *)
        F.pp_close_box fmt ()
      in

      List.iter extract_branch branches;

      (* End the match *)
      match backend () with
      | Lean -> (* We rely on indentation in Lean *) ()
      | FStar | Coq ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt "end"
      | HOL4 -> F.pp_print_string fmt ")"));
  (* Close the box for the whole expression *)
  F.pp_close_box fmt ()

and extract_meta (span : Meta.span) (ctx : extraction_ctx) (fmt : F.formatter)
    ~(inside : bool) ~(inside_do : bool) (meta : emeta) (e : texpr) : unit =
  match meta with
  | TypeAnnot ->
      F.pp_print_string fmt "(";
      extract_texpr span ctx fmt ~inside:false ~inside_do e;
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":";
      F.pp_print_space fmt ();
      extract_ty span ctx fmt TypeDeclId.Set.empty ~inside:false e.ty;
      F.pp_print_string fmt ")"
  | _ -> extract_texpr span ctx fmt ~inside ~inside_do e

and extract_StructUpdate (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) ~(inside : bool) (supd : struct_update) (ty : ty) : unit
    =
  (* We can't update a subset of the fields in Coq (i.e., we can do
     [{| x:= 3; y := 4 |}], but there is no syntax for [{| s with x := 3 |}]) *)
  [%sanity_check] span (backend () <> Coq || supd.init = None);
  (* In the case of HOL4, records with no fields are not supported and are
     thus extracted to unit. We need to check that by looking up the definition *)
  let extract_as_unit =
    match (backend (), supd.struct_id) with
    | HOL4, TAdtId adt_id ->
        let d = TypeDeclId.Map.find adt_id ctx.trans_ctx.type_ctx.type_decls in
        d.kind = Struct []
    | _ -> false
  in
  if extract_as_unit then
    (* Remark: this is only valid for HOL4 (for instance the Coq unit value is [tt]) *)
    F.pp_print_string fmt "()"
  else
    (* There are two cases:
       - this is a regular struct
       - this is an array
    *)
    match supd.struct_id with
    | TAdtId _ ->
        F.pp_open_hvbox fmt 0;
        F.pp_open_hvbox fmt ctx.indent_incr;
        (* Inner/outer brackets: there are several syntaxes for the field updates.

           For instance, in F*:
           {[
             { x with f = ..., ... }
           ]}

           In HOL4:
           {[
             x with <| f = ..., ... |>
           ]}

           In the above examples:
           - in F*, the { } brackets are "outer" brackets
           - in HOL4, the <| |> brackets are "inner" brackets
        *)
        (* Outer brackets *)
        let olb, orb =
          match backend () with
          | Lean | FStar -> (Some "{", Some "}")
          | Coq -> (Some "{|", Some "|}")
          | HOL4 -> (None, None)
        in
        (* Inner brackets *)
        let ilb, irb =
          match backend () with
          | Lean | FStar | Coq -> (None, None)
          | HOL4 -> (Some "<|", Some "|>")
        in
        (* Helper *)
        let print_bracket (is_left : bool) b =
          match b with
          | Some b ->
              if not is_left then F.pp_print_space fmt ();
              F.pp_print_string fmt b;
              if is_left then F.pp_print_space fmt ()
          | None -> ()
        in
        print_bracket true olb;
        let need_paren = inside && backend () = HOL4 in
        if need_paren then F.pp_print_string fmt "(";
        F.pp_open_hvbox fmt ctx.indent_incr;
        if supd.init <> None then (
          let init = Option.get supd.init in
          extract_texpr span ctx fmt ~inside:false ~inside_do:false init;
          F.pp_print_space fmt ();
          F.pp_print_string fmt "with";
          F.pp_print_space fmt ());
        print_bracket true ilb;
        F.pp_open_hvbox fmt 0;
        let delimiter =
          match backend () with
          | Lean -> ","
          | Coq | FStar | HOL4 -> ";"
        in
        let assign =
          match backend () with
          | Coq | Lean | HOL4 -> ":="
          | FStar -> "="
        in
        Collections.List.iter_link
          (fun () ->
            F.pp_print_string fmt delimiter;
            F.pp_print_space fmt ())
          (fun (fid, fe) ->
            F.pp_open_hvbox fmt ctx.indent_incr;
            let f = ctx_get_field span supd.struct_id fid ctx in
            F.pp_print_string fmt f;
            (* Simplification: if the field value is a variable the same
               name as the field, we do not print it.

               Example: we generate [{ x }] instead of [{ x := x }].
            *)
            let has_same_name =
              match fe.e with
              | FVar vid ->
                  let var_name = ctx_get_var span vid ctx in
                  f = var_name
              | BVar _ -> [%internal_error] span
              | _ -> false
            in
            if not has_same_name then (
              F.pp_print_string fmt (" " ^ assign);
              F.pp_print_space fmt ();
              F.pp_open_hvbox fmt ctx.indent_incr;
              extract_texpr span ctx fmt ~inside:true ~inside_do:false fe;
              F.pp_close_box fmt ());
            F.pp_close_box fmt ())
          supd.updates;
        F.pp_close_box fmt ();
        print_bracket false irb;
        F.pp_close_box fmt ();
        if need_paren then F.pp_print_string fmt ")";
        F.pp_close_box fmt ();
        print_bracket false orb;
        F.pp_close_box fmt ()
    | TBuiltin TArray ->
        let ty =
          match ty with
          | TAdt (TBuiltin TArray, { types = [ ty ]; _ }) -> ty
          | _ -> [%internal_error] span
        in
        extract_array_or_slice span ctx fmt ~inside ~is_array:true ty
          (List.map snd supd.updates)
    | _ -> [%admit_raise] span "Unreachable" fmt

(** A small utility to print the parameters of a function signature.

    We return two contexts:
    - the context augmented with bindings for the generics
    - the context augmented with bindings for the generics *and* bindings for
      the input values

    We also return names for the type parameters, const generics, etc.

    TODO: do we really need the first one? It comes from the fact that when we
    print the input values for the decrease clause, we introduce bindings in the
    context (because we print patterns, not the variables). We should figure a
    cleaner way. *)
let extract_fun_parameters (space : bool ref) (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) :
    extraction_ctx * extraction_ctx * (explicit * string) list =
  (* First, add the associated types and constants if the function is a method
     in a trait declaration.

     About the order: we want to make sure the names are reserved for
     those (variable names might collide with them but it is ok, we will add
     suffixes to the variables).
  *)
  (* Add the type parameters - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  let ctx, type_params, cg_params, trait_clauses =
    ctx_add_generic_params def.item_meta.span def.item_meta.name Item
      def.signature.llbc_generics def.signature.generics ctx
  in
  (* Print the generics *)
  (* Open a box for the generics *)
  F.pp_open_hovbox fmt 0;
  let explicit = def.signature.explicit_info in
  (let space = Some space in
   extract_generic_params def.item_meta.span ctx fmt TypeDeclId.Set.empty ~space
     Item def.signature.generics (Some explicit) type_params cg_params
     trait_clauses);
  (* Close the box for the generics *)
  F.pp_close_box fmt ();
  (* The input parameters - note that doing this adds bindings to the context *)
  [%ldebug
    "Extracting the input parameters of: "
    ^ name_to_string ctx def.item_meta.name];
  let ctx_body =
    match def.body with
    | None -> ctx
    | Some body ->
        List.fold_left
          (fun ctx (lv : tpat) ->
            insert_req_space fmt space;
            (* Open a box for the input parameter *)
            F.pp_open_hovbox fmt 0;
            F.pp_print_string fmt "(";
            let ctx =
              extract_tpat def.item_meta.span ctx fmt ~is_let:true ~inside:false
                lv
            in
            F.pp_print_space fmt ();
            F.pp_print_string fmt ":";
            F.pp_print_space fmt ();
            extract_ty def.item_meta.span ctx fmt TypeDeclId.Set.empty
              ~inside:false lv.ty;
            F.pp_print_string fmt ")";
            (* Close the box for the input parameters *)
            F.pp_close_box fmt ();
            ctx)
          ctx body.inputs
  in
  let type_params = List.combine explicit.explicit_types type_params in
  let cg_params = List.combine explicit.explicit_const_generics cg_params in
  let trait_clauses = List.map (fun x -> (Explicit, x)) trait_clauses in
  (ctx, ctx_body, List.concat [ type_params; cg_params; trait_clauses ])

(** A small utility to print the types of the input parameters in the form:
    [u32 -> list u32 -> ...] (we don't print the return type of the function)

    This is used for opaque function declarations, in particular. *)
let extract_fun_input_parameters_types (span : span) (ctx : extraction_ctx)
    (fmt : F.formatter) (inputs : ty list) : unit =
  let extract_param (ty : ty) : unit =
    let inside = false in
    extract_ty span ctx fmt TypeDeclId.Set.empty ~inside ty;
    F.pp_print_space fmt ();
    extract_arrow fmt ();
    F.pp_print_space fmt ()
  in
  List.iter extract_param inputs

let assert_backend_supports_decreases_clauses (span : Meta.span) =
  match backend () with
  | FStar | Lean -> ()
  | _ ->
      [%craise] span
        "Decreases clauses are only supported for the Lean and F* backends"

(** Extract a decreases clause function template body.

    For F* only.

    In order to help the user, we can generate a template for the functions
    required by the decreases clauses for. We simply generate definitions of the
    following form in a separate file:
    {[
      let f_decrease (t : Type0) (x : t) : nat = admit()
    ]}

    Where the translated functions for [f] look like this:
    {[
      let f_fwd (t : Type0) (x : t) : Tot ... (decreases (f_decrease t x)) = ...
    ]} *)
let extract_template_fstar_decreases_clause (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : unit =
  [%cassert] def.item_meta.span
    (backend () = FStar)
    "The generation of template decrease clauses is only supported for the F* \
     backend";
  (* Retrieve the function name *)
  let def_name =
    ctx_get_termination_measure def.item_meta.span def.def_id def.loop_id ctx
  in
  (* Open the binders - it is easier to only manipulate variables which have unique ids *)
  let _, fresh_fvar_id = FVarId.fresh_stateful_generator () in
  let def =
    {
      def with
      body =
        Option.map
          (fun b -> snd (open_all_fun_body fresh_fvar_id def.item_meta.span b))
          def.body;
    }
  in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  (let name =
     if !extract_external_name_patterns && not def.item_meta.is_local then
       Some def.item_meta.name
     else None
   in
   extract_comment_with_span ctx fmt
     [ "[" ^ name_to_string ctx def.item_meta.name ^ "]: decreases clause" ]
     name def.item_meta.span);
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Add the [unfold] keyword *)
  F.pp_print_string fmt "unfold";
  F.pp_print_space fmt ();
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  F.pp_print_string fmt ("let " ^ def_name);
  F.pp_print_space fmt ();
  (* Extract the parameters *)
  let space = ref true in
  let _, _, _ = extract_fun_parameters space ctx fmt def in
  insert_req_space fmt space;
  F.pp_print_string fmt ":";
  (* Print the signature *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt "nat";
  (* Print the "=" *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt "=";
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  F.pp_print_space fmt ();
  (* Print the "admit ()" *)
  F.pp_print_string fmt "admit ()";
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_close_box fmt ();
  (* Close the box for the whole definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Extract templates for the [termination_by] and [decreasing_by] clauses of a
    recursive function definition.

    For Lean only.

    We extract two commands. The first one is a regular definition for the
    termination measure (the value derived from the function arguments that
    decreases over function calls). The second one is a macro definition that
    defines a proof script (allowed to refer to function arguments) that proves
    termination. *)
let extract_template_lean_termination_and_decreasing (ctx : extraction_ctx)
    (fmt : F.formatter) (def : fun_decl) : unit =
  [%cassert] def.item_meta.span
    (backend () = Lean)
    "The generation of template termination and decreasing clauses is only \
     supported for the Lean backend";
  (*
   * Extract a template for the termination measure
   *)
  (* Open the binders - it is easier to only manipulate variables which have unique ids *)
  let _, fresh_fvar_id = FVarId.fresh_stateful_generator () in
  let def =
    {
      def with
      body =
        Option.map
          (fun b -> snd (open_all_fun_body fresh_fvar_id def.item_meta.span b))
          def.body;
    }
  in
  (* Retrieve the function name *)
  let def_name =
    ctx_get_termination_measure def.item_meta.span def.def_id def.loop_id ctx
  in
  let def_body = Option.get def.body in
  let span = def.item_meta.span in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  extract_comment_with_span ctx fmt
    [ "[" ^ name_to_string ctx def.item_meta.name ^ "]: termination measure" ]
    None def.item_meta.span;
  F.pp_print_space fmt ();
  (* Open a box for the definition, so that whenever possible it gets printed on
   * one line *)
  F.pp_open_hvbox fmt 0;
  (* Add the [unfold] keyword *)
  F.pp_print_string fmt "@[simp]";
  F.pp_print_space fmt ();
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  F.pp_print_string fmt ("def " ^ def_name);
  F.pp_print_space fmt ();
  (* Extract the parameters *)
  let space = ref true in
  let _, ctx_body, _ = extract_fun_parameters space ctx fmt def in
  (* Print the ":=" *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt ":=";
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  F.pp_print_space fmt ();
  (* Tuple of the arguments *)
  let vars = List.map ([%add_loc] as_pat_open_fvar_id span) def_body.inputs in

  if List.length vars = 1 then
    F.pp_print_string fmt
      (ctx_get_var def.item_meta.span (List.hd vars) ctx_body)
  else (
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt "(";
    Collections.List.iter_link
      (fun () ->
        F.pp_print_string fmt ",";
        F.pp_print_space fmt ())
      (fun v ->
        F.pp_print_string fmt (ctx_get_var def.item_meta.span v ctx_body))
      vars;
    F.pp_print_string fmt ")";
    F.pp_close_box fmt ());
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT = admit()" *)
  F.pp_close_box fmt ();
  (* Close the box for the whole definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0;

  (*
   * Extract a template for the decreases proof
   *)
  let def_name =
    ctx_get_decreases_proof def.item_meta.span def.def_id def.loop_id ctx
  in
  (* syntax <def_name> term ... term : tactic *)
  F.pp_print_break fmt 0 0;
  extract_comment_with_span ctx fmt
    [ "[" ^ name_to_string ctx def.item_meta.name ^ "]: decreases_by tactic" ]
    None def.item_meta.span;
  F.pp_print_space fmt ();
  F.pp_open_hvbox fmt 0;
  F.pp_print_string fmt "syntax \"";
  F.pp_print_string fmt def_name;
  F.pp_print_string fmt "\" term+ : tactic";
  F.pp_print_break fmt 0 0;
  (* macro_rules | `(tactic| fact_termination_proof $x) => `(tactic| ( *)
  F.pp_print_string fmt "macro_rules";
  F.pp_print_space fmt ();
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt "| `(tactic| ";
  F.pp_print_string fmt def_name;
  List.iter
    (fun v ->
      F.pp_print_space fmt ();
      F.pp_print_string fmt "$";
      F.pp_print_string fmt (ctx_get_var def.item_meta.span v ctx_body))
    vars;
  F.pp_print_string fmt ") =>";
  F.pp_close_box fmt ();
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt "`(tactic| sorry)";
  F.pp_close_box fmt ();
  F.pp_close_box fmt ();
  F.pp_close_box fmt ();
  F.pp_print_break fmt 0 0

let extract_fun_comment (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  let comment_pre = "[" ^ name_to_string ctx def.item_meta.name ^ "]:" in
  let comment =
    let loop_comment =
      match def.loop_id with
      | None -> ""
      | Some (id, false) -> " loop " ^ LoopId.to_string id ^ ":"
      | Some (id, true) -> " loop body " ^ LoopId.to_string id ^ ":"
    in
    [ comment_pre ^ loop_comment ]
  in
  let name =
    if !extract_external_name_patterns && not def.item_meta.is_local then
      Some def.item_meta.name
    else None
  in
  extract_comment_with_span ctx fmt comment name
    ~public:def.item_meta.attr_info.public def.item_meta.span

(** Extract a function declaration.

    This function is for all function declarations and all backends **at the
    exception** of opaque (builtin/declared) functions for HOL4.

    See {!extract_fun_decl}. *)
let extract_fun_decl_gen (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (has_decreases_clause : bool) (def : fun_decl) : unit =
  [%sanity_check] def.item_meta.span (not def.is_global_decl_body);
  (* Retrieve the function name *)
  let def_name =
    ctx_get_local_function def.item_meta.span def.def_id def.loop_id ctx
  in
  [%ltrace "Extracting function: " ^ def_name];
  (* Open the binders - it is easier to only manipulate variables which have unique ids *)
  let _, fresh_fvar_id = FVarId.fresh_stateful_generator () in
  let def =
    {
      def with
      body =
        Option.map
          (fun b -> snd (open_all_fun_body fresh_fvar_id def.item_meta.span b))
          def.body;
    }
  in
  let span = def.item_meta.span in
  (* Add a break before *)
  if backend () <> HOL4 || not (decl_is_first_from_group kind) then
    F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted definition to its original rust definition *)
  extract_fun_comment ctx fmt def;
  F.pp_print_space fmt ();
  (* Open two boxes for the definition, so that whenever possible it gets printed on
   * one line and indents are correct *)
  F.pp_open_hvbox fmt 0;
  (* Extract the attributes *)
  let rust_attributes =
    if backend () = Lean then
      match def.loop_id with
      | None -> []
      | Some (_, false) -> [ "rust_loop" ]
      | Some (_, true) -> [ "rust_loop_body" ]
    else []
  in
  let reduc_attribute =
    if def.backend_attributes.reducible && backend () = Lean then
      [ "reducible" ]
    else []
  in
  let attributes = rust_attributes @ reduc_attribute in
  extract_attributes span ctx fmt def.item_meta.name None attributes "rust_fun"
    []
    ~is_external:(not def.item_meta.is_local);
  F.pp_open_vbox fmt ctx.indent_incr;
  (* For HOL4: we may need to put parentheses around the definition *)
  let parenthesize = backend () = HOL4 && decl_is_not_last_from_group kind in
  if parenthesize then F.pp_print_string fmt "(";
  (* Open a box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* > "let FUN_NAME" *)
  let is_opaque = Option.is_none def.body in
  (* If in Coq and the declaration is opaque, it must have the shape:
     [Axiom Ident : forall (T0 ... Tn : Type), ... -> ... -> ...].

     The boolean [is_opaque_coq] is used to detect this case.
  *)
  let is_opaque_coq = backend () = Coq && is_opaque in
  let use_forall =
    is_opaque_coq && def.signature.generics <> empty_generic_params
  in
  (* Print the qualifier ("assume", etc.). *)
  let qualif = fun_decl_kind_to_qualif kind in
  (match qualif with
  | Some qualif ->
      F.pp_print_string fmt qualif;
      F.pp_print_space fmt ()
  | None -> ());
  F.pp_print_string fmt def_name;
  F.pp_print_space fmt ();
  if use_forall then (
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    F.pp_print_string fmt "forall");
  (* Open a box for "(PARAMS) : EFFECT =" *)
  F.pp_open_hvbox fmt 0;
  (* Open a box for "(PARAMS) :" *)
  F.pp_open_hovbox fmt 0;
  let space = ref true in
  let ctx, ctx_body, all_params = extract_fun_parameters space ctx fmt def in
  (* Print the return type - note that we have to be careful when
   * printing the input values for the decrease clause, because
   * it introduces bindings in the context... We thus "forget"
   * the bindings we introduced above.
   * TODO: figure out a cleaner way *)
  let _ =
    if use_forall then F.pp_print_string fmt ","
    else (
      insert_req_space fmt space;
      F.pp_print_string fmt ":");
    (* Close the box for "(PARAMS) :" *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Open a box for the EFFECT *)
    F.pp_open_hvbox fmt 0;
    (* Open a box for the return type *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    (* Print the return type *)
    (* For opaque definitions, as we don't have named parameters under the hand,
     * we don't print parameters in the form [(x : a) (y : b) ...] above,
     * but wait until here to print the types: [a -> b -> ...]. *)
    if is_opaque then
      extract_fun_input_parameters_types def.item_meta.span ctx fmt
        def.signature.inputs;
    (* [Tot] *)
    if has_decreases_clause then (
      assert_backend_supports_decreases_clauses def.item_meta.span;
      if backend () = FStar then (
        F.pp_print_string fmt "Tot";
        F.pp_print_space fmt ()));
    extract_ty def.item_meta.span ctx fmt TypeDeclId.Set.empty
      ~inside:has_decreases_clause def.signature.output;
    (* Close the box for the return type *)
    F.pp_close_box fmt ();
    (* Print the decrease clause - rk.: a function with a decreases clause
     * is necessarily a transparent function *)
    if has_decreases_clause && backend () = FStar then (
      assert_backend_supports_decreases_clauses def.item_meta.span;
      F.pp_print_space fmt ();
      (* Open a box for the decreases clause *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* *)
      F.pp_print_string fmt "(decreases (";
      F.pp_print_cut fmt ();
      (* Open a box for the decreases term *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* The name of the decrease clause *)
      let decr_name =
        ctx_get_termination_measure def.item_meta.span def.def_id def.loop_id
          ctx
      in
      F.pp_print_string fmt decr_name;
      (* Print the generic parameters - TODO: we do this many
         times, we should have a helper to factor it out *)
      List.iter
        (fun (name : string) ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt name)
        (List.filter_map
           (fun (e, x) -> if e = Implicit then None else Some x)
           all_params);
      (* Print the input values: we have to be careful here to print
       * only the input values which are in common with the *forward*
       * function (the additional input values "given back" to the
       * backward functions have no influence on termination: we thus
       * share the decrease clauses between the forward and the backward
       * functions - we also ignore the additional state received by the
       * backward function, if there is one).
       *)
      let inputs_lvs = (Option.get def.body).inputs in
      (* TODO: we should probably print the input variables, not the typed
         patterns *)
      let _ =
        List.fold_left
          (fun ctx (lv : tpat) ->
            F.pp_print_space fmt ();
            let ctx =
              extract_tpat def.item_meta.span ctx fmt ~is_let:true ~inside:false
                lv
            in
            ctx)
          ctx inputs_lvs
      in
      F.pp_print_string fmt "))";
      (* Close the box for the decreases term *)
      F.pp_close_box fmt ();
      (* Close the box for the decreases clause *)
      F.pp_close_box fmt ());
    (* Close the box for the EFFECT *)
    F.pp_close_box fmt ()
  in
  (* Print the "=" *)
  if not is_opaque then (
    F.pp_print_space fmt ();
    let eq =
      match backend () with
      | FStar | HOL4 -> "="
      | Coq -> ":="
      | Lean -> ":= do"
    in
    F.pp_print_string fmt eq);
  (* Close the box for "(PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  (* Close the box for "let FUN_NAME (PARAMS) : EFFECT =" *)
  F.pp_close_box fmt ();
  if not is_opaque then (
    F.pp_print_space fmt ();
    (* Open a box for the body *)
    F.pp_open_hvbox fmt 0;
    (* Extract the body *)
    let _ =
      F.pp_open_hovbox fmt ctx.indent_incr;
      let _ =
        extract_texpr def.item_meta.span ctx_body fmt ~inside:false
          ~inside_do:true (Option.get def.body).body
      in
      F.pp_close_box fmt ()
    in
    (* Close the box for the body *)
    F.pp_close_box fmt ());
  (* Close the inner box for the definition *)
  F.pp_close_box fmt ();
  (* Termination clause and proof for Lean *)
  if has_decreases_clause && backend () = Lean then (
    let def_body = Option.get def.body in
    let vars = List.map ([%add_loc] as_pat_open_fvar_id span) def_body.inputs in

    (* termination_by *)
    let terminates_name =
      ctx_get_termination_measure def.item_meta.span def.def_id def.loop_id ctx
    in
    F.pp_print_break fmt 0 0;
    (* Open a box for the whole [termination_by CALL => DECREASES] *)
    F.pp_open_hvbox fmt ctx.indent_incr;
    (* Open a box for {termination_by CALL =>} *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt "termination_by";
    F.pp_print_space fmt ();
    F.pp_print_string fmt def_name;
    List.iter
      (fun v ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt (ctx_get_var def.item_meta.span v ctx_body))
      vars;
    F.pp_print_space fmt ();
    F.pp_print_string fmt "=>";
    (* Close the box for [termination_by CALL =>] *)
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    (* Open the box for [DECREASES] *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt terminates_name;
    (* Print the generic params - TODO: factor out *)
    List.iter
      (fun (name : string) ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt name)
      (List.filter_map
         (fun (e, x) -> if e = Implicit then None else Some x)
         all_params);
    (* Print the variables *)
    List.iter
      (fun v ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt (ctx_get_var def.item_meta.span v ctx_body))
      vars;
    (* Close the box for [DECREASES] *)
    F.pp_close_box fmt ();
    (* Close the box for the whole [termination_by CALL => DECREASES] *)
    F.pp_close_box fmt ();

    F.pp_print_break fmt 0 0;
    (* Open a box for the [decreasing by ...] *)
    F.pp_open_hvbox fmt ctx.indent_incr;
    let decreases_name =
      ctx_get_decreases_proof def.item_meta.span def.def_id def.loop_id ctx
    in
    F.pp_print_string fmt "decreasing_by";
    F.pp_print_space fmt ();
    F.pp_open_hvbox fmt ctx.indent_incr;
    F.pp_print_string fmt decreases_name;
    List.iter
      (fun v ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt (ctx_get_var def.item_meta.span v ctx_body))
      vars;
    F.pp_close_box fmt ();
    (* Close the box for the [decreasing by ...] *)
    F.pp_close_box fmt ());
  (* Close the parentheses *)
  if parenthesize then F.pp_print_string fmt ")";
  (* Add the definition end delimiter *)
  if backend () = HOL4 && decl_is_not_last_from_group kind then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt "/\\")
  else if backend () = Coq && decl_is_last_from_group kind then (
    (* This is actually an end of group delimiter. For aesthetic reasons
       we print it here instead of in {!end_fun_decl_group}. *)
    F.pp_print_cut fmt ();
    F.pp_print_string fmt ".");
  (* Add the post-qualifier (i.e., the [partial_fixpoint] keyword if necessary) *)
  Option.iter
    (fun qualif ->
      F.pp_print_space fmt ();
      F.pp_print_string fmt qualif)
    (fun_decl_kind_to_post_qualif kind);
  (* Close the outer box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  if backend () <> HOL4 || decl_is_not_last_from_group kind then
    F.pp_print_break fmt 0 0

(** Extract an opaque function declaration to HOL4.

    Remark (SH): having to treat this specific case separately is very annoying,
    but I could not find a better way. *)
let extract_fun_decl_hol4_opaque (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  (* Retrieve the definition name *)
  let def_name =
    ctx_get_local_function def.item_meta.span def.def_id def.loop_id ctx
  in
  (* Open the binders - it is easier to only manipulate variables which have unique ids *)
  let _, fresh_fvar_id = FVarId.fresh_stateful_generator () in
  let def =
    {
      def with
      body =
        Option.map
          (fun b -> snd (open_all_fun_body fresh_fvar_id def.item_meta.span b))
          def.body;
    }
  in
  [%cassert] def.item_meta.span
    (def.signature.generics.const_generics = [])
    "Constant generics are not supported yet when generating code for HOL4";
  (* Add the type/const gen parameters - note that we need those bindings
     only for the generation of the type (they are not top-level) *)
  let ctx, _, _, _ =
    ctx_add_generic_params def.item_meta.span def.item_meta.name Item
      def.signature.llbc_generics def.signature.generics ctx
  in
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0;
  (* Open a box for the whole definition *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* Print a comment to link the extracted definition to its original rust definition *)
  extract_fun_comment ctx fmt def;
  (* Generate: `val _ = new_constant ("...",` *)
  F.pp_print_string fmt ("val _ = new_constant (\"" ^ def_name ^ "\",");
  F.pp_print_space fmt ();
  (* Open a box for the type *)
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt "“:";
  (* Generate the type *)
  extract_fun_input_parameters_types def.item_meta.span ctx fmt
    def.signature.inputs;
  extract_ty def.item_meta.span ctx fmt TypeDeclId.Set.empty ~inside:false
    def.signature.output;
  (* Close the box for the type *)
  F.pp_print_string fmt "”";
  F.pp_close_box fmt ();
  (* Close the parenthesis opened for the inputs of `new_constant` *)
  F.pp_print_string fmt ")";
  (* Close the box for the definition *)
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Extract a function declaration.

    Note that all the names used for extraction should already have been
    registered.

    We take the definition of the forward translation as parameter (which is
    equal to the definition to extract, if we extract a forward function)
    because it is useful for the decrease clause.

    This function should be inserted between calls to {!start_fun_decl_group}
    and {!end_fun_decl_group}. *)
let extract_fun_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (has_decreases_clause : bool) (def : fun_decl) : unit =
  [%sanity_check] def.item_meta.span (not def.is_global_decl_body);
  (* We treat HOL4 opaque functions in a specific manner *)
  if backend () = HOL4 && Option.is_none def.body then
    extract_fun_decl_hol4_opaque ctx fmt def
  else extract_fun_decl_gen ctx fmt kind has_decreases_clause def

(** Extract a global declaration body of the shape "QUALIF NAME : TYPE = BODY"
    with a custom body extractor.

    We introduce this helper because every (non opaque) global declaration gets
    extracted to two declarations, and we can actually factor out the generation
    of those declarations. See {!extract_global_decl} for more explanations. *)
let extract_global_decl_body_gen (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (decl : global_decl) (kind : decl_kind)
    ~(irreducible : bool) ~(with_do : bool) (name : string)
    (generics : generic_params) (explicit : explicit_info)
    (type_params : string list) (cg_params : string list)
    (trait_clauses : string list) (ty : ty)
    (extract_body : (F.formatter -> unit) Option.t) : unit =
  let is_opaque = Option.is_none extract_body in

  (* HOL4: Definition wrapper *)
  if backend () = HOL4 then (
    (* Open a vertical box: we *must* break lines *)
    F.pp_open_vbox fmt 0;
    F.pp_print_string fmt ("Definition " ^ name ^ "_def:");
    F.pp_print_space fmt ();
    F.pp_open_vbox fmt ctx.indent_incr;
    F.pp_print_string fmt (String.make ctx.indent_incr ' '));

  (* Open the definition boxes (depth=0) *)
  F.pp_open_hvbox fmt 0;

  (* For lean: add the irreducible attribute *)
  [%sanity_check] span (backend () = Lean || not irreducible);
  let attributes =
    if is_opaque then []
    else if backend () = Lean then
      if irreducible then [ "global_simps"; "irreducible" ]
      else [ "global_simps" ]
    else []
  in
  let trait_default =
    match decl.src with
    | TraitDeclItem (_, _, true) -> [ "trait_default" ]
    | _ -> []
  in
  let attributes = attributes @ trait_default in
  extract_attributes span ctx fmt decl.item_meta.name None attributes
    "rust_const" []
    ~is_external:(not decl.item_meta.is_local);

  (* Second definition box *)
  F.pp_open_hvbox fmt ctx.indent_incr;

  (* Open "QUALIF NAME PARAMS : TYPE =" box (depth=1) *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print "QUALIF NAME PARAMS " *)
  (match fun_decl_kind_to_qualif kind with
  | Some qualif ->
      F.pp_print_string fmt qualif;
      F.pp_print_space fmt ()
  | None -> ());
  F.pp_print_string fmt name;
  F.pp_print_space fmt ();

  (* Extract the generic parameters *)
  let space = ref true in
  extract_generic_params span ctx fmt TypeDeclId.Set.empty ~space:(Some space)
    Item generics (Some explicit) type_params cg_params trait_clauses;
  if not !space then F.pp_print_space fmt ();

  (* Open ": TYPE =" box (depth=2) *)
  F.pp_open_hvbox fmt 0;
  (* Print ": " *)
  F.pp_print_string fmt ":";
  F.pp_print_space fmt ();

  (* Open "TYPE" box (depth=3) *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Print "TYPE" *)
  extract_ty span ctx fmt TypeDeclId.Set.empty ~inside:false ty;
  (* Close "TYPE" box (depth=3) *)
  F.pp_close_box fmt ();

  if not is_opaque then (
    (* Print " =" *)
    F.pp_print_space fmt ();
    let eq =
      match backend () with
      | FStar | HOL4 -> "="
      | Coq -> ":="
      | Lean -> if with_do then ":= do" else ":="
    in
    F.pp_print_string fmt eq);
  (* Close ": TYPE =" box (depth=2) *)
  F.pp_close_box fmt ();
  (* Close "QUALIF NAME : TYPE =" box (depth=1) *)
  F.pp_close_box fmt ();

  if not is_opaque then (
    F.pp_print_space fmt ();
    (* Open "BODY" box (depth=1) *)
    F.pp_open_hvbox fmt 0;
    (* Print "BODY" *)
    F.pp_open_hovbox fmt ctx.indent_incr;
    (Option.get extract_body) fmt;
    F.pp_close_box fmt ();
    (* Close "BODY" box (depth=1) *)
    F.pp_close_box fmt ());

  (* Close the inner definition box (depth=0) *)
  F.pp_close_box fmt ();

  (* Coq: add a "." *)
  if backend () = Coq then (
    F.pp_print_cut fmt ();
    F.pp_print_string fmt ".");

  (* Close the outer definition box (depth=0) *)
  F.pp_close_box fmt ();

  (* HOL4: Definition wrapper *)
  if backend () = HOL4 then (
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    F.pp_print_string fmt "End";
    F.pp_close_box fmt ())

(** Extract an opaque global declaration for HOL4.

    Remark (SH): having to treat this specific case separately is very annoying,
    but I could not find a better way. *)
let extract_global_decl_hol4_opaque (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (name : string) (generics : generic_params) (ty : ty) :
    unit =
  (* TODO: non-empty generics *)
  assert (generics = empty_generic_params);
  (* Open the definition boxe (depth=0) *)
  F.pp_open_hvbox fmt ctx.indent_incr;
  (* [val ..._def = new_constant ("...",] *)
  F.pp_open_hovbox fmt 0;
  F.pp_print_string fmt
    ("val " ^ name ^ "_def = new_constant (\"" ^ name ^ "\", ");
  F.pp_close_box fmt ();
  (* Print the type *)
  F.pp_open_hovbox fmt 0;
  extract_ty span ctx fmt TypeDeclId.Set.empty ~inside:false ty;
  (* Close the definition *)
  F.pp_print_string fmt ")";
  F.pp_close_box fmt ();
  (* Close the definition box *)
  F.pp_close_box fmt ();
  (* Add a line *)
  F.pp_print_space fmt ()

(** Extract a global declaration.

    We generate the body which *computes* the global value separately from the
    value declaration itself.

    For example in Rust, [static X: u32 = 3;]

    will be translated to the following F*: [let x_body : result u32 = Return 3]
    (* this has type [result u32] *) [let x_c : u32 = eval_global x_body] (*
    this has type [u32] (no [result]!) *)

    This function generates the two declarations.

    Remark: because global declaration groups are always singletons (i.e., there
    are no groups of mutually recursive global declarations), this function
    doesn't need to be called between calls to functions of the shape
    [{start,end}_gloabl_decl_group], contrary to {!extract_type_decl} and
    {!extract_fun_decl}. *)
let extract_global_decl_aux (ctx : extraction_ctx) (fmt : F.formatter)
    (global : global_decl) (body : fun_decl) (interface : bool) : unit =
  let span = body.item_meta.span in
  [%sanity_check] span body.is_global_decl_body;
  [%sanity_check] span (body.signature.inputs = []);
  (* Open the binders - it is easier to only manipulate variables which have unique ids *)
  let _, fresh_fvar_id = FVarId.fresh_stateful_generator () in
  let body =
    {
      body with
      body =
        Option.map
          (fun b -> snd (open_all_fun_body fresh_fvar_id body.item_meta.span b))
          body.body;
    }
  in
  (* Add a break then the name of the corresponding LLBC declaration *)
  F.pp_print_break fmt 0 0;
  let name =
    if !extract_external_name_patterns && not global.item_meta.is_local then
      Some global.item_meta.name
    else None
  in
  extract_comment_with_span ctx fmt
    [ "[" ^ name_to_string ctx global.item_meta.name ^ "]" ]
    name ~public:global.item_meta.attr_info.public global.span;
  F.pp_print_space fmt ();

  let decl_name = ctx_get_global span global.def_id ctx in
  let output_ty = body.signature.output in
  (* Add the type parameters *)
  let ctx, type_params, cg_params, trait_clauses =
    ctx_add_generic_params span global.item_meta.name Item global.llbc_generics
      global.generics ctx
  in
  match body.body with
  | None ->
      (* No body: only generate a [val x_c : u32] declaration *)
      let kind = if interface then Declared else Builtin in
      if backend () = HOL4 then
        extract_global_decl_hol4_opaque span ctx fmt decl_name global.generics
          output_ty
      else (
        extract_global_decl_body_gen span ctx fmt global kind ~irreducible:false
          ~with_do:false decl_name global.generics global.explicit_info
          type_params cg_params trait_clauses output_ty None;
        F.pp_print_space fmt ())
  | Some body ->
      (* There is a body *)
      let with_do =
        match body.body.e with
        | Let (true, _, _, _) -> true
        | _ -> false
      in
      extract_global_decl_body_gen span ctx fmt global SingleNonRec
        ~irreducible:(backend () = Lean)
        ~with_do decl_name global.generics global.explicit_info type_params
        cg_params trait_clauses output_ty
        (Some
           (fun fmt ->
             extract_texpr span ctx fmt ~inside:false ~inside_do:with_do
               body.body));
      (* Add a break to insert lines between declarations *)
      F.pp_print_break fmt 0 0

let extract_global_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (global : global_decl option) (body : fun_decl) (interface : bool) : unit =
  match global with
  | Some global -> extract_global_decl_aux ctx fmt global body interface
  | None -> ()

(** Similar to {!extract_trait_decl_register_names} *)
let extract_trait_decl_register_parent_clause_names (ctx : extraction_ctx)
    (trait_decl : trait_decl)
    (builtin_info : Pure.builtin_trait_decl_info option) : extraction_ctx =
  (* Compute the clause names *)
  let clause_names =
    match builtin_info with
    | None ->
        List.map
          (fun (c : trait_param) ->
            let name = ctx_compute_trait_parent_clause_name ctx trait_decl c in
            (* Add a prefix if necessary *)
            let name =
              if !record_fields_short_names then name
              else ctx_compute_trait_decl_name ctx trait_decl ^ name
            in
            (c.clause_id, name))
          trait_decl.parent_clauses
    | Some info ->
        [%cassert] trait_decl.item_meta.span
          (List.length trait_decl.parent_clauses
          = List.length info.parent_clauses)
          ("Invalid builtin information for trait decl: "
          ^ name_to_string ctx trait_decl.item_meta.name
          ^ "; expected "
          ^ string_of_int (List.length trait_decl.parent_clauses)
          ^ " parent clauses, found "
          ^ string_of_int (List.length info.parent_clauses));
        List.map
          (fun (c, name) -> (c.clause_id, name))
          (List.combine trait_decl.parent_clauses info.parent_clauses)
  in
  (* Register the names *)
  List.fold_left
    (fun ctx (cid, cname) ->
      ctx_add trait_decl.item_meta.span
        (TraitParentClauseId (trait_decl.def_id, cid))
        cname ctx)
    ctx clause_names

(** Similar to {!extract_trait_decl_register_names} *)
let extract_trait_decl_register_constant_names (ctx : extraction_ctx)
    (trait_decl : trait_decl)
    (builtin_info : Pure.builtin_trait_decl_info option) : extraction_ctx =
  let consts = trait_decl.consts in
  (* Compute the names *)
  let constant_names =
    match builtin_info with
    | None ->
        List.map
          (fun (const_id, item_name, _) ->
            let name = ctx_compute_trait_const_name ctx trait_decl item_name in
            (* Add a prefix if necessary *)
            let name =
              if !record_fields_short_names then name
              else ctx_compute_trait_decl_name ctx trait_decl ^ name
            in
            (const_id, name))
          consts
    | Some info ->
        let const_map = StringMap.of_list info.consts in
        List.map
          (fun (const_id, item_name, _) ->
            (const_id, StringMap.find item_name const_map))
          consts
  in
  (* Register the names *)
  List.fold_left
    (fun ctx (const_id, name) ->
      ctx_add trait_decl.item_meta.span
        (TraitConstId (trait_decl.def_id, const_id))
        name ctx)
    ctx constant_names

(** Similar to {!extract_trait_decl_register_names} *)
let extract_trait_decl_type_names (ctx : extraction_ctx)
    (trait_decl : trait_decl)
    (builtin_info : Pure.builtin_trait_decl_info option) : extraction_ctx =
  let types = trait_decl.types in
  (* Compute the names *)
  let type_names =
    match builtin_info with
    | None ->
        let compute_type_name (item_name : string) : string =
          let type_name =
            ctx_compute_trait_type_name ctx trait_decl item_name
          in
          if !record_fields_short_names then type_name
          else ctx_compute_trait_decl_name ctx trait_decl ^ type_name
        in
        List.map
          (fun (type_id, item_name) ->
            (* Type name *)
            let type_name = compute_type_name item_name in
            (type_id, type_name))
          types
    | Some info ->
        let type_map = StringMap.of_list info.types in
        List.map
          (fun (type_id, item_name) ->
            match StringMap.find_opt item_name type_map with
            | Some type_name -> (type_id, type_name)
            | None ->
                [%craise] trait_decl.item_meta.span
                  ("Unexpected error: could not find the information for the \
                    trait associated type '" ^ item_name
                 ^ "' for trait declaration '"
                  ^ name_to_string ctx trait_decl.item_meta.name
                  ^ "'"))
          types
  in
  (* Register the names *)
  List.fold_left
    (fun ctx (type_id, type_name) ->
      ctx_add trait_decl.item_meta.span
        (TraitTypeId (trait_decl.def_id, type_id))
        type_name ctx)
    ctx type_names

(** Similar to {!extract_trait_decl_register_names} *)
let extract_trait_decl_method_names (ctx : extraction_ctx)
    (trait_decl : trait_decl) (trait_decl_name : string)
    (builtin_info : Pure.builtin_trait_decl_info option) : extraction_ctx =
  [%ltrace trait_decl.name];
  let methods = trait_decl.methods in
  (* Small helper *)
  let compute_item_name (item_name : string) (id : fun_decl_id) :
      FunDeclId.id option * string =
    [%ldebug "(" ^ trait_decl.name ^ "): compute_item_name: " ^ item_name];
    let trans : pure_fun_translation =
      match FunDeclId.Map.find_opt id ctx.trans_funs with
      | Some decl -> decl
      | None ->
          [%craise] trait_decl.item_meta.span
            ("Unexpected error: could not find the declaration for method '"
           ^ item_name ^ "' for trait declaration '"
            ^ name_to_string ctx trait_decl.item_meta.name
            ^ "'")
    in

    let f = trans.f in
    (* We do something special to reuse the [ctx_compute_fun_decl]
       function. TODO: make it cleaner. *)
    let llbc_name : Types.name =
      [ Types.PeIdent (item_name, Disambiguator.zero) ]
    in
    let f = { f with item_meta = { f.item_meta with name = llbc_name } } in
    [%ldebug
      "compute_item_name: llbc_name=" ^ name_to_string ctx f.item_meta.name];
    let name = ctx_compute_fun_name f true ctx in
    (* Add a prefix if necessary *)
    let name =
      if !record_fields_short_names then name
      else ctx_compute_trait_decl_name ctx trait_decl ^ "_" ^ name
    in
    (None, name)
  in
  (* Compute the names *)
  let method_names =
    match builtin_info with
    | None ->
        (* Not a builtin function *)
        List.map
          (fun (method_id, name, bound_fn) ->
            let default_id, fun_name =
              compute_item_name name bound_fn.binder_value.fun_id
            in
            (method_id, default_id, fun_name))
          methods
    | Some info ->
        (* This is a builtin *)
        let funs_map = StringMap.of_list info.methods in
        List.map
          (fun (method_id, item_name, fun_binder) ->
            match StringMap.find_opt item_name funs_map with
            | None ->
                [%warn] trait_decl.item_meta.span
                  ("When retrieving the builtin information for trait decl '"
                 ^ trait_decl.name
                 ^ "', could not find the information for item '" ^ item_name
                 ^ "'. The model defined in the " ^ Config.backend_name ()
                 ^ " library seems to be missing the corresponding field.");
                (* Use the LLBC definition to compute the name *)
                let default_id, fun_name =
                  compute_item_name item_name fun_binder.binder_value.fun_id
                in
                (method_id, default_id, fun_name)
            | Some info ->
                let fun_name = info.extract_name in
                let default_id =
                  if info.has_default then Some fun_binder.binder_value.fun_id
                  else None
                in
                (method_id, default_id, fun_name))
          methods
  in
  (* Register the names *)
  List.fold_left
    (fun ctx (method_id, default_id, fun_name) ->
      (* Register the method name.

          Similarly as with structure fields, in the case of Lean check
          whether we collide with keywords. If it is the case, add french quotes.
       *)
      let fun_name =
        match backend () with
        | Lean when names_maps_is_keyword ctx.names_maps fun_name ->
            "«" ^ fun_name ^ "»"
        | _ -> fun_name
      in
      let ctx =
        ctx_add trait_decl.item_meta.span
          (TraitMethodId (trait_decl.def_id, method_id))
          fun_name ctx
      in
      (* Also register the default implementation if there is *)
      match default_id with
      | Some def_id when backend () = Lean ->
          ctx_add trait_decl.item_meta.span
            (FunId (FromLlbc (FunId (FRegular def_id), None)))
            (trait_decl_name ^ fun_name ^ ".default")
            ctx
      | _ -> ctx)
    ctx method_names

(** Similar to {!extract_type_decl_register_names} *)
let extract_trait_decl_register_names (ctx : extraction_ctx)
    (trait_decl : trait_decl) : extraction_ctx =
  let ctx, trait_name =
    let trait_name, trait_constructor =
      match trait_decl.builtin_info with
      | None ->
          ( ctx_compute_trait_decl_name ctx trait_decl,
            ctx_compute_trait_decl_constructor ctx trait_decl )
      | Some info -> (info.extract_name, info.constructor)
    in
    let ctx =
      ctx_add trait_decl.item_meta.span (TraitDeclId trait_decl.def_id)
        trait_name ctx
    in
    let ctx =
      ctx_add trait_decl.item_meta.span
        (TraitDeclConstructorId trait_decl.def_id) trait_constructor ctx
    in
    (ctx, trait_name)
  in
  let builtin_info = trait_decl.builtin_info in
  (* Parent clauses *)
  let ctx =
    extract_trait_decl_register_parent_clause_names ctx trait_decl builtin_info
  in
  (* Constants *)
  let ctx =
    extract_trait_decl_register_constant_names ctx trait_decl builtin_info
  in
  (* Types *)
  let ctx = extract_trait_decl_type_names ctx trait_decl builtin_info in
  (* Required methods *)
  let ctx =
    extract_trait_decl_method_names ctx trait_decl trait_name builtin_info
  in
  ctx

(** Similar to {!extract_type_decl_register_names} *)
let extract_trait_impl_register_names (ctx : extraction_ctx)
    (trait_impl : trait_impl) : extraction_ctx =
  [%ldebug
    "trait_impl.impl_trait" ^ trait_decl_ref_to_string ctx trait_impl.impl_trait];
  (* Register some builtin information (if necessary) *)
  let ctx, builtin_info =
    match trait_impl.builtin_info with
    | None -> (ctx, None)
    | Some builtin_info ->
        let ctx =
          match builtin_info.keep_params with
          | None -> ctx
          | Some filter ->
              {
                ctx with
                trait_impls_filter_type_args_map =
                  TraitImplId.Map.add trait_impl.def_id filter
                    ctx.trait_impls_filter_type_args_map;
              }
        in
        let ctx =
          match builtin_info.keep_trait_clauses with
          | None -> ctx
          | Some filter ->
              {
                ctx with
                trait_impls_filter_trait_clauses_map =
                  TraitImplId.Map.add trait_impl.def_id filter
                    ctx.trait_impls_filter_trait_clauses_map;
              }
        in
        (ctx, Some builtin_info)
  in

  (* Everything is taken care of by {!extract_trait_decl_register_names} *but*
     the name of the implementation itself *)
  (* Compute the name *)
  let name =
    match builtin_info with
    | None -> ctx_compute_trait_impl_name ctx trait_impl
    | Some info -> info.extract_name
  in
  ctx_add trait_impl.item_meta.span (TraitImplId trait_impl.def_id) name ctx

(** Small helper.

    The type `ty` is to be understood in a very general sense. *)
let extract_trait_item (ctx : extraction_ctx) (fmt : F.formatter)
    (item_name : string) (separator : string) (ty : unit -> unit) : unit =
  F.pp_print_space fmt ();
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt item_name;
  F.pp_print_space fmt ();
  (* ":" or "=" *)
  F.pp_print_string fmt separator;
  ty ();
  (match backend () with
  | Lean -> ()
  | _ -> F.pp_print_string fmt ";");
  F.pp_close_box fmt ()

let extract_trait_decl_item (ctx : extraction_ctx) (fmt : F.formatter)
    (item_name : string) (ty : unit -> unit) : unit =
  extract_trait_item ctx fmt item_name ":" ty

let extract_trait_impl_item (ctx : extraction_ctx) (fmt : F.formatter)
    (item_name : string) (ty : unit -> unit) : unit =
  let assign =
    match backend () with
    | Lean | Coq -> ":="
    | _ -> "="
  in
  extract_trait_item ctx fmt item_name assign ty

(** Small helper - TODO: move *)
let generic_params_drop_prefix ~(drop_trait_clauses : bool)
    (g1 : generic_params) (g2 : generic_params) : generic_params =
  let open Collections.List in
  let types = drop (length g1.types) g2.types in
  let const_generics = drop (length g1.const_generics) g2.const_generics in
  let trait_clauses =
    if drop_trait_clauses then drop (length g1.trait_clauses) g2.trait_clauses
    else g2.trait_clauses
  in
  { types; const_generics; trait_clauses }

(** Small helper - TODO: move *)
let explicit_info_drop_prefix (g1 : generic_params) (g2 : explicit_info) :
    explicit_info =
  let open Collections.List in
  let explicit_types = drop (length g1.types) g2.explicit_types in
  let explicit_const_generics =
    drop (length g1.const_generics) g2.explicit_const_generics
  in
  { explicit_types; explicit_const_generics }

(** Small helper.

    Extract the items for a method in a trait decl. *)
let extract_trait_decl_method_items_aux (ctx : extraction_ctx)
    (fmt : F.formatter) (decl : trait_decl) (method_id : trait_method_id)
    (fn : fun_decl_ref binder) : unit =
  (* Lookup the definition *)
  let fun_decl_id = fn.binder_value.fun_id in
  let trans =
    [%silent_unwrap_opt_span] None
      (A.FunDeclId.Map.find_opt fun_decl_id ctx.trans_funs)
  in
  let span = trans.f.item_meta.span in
  (* Extract the items *)
  let fun_name = ctx_get_trait_method span decl.def_id method_id ctx in
  let ty () =
    let method_llbc_generics = fn.binder_llbc_generics in
    let method_generics = fn.binder_generics in
    let method_explicit_info = fn.binder_explicit_info in
    let ctx, type_params, cg_params, trait_clauses =
      ctx_add_generic_params span trans.f.item_meta.name Method
        method_llbc_generics method_generics ctx
    in
    let backend_uses_forall =
      match backend () with
      | Coq | Lean -> true
      | FStar | HOL4 -> false
    in
    let generics_not_empty = method_generics <> empty_generic_params in
    let use_forall = generics_not_empty && backend_uses_forall in
    let use_arrows = generics_not_empty && not backend_uses_forall in
    let use_forall_use_sep = false in
    extract_generic_params span ctx fmt TypeDeclId.Set.empty ~use_forall
      ~use_forall_use_sep ~use_arrows Method method_generics
      (Some method_explicit_info) type_params cg_params trait_clauses;
    if use_forall then F.pp_print_string fmt ",";

    (* Extract the inputs and output *)
    F.pp_print_space fmt ();
    (* We substitute the function item generics in temrs of the trait + method
       generics. *)
    let signature = trans.f.signature in
    let subst =
      make_subst_from_generics signature.generics fn.binder_value.fun_generics
    in
    let ({ inputs; output; _ } : fun_sig) = signature in
    let inputs = List.map (ty_substitute subst) inputs in
    let output = ty_substitute subst output in
    extract_fun_input_parameters_types span ctx fmt inputs;
    extract_ty span ctx fmt TypeDeclId.Set.empty ~inside:false output
  in
  extract_trait_decl_item ctx fmt fun_name ty

let extract_trait_decl_method_items (ctx : extraction_ctx) (fmt : F.formatter)
    (decl : trait_decl) (method_id : trait_method_id) (fn : fun_decl_ref binder)
    : unit =
  try extract_trait_decl_method_items_aux ctx fmt decl method_id fn
  with CFailure _ ->
    F.pp_print_space fmt ();
    extract_admit fmt

(** Extract a trait declaration *)
let extract_trait_decl (ctx : extraction_ctx) (fmt : F.formatter)
    (decl : trait_decl) : unit =
  (* Retrieve the trait name *)
  let decl_name = ctx_get_trait_decl decl.item_meta.span decl.def_id ctx in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  (let name =
     if !extract_external_name_patterns && not decl.item_meta.is_local then
       Some decl.item_meta.name
     else None
   in
   extract_comment_with_span ctx fmt
     [ "Trait declaration: [" ^ name_to_string ctx decl.item_meta.name ^ "]" ]
     name ~public:decl.item_meta.attr_info.public decl.item_meta.span);
  F.pp_print_break fmt 0 0;
  (* Extract the attributes *)
  ((* We need to list the extract options *)
   let add_quotes (ls : string list) : string list =
     List.map (fun s -> "\"" ^ s ^ "\"") ls
   in
   let types =
     List.map
       (fun (type_id, _) ->
         ctx_get_trait_type decl.item_meta.span decl.def_id type_id ctx)
       decl.types
   in
   let types =
     if types = [] then []
     else [ "(types := [" ^ String.concat ", " (add_quotes types) ^ "])" ]
   in
   let parent_clauses : string list =
     List.map
       (fun clause ->
         ctx_get_trait_parent_clause decl.item_meta.span decl.def_id
           clause.clause_id ctx)
       decl.parent_clauses
   in
   let parent_clauses =
     if parent_clauses = [] then []
     else
       [
         "(parentClauses := ["
         ^ String.concat ", " (add_quotes parent_clauses)
         ^ "])";
       ]
   in
   let consts =
     List.map
       (fun (const_id, _, _) ->
         ctx_get_trait_const decl.item_meta.span decl.def_id const_id ctx)
       decl.consts
   in
   let consts =
     if consts = [] then []
     else [ "(consts := [" ^ String.concat ", " (add_quotes consts) ^ "])" ]
   in
   (* TODO: default methods *)
   extract_attributes decl.item_meta.span ctx fmt decl.item_meta.name None []
     "rust_trait"
     (parent_clauses @ types @ consts)
     ~is_external:(not decl.item_meta.is_local));
  (* Open two outer boxes for the definition, so that whenever possible it gets printed on
     one line and indents are correct.

     There is just an exception with Lean: in this backend, line breaks are important
     for the parsing, so we always open a vertical box.
  *)
  if backend () = Lean then F.pp_open_vbox fmt ctx.indent_incr
  else (
    F.pp_open_hvbox fmt 0;
    F.pp_open_hvbox fmt ctx.indent_incr);

  (* `struct Trait (....) =` *)
  (* Open the box for the name + generics *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  let qualif =
    Option.get
      (type_decl_kind_to_qualif decl.item_meta.span SingleNonRec (Some Struct))
  in
  let is_empty = trait_decl_is_empty decl in
  if backend () = FStar && not is_empty then (
    F.pp_print_string fmt "noeq";
    F.pp_print_space fmt ());
  F.pp_print_string fmt qualif;
  F.pp_print_space fmt ();
  F.pp_print_string fmt decl_name;
  (* Print the generics *)
  let generics = decl.generics in
  (* Add the type and const generic params - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  (* First, reserve the trait field names (constants, types, methods, parent
     clauses) so that generic parameter names are made fresh w.r.t. them.
     This prevents e.g. a const generic parameter [N] from keeping its name
     when the trait also has a field named [N]. *)
  let ctx =
    let field_names =
      List.map
        (fun (const_id, _, _) ->
          ctx_get_trait_const decl.item_meta.span decl.def_id const_id ctx)
        decl.consts
      @ List.map
          (fun (type_id, _) ->
            ctx_get_trait_type decl.item_meta.span decl.def_id type_id ctx)
          decl.types
      @ List.map
          (fun (method_id, _, _) ->
            ctx_get_trait_method decl.item_meta.span decl.def_id method_id ctx)
          decl.methods
      @ List.map
          (fun (clause : trait_param) ->
            ctx_get_trait_parent_clause decl.item_meta.span decl.def_id
              clause.clause_id ctx)
          decl.parent_clauses
    in
    ctx_reserve_names field_names ctx
  in
  let ctx, type_params, cg_params, trait_clauses =
    ctx_add_generic_params decl.item_meta.span decl.item_meta.name Item
      decl.llbc_generics generics ctx
  in
  extract_generic_params decl.item_meta.span ctx fmt TypeDeclId.Set.empty Item
    generics (Some decl.explicit_info) type_params cg_params trait_clauses;

  F.pp_print_space fmt ();
  if is_empty && backend () = FStar then (
    F.pp_print_string fmt "= unit";
    (* Outer box *)
    F.pp_close_box fmt ())
  else if is_empty && backend () = Coq then (
    (* Coq is not very good at infering constructors *)
    let cons = ctx_get_trait_constructor decl.item_meta.span decl.def_id ctx in
    F.pp_print_string fmt (":= " ^ cons ^ "{}.");
    (* Outer box *)
    F.pp_close_box fmt ())
  else (
    (match backend () with
    | Lean -> F.pp_print_string fmt "where"
    | FStar -> F.pp_print_string fmt "= {"
    | Coq ->
        let cons =
          ctx_get_trait_constructor decl.item_meta.span decl.def_id ctx
        in
        F.pp_print_string fmt (":= " ^ cons ^ " {")
    | _ -> F.pp_print_string fmt "{");

    (* Close the box for the name + generics *)
    F.pp_close_box fmt ();

    (*
     * Extract the items
     *)

    (* The constants *)
    List.iter
      (fun (const_id, _, ty) ->
        let item_name =
          ctx_get_trait_const decl.item_meta.span decl.def_id const_id ctx
        in
        let ty () =
          let inside = false in
          F.pp_print_space fmt ();
          let ty = mk_result_ty ty in
          extract_ty decl.item_meta.span ctx fmt TypeDeclId.Set.empty ~inside ty
        in
        extract_trait_decl_item ctx fmt item_name ty)
      decl.consts;

    (* The types *)
    List.iter
      (fun (type_id, _) ->
        (* Extract the type *)
        let item_name =
          ctx_get_trait_type decl.item_meta.span decl.def_id type_id ctx
        in
        let ty () =
          F.pp_print_space fmt ();
          F.pp_print_string fmt (type_keyword decl.item_meta.span)
        in
        extract_trait_decl_item ctx fmt item_name ty)
      decl.types;

    (* The parent clauses - note that the parent clauses may refer to the types
       and const generics: for this reason we extract them *after* *)
    List.iter
      (fun clause ->
        let item_name =
          ctx_get_trait_parent_clause decl.item_meta.span decl.def_id
            clause.clause_id ctx
        in
        let ty () =
          F.pp_print_space fmt ();
          extract_trait_clause_type decl.item_meta.span ctx fmt
            TypeDeclId.Set.empty clause
        in
        extract_trait_decl_item ctx fmt item_name ty)
      decl.parent_clauses;

    (* The methods *)
    List.iter
      (fun (method_id, _name, fn) ->
        extract_trait_decl_method_items ctx fmt decl method_id fn)
      decl.methods;

    (* Close the outer boxes for the definition *)
    if backend () <> Lean then F.pp_close_box fmt ();
    (* Close the brackets *)
    match backend () with
    | Lean -> ()
    | Coq ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt "}."
    | _ ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt "}");
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Generate the [Arguments] instructions for the trait declarationsin Coq, so
    that we don't have to provide the implicit arguments when projecting the
    fields. *)
let extract_trait_decl_coq_arguments (ctx : extraction_ctx) (fmt : F.formatter)
    (decl : trait_decl) : unit =
  (* Counting the number of parameters of the trait declaration itself *)
  let num_prefix_params =
    List.length decl.generics.types
    + List.length decl.generics.const_generics
    + List.length decl.generics.trait_clauses
  in
  let params = Collections.List.repeat num_prefix_params Implicit in
  (* The constructor *)
  let cons_name =
    ctx_get_trait_constructor decl.item_meta.span decl.def_id ctx
  in
  extract_coq_arguments_instruction ctx fmt cons_name params;
  (* Add the record itself as a parameter for the projectors *)
  let params = params @ [ Explicit ] in
  (* The constants *)
  List.iter
    (fun (const_id, _, _) ->
      let item_name =
        ctx_get_trait_const decl.item_meta.span decl.def_id const_id ctx
      in
      extract_coq_arguments_instruction ctx fmt item_name params)
    decl.consts;
  (* The types *)
  List.iter
    (fun (type_id, _) ->
      (* The type *)
      let item_name =
        ctx_get_trait_type decl.item_meta.span decl.def_id type_id ctx
      in
      extract_coq_arguments_instruction ctx fmt item_name params)
    decl.types;
  (* The parent clauses *)
  List.iter
    (fun clause ->
      let item_name =
        ctx_get_trait_parent_clause decl.item_meta.span decl.def_id
          clause.clause_id ctx
      in
      extract_coq_arguments_instruction ctx fmt item_name params)
    decl.parent_clauses;
  (* The  methods *)
  List.iter
    (fun (method_id, _item_name, bound_fn) ->
      let explicit_info = bound_fn.binder_explicit_info in
      (* TODO: this looks incorrect, we should instantiate the binder properly *)
      let params =
        params
        @ List.concat
            [
              explicit_info.explicit_types;
              explicit_info.explicit_const_generics;
            ]
      in
      (* Extract *)
      let item_name =
        ctx_get_trait_method decl.item_meta.span decl.def_id method_id ctx
      in
      extract_coq_arguments_instruction ctx fmt item_name params)
    decl.methods;
  (* Add a space *)
  F.pp_print_space fmt ()

(** See {!extract_trait_decl_coq_arguments} *)
let extract_trait_decl_extra_info (ctx : extraction_ctx) (fmt : F.formatter)
    (trait_decl : trait_decl) : unit =
  match backend () with
  | Coq -> extract_trait_decl_coq_arguments ctx fmt trait_decl
  | _ -> ()

(** Small helper.

    Extract the items for a method in a trait impl. *)
let extract_trait_impl_method_items_aux (ctx : extraction_ctx)
    (fmt : F.formatter) (impl : trait_impl) (method_id : trait_method_id)
    (fn : fun_decl_ref binder) : unit =
  let span = impl.item_meta.span in
  let trait_decl_id = impl.impl_trait.trait_decl_id in
  let method_decl_id = fn.binder_value.fun_id in
  (* Lookup the definition *)
  let trans =
    [%unwrap_with_span] span
      (A.FunDeclId.Map.find_opt method_decl_id ctx.trans_funs)
      "Could not lookup the translated function, probably because of an error \
       which happened before"
  in
  (* Extract the items *)
  let fun_name = ctx_get_trait_method span trait_decl_id method_id ctx in
  let ty () =
    (* Extract the generics - we need to quantify over the generics which
       are specific to the method, and call it will all the generics
       (trait impl + method generics) *)
    let method_generics = fn.binder_generics in
    let method_llbc_generics = fn.binder_llbc_generics in
    let method_explicit_info = fn.binder_explicit_info in
    let ctx, method_tys, method_cgs, method_tcs =
      ctx_add_generic_params span trans.f.item_meta.name Method
        method_llbc_generics method_generics ctx
    in
    let use_fun = method_generics <> empty_generic_params in
    extract_generic_params span ctx fmt TypeDeclId.Set.empty ~use_fun Method
      method_generics (Some method_explicit_info) method_tys method_cgs
      method_tcs;
    if use_fun then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt "=>");

    (* Extract the function call *)
    F.pp_print_space fmt ();
    let fun_name = ctx_get_local_function span method_decl_id None ctx in
    F.pp_print_string fmt fun_name;
    extract_generic_args span ctx fmt TypeDeclId.Set.empty
      ~explicit:(Some trans.f.signature.explicit_info)
      fn.binder_value.fun_generics
  in

  extract_trait_impl_item ctx fmt fun_name ty

let extract_trait_impl_method_items (ctx : extraction_ctx) (fmt : F.formatter)
    (impl : trait_impl) (method_id : trait_method_id) (fn : fun_decl_ref binder)
    : unit =
  try extract_trait_impl_method_items_aux ctx fmt impl method_id fn
  with CFailure _ ->
    F.pp_print_space fmt ();
    extract_admit fmt

(** Extract a trait implementation *)
let extract_trait_impl (ctx : extraction_ctx) (fmt : F.formatter)
    ~(is_rec : bool) (impl : trait_impl) : unit =
  [%ltrace name_to_string ctx impl.item_meta.name];
  let span = impl.item_meta.span in
  (* Retrieve the impl name *)
  let impl_name = ctx_get_trait_impl span impl.def_id ctx in
  (* Add a break before *)
  F.pp_print_break fmt 0 0;
  (* Print a comment to link the extracted type to its original rust definition *)
  begin
    let decl_id = impl.impl_trait.trait_decl_id in
    let trait_decl = TraitDeclId.Map.find decl_id ctx.trans_trait_decls in
    let decl_ref = impl.llbc_impl_trait in
    let name = trait_decl.item_meta.name in
    let generics = (impl.llbc_generics, decl_ref.generics) in
    (* Extract the comment *)
    (let name, generics =
       if !extract_external_name_patterns && not impl.item_meta.is_local then (
         [%ldebug
           let params0, params1 =
             llbc_generic_params_to_strings ctx impl.llbc_generics
           in
           let params = String.concat ", " (params0 @ params1) in
           let args0, args1 =
             llbc_generic_args_to_strings ctx decl_ref.generics
           in
           let args = String.concat ", " (args0 @ args1) in
           "- trait_decl.llbc_generics: [" ^ params ^ "]"
           ^ "\n- decl_ref.decl_generics: [" ^ args ^ "]"];
         (Some name, Some generics))
       else (None, None)
     in
     extract_comment_with_span ctx fmt
       [
         "Trait implementation: ["
         ^ name_to_string ctx impl.item_meta.name
         ^ "]";
       ]
       (* TODO: why option option for the generics? Looks like a bug in OCaml!? *)
       name ?generics:(Some generics) ~public:impl.item_meta.attr_info.public
       span);
    F.pp_print_break fmt 0 0;
    (* Extract the attributes *)
    let attributes = if backend () = Lean then [ "reducible" ] else [] in
    extract_attributes span ctx fmt name (Some generics) attributes
      "rust_trait_impl" []
      ~is_external:(not impl.item_meta.is_local)
  end;

  (* Open two outer boxes for the definition, so that whenever possible it gets printed on
     one line and indents are correct.

     There is just an exception with Lean: in this backend, line breaks are important
     for the parsing, so we always open a vertical box.
  *)
  if backend () = Lean then (
    F.pp_open_vbox fmt 0;
    F.pp_open_vbox fmt ctx.indent_incr)
  else (
    F.pp_open_hvbox fmt 0;
    F.pp_open_hvbox fmt ctx.indent_incr);

  (* `let (....) : Trait ... =` *)
  (* Open the box for the name + generics *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  (* Lean only: we have a special elaboration if the impl is recursive *)
  (if is_rec then (
     F.pp_print_string fmt "impl_def";
     F.pp_print_space fmt ())
   else
     match fun_decl_kind_to_qualif SingleNonRec with
     | Some qualif ->
         F.pp_print_string fmt qualif;
         F.pp_print_space fmt ()
     | None -> ());
  F.pp_print_string fmt impl_name;

  (* Print the generics *)
  (* Add the type and const generic params - note that we need those bindings only for the
   * body translation (they are not top-level) *)
  (* First, reserve the trait decl field names (constants, types, methods, parent
     clauses) so that generic parameter names are made fresh w.r.t. them.
     See the comment in {!extract_trait_decl}. *)
  let ctx =
    let decl_id = impl.impl_trait.trait_decl_id in
    let trait_decl = TraitDeclId.Map.find decl_id ctx.trans_trait_decls in
    let field_names =
      List.map
        (fun (const_id, _, _) -> ctx_get_trait_const span decl_id const_id ctx)
        trait_decl.consts
      @ List.map
          (fun (type_id, _) -> ctx_get_trait_type span decl_id type_id ctx)
          trait_decl.types
      @ List.map
          (fun (method_id, _, _) ->
            ctx_get_trait_method span decl_id method_id ctx)
          trait_decl.methods
      @ List.map
          (fun (clause : trait_param) ->
            ctx_get_trait_parent_clause span decl_id clause.clause_id ctx)
          trait_decl.parent_clauses
    in
    ctx_reserve_names field_names ctx
  in
  let ctx, type_params, cg_params, trait_clauses =
    ctx_add_generic_params span impl.item_meta.name Item impl.llbc_generics
      impl.generics ctx
  in
  extract_generic_params span ctx fmt TypeDeclId.Set.empty Item impl.generics
    (Some impl.explicit_info) type_params cg_params trait_clauses;

  (* Print the type *)
  F.pp_print_space fmt ();
  F.pp_print_string fmt ":";
  F.pp_print_space fmt ();
  extract_trait_decl_ref span ctx fmt TypeDeclId.Set.empty ~inside:false
    impl.impl_trait;

  let is_empty = trait_impl_is_empty impl in

  F.pp_print_space fmt ();
  if is_empty && backend () = FStar then (
    F.pp_print_string fmt "= ()";
    (* Outer box *)
    F.pp_close_box fmt ())
  else if is_empty && backend () = Coq then (
    (* Coq is not very good at infering constructors *)
    let cons =
      ctx_get_trait_constructor span impl.impl_trait.trait_decl_id ctx
    in
    F.pp_print_string fmt (":= " ^ cons ^ ".");
    (* Outer box *)
    F.pp_close_box fmt ())
  else (
    if backend () = Lean then F.pp_print_string fmt ":= {"
    else if backend () = Coq then F.pp_print_string fmt ":= {|"
    else F.pp_print_string fmt "= {";

    (* Close the box for the name + generics *)
    F.pp_close_box fmt ();

    (*
     * Extract the items
     *)
    let trait_decl_id = impl.impl_trait.trait_decl_id in
    let trait_decl = TraitDeclId.Map.find trait_decl_id ctx.crate.trait_decls in

    (* The constants *)
    List.iter
      (fun (const_id, _, gref) ->
        let item_name = ctx_get_trait_const span trait_decl_id const_id ctx in
        (* Lookup the information about the explicit/implicit parameters *)
        let explicit =
          match GlobalDeclId.Map.find_opt gref.global_id ctx.trans_globals with
          | None ->
              (* The declaration might be missing if there was an error *) None
          | Some d -> Some d.explicit_info
        in
        let print_params () =
          extract_generic_args span ctx fmt TypeDeclId.Set.empty ~explicit
            gref.global_generics
        in
        let global_decl =
          [%unwrap_with_span] span
            (GlobalDeclId.Map.find_opt gref.global_id ctx.trans_globals)
            "Internal error"
        in
        let needs_brackets =
          (not global_decl.can_fail)
          &&
          match explicit with
          | Some explicit ->
              PureUtils.explicit_info_has_explicit explicit
              || gref.global_generics.trait_refs <> []
          | None -> gref.global_generics <> empty_generic_args
        in
        let ty () =
          F.pp_print_space fmt ();
          if not global_decl.can_fail then (
            let ok =
              match backend () with
              | Lean -> "ok"
              | _ -> "Ok"
            in
            F.pp_print_string fmt ok;
            F.pp_print_space fmt ());
          if needs_brackets then F.pp_print_string fmt "(";
          F.pp_print_string fmt (ctx_get_global span gref.global_id ctx);
          print_params ();
          if needs_brackets then F.pp_print_string fmt ")"
        in

        extract_trait_impl_item ctx fmt item_name ty)
      impl.consts;

    (* The types *)
    List.iter
      (fun (type_id, _, ty) ->
        (* Extract the type *)
        let item_name = ctx_get_trait_type span trait_decl_id type_id ctx in
        let ty () =
          F.pp_print_space fmt ();
          extract_ty span ctx fmt TypeDeclId.Set.empty ~inside:false ty
        in
        extract_trait_impl_item ctx fmt item_name ty)
      impl.types;

    (* The parent clauses *)
    List.iter
      (fun (clause, trait_ref) ->
        let item_name =
          ctx_get_trait_parent_clause span trait_decl_id clause.T.clause_id ctx
        in
        let ty () =
          F.pp_print_space fmt ();
          extract_trait_ref span ctx fmt TypeDeclId.Set.empty ~inside:false
            trait_ref
        in
        extract_trait_impl_item ctx fmt item_name ty)
      (List.combine trait_decl.implied_clauses impl.parent_trait_refs);

    (* The methods *)
    List.iter
      (fun (method_id, _name, bound_fn) ->
        extract_trait_impl_method_items ctx fmt impl method_id bound_fn)
      impl.methods;

    (* Close the outer boxes for the definition, as well as the brackets *)
    F.pp_close_box fmt ();
    if backend () = Coq then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt "|}.")
    else if (not (backend () = FStar)) || not is_empty then (
      F.pp_print_space fmt ();
      F.pp_print_string fmt "}"));
  F.pp_close_box fmt ();
  (* Add breaks to insert new lines between definitions *)
  F.pp_print_break fmt 0 0

(** Extract a unit test, if the function is a unit function (takes no
    parameters, returns unit).

    A unit test simply checks that the function normalizes to [Return ()].

    F*:
    {[
      let _ = assert_norm (FUNCTION = Return ())
    ]}

    Coq:
    {[
      Check (FUNCTION)%return).
    ]} *)
let extract_unit_test_if_marked (ctx : extraction_ctx) (fmt : F.formatter)
    (def : fun_decl) : unit =
  (* Check if this function has the #[verify::test] attribute *)
  let has_test_attr =
    List.exists
      (fun (attr : Meta.attribute) ->
        match attr with
        | AttrUnknown { path; _ } -> path = "verify::test"
        | _ -> false)
      def.item_meta.attr_info.attributes
  in
  if not has_test_attr then ()
  else
    (* Check if this is a unit function *)
    let sg = def.signature in
    if
      sg.generics = empty_generic_params
      && (sg.inputs = [ mk_unit_ty ] || sg.inputs = [])
      && sg.output = mk_result_ty mk_unit_ty
    then (
      (* Add a break before *)
      F.pp_print_break fmt 0 0;
      (* Print a comment *)
      extract_plain_comment fmt
        [ "Unit test for [" ^ name_to_string ctx def.item_meta.name ^ "]" ];
      F.pp_print_space fmt ();
      (* Open a box for the test *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      (* Print the test *)
      (match backend () with
      | FStar ->
          F.pp_print_string fmt "let _ =";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "assert_norm";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "(";
          let fun_name =
            ctx_get_local_function def.item_meta.span def.def_id def.loop_id ctx
          in
          F.pp_print_string fmt fun_name;
          if sg.inputs <> [] then (
            F.pp_print_space fmt ();
            F.pp_print_string fmt "()");
          F.pp_print_space fmt ();
          F.pp_print_string fmt "=";
          F.pp_print_space fmt ();
          let success =
            ctx_get_variant def.item_meta.span (TBuiltin TResult) result_ok_id
              ctx
          in
          F.pp_print_string fmt (success ^ " ())")
      | Coq ->
          F.pp_print_string fmt "Check";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "(";
          let fun_name =
            ctx_get_local_function def.item_meta.span def.def_id def.loop_id ctx
          in
          F.pp_print_string fmt fun_name;
          if sg.inputs <> [] then (
            F.pp_print_space fmt ();
            F.pp_print_string fmt "()";
            F.pp_print_space fmt ());
          F.pp_print_string fmt ")%return."
      | Lean ->
          F.pp_print_string fmt "#assert";
          F.pp_print_space fmt ();
          F.pp_print_string fmt "(";
          let fun_name =
            ctx_get_local_function def.item_meta.span def.def_id def.loop_id ctx
          in
          F.pp_print_string fmt fun_name;
          if sg.inputs <> [] then (
            F.pp_print_space fmt ();
            F.pp_print_string fmt "()");
          F.pp_print_space fmt ();
          F.pp_print_string fmt "==";
          F.pp_print_space fmt ();
          let success =
            ctx_get_variant def.item_meta.span (TBuiltin TResult) result_ok_id
              ctx
          in
          F.pp_print_string fmt (success ^ " ())")
      | HOL4 ->
          F.pp_print_string fmt "val _ = assert_ok (";
          F.pp_print_string fmt "“";
          let fun_name =
            ctx_get_local_function def.item_meta.span def.def_id def.loop_id ctx
          in
          F.pp_print_string fmt fun_name;
          if sg.inputs <> [] then (
            F.pp_print_space fmt ();
            F.pp_print_string fmt "()");
          F.pp_print_string fmt "”)");
      (* Close the box for the test *)
      F.pp_close_box fmt ();
      (* Add a break after *)
      F.pp_print_break fmt 0 0)
    else
      [%craise_opt_span] (Some def.item_meta.span)
        ("#[verify::test] on function with unsupported signature: "
        ^ name_to_string ctx def.item_meta.name
        ^ " (expected no generics, no params or unit param, and Result<()> \
           output)")
