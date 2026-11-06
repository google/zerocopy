open Libsail

open Type_check
open Ast
open Ast_compare
open Ast_defs
open Ast_util
open Bit
open Reporting
open Rewriter
open PPrint
open Pretty_print_common

module IntSet = Set.Make (Int)

(* Command line options *)
let opt_extern_types : string list ref = ref []

let opt_line_width : int ref = ref 100

type global_context = {
  effect_info : Effects.side_effect_info;
  fun_args : string list Bindings.t;
  ctor_renames : string Bindings.t;
  kid_id_renames : id option KBindings.t;
      (** Associates a kind variable to the corresponding argument of the function, used for implicit arguments. *)
  kid_id_renames_rev : kid Bindings.t;  (** Inverse of the [kid_id_renames] mapping. *)
  out_name_camel : string;
  defined_functions : IdSet.t;
}

let the_main_function_has_been_seen = ref false

let opt_noncomputable_functions : IdSet.t ref = ref IdSet.empty

let opt_partial_functions : IdSet.t ref = ref IdSet.empty

let non_beq_types : IdSet.t ref = ref IdSet.empty

let remove_empties (docs : document list) = List.filter (fun d -> d != empty) docs

let opens = ref IdSet.empty

type context = {
  global : global_context;
  env : Type_check.env;
      (** The typechecking environment of the current function. This environment is reset using [initial_context] when
          we start processing a new function. Note that we use it to store paths of the form id.x.y.z. *)
  kid_id_renames : id option KBindings.t;
      (** Associates a kind variable to the corresponding argument of the function, used for implicit arguments. *)
  kid_id_renames_rev : kid Bindings.t;  (** Inverse of the [kid_id_renames] mapping. *)
  mutable loop_level : int;
  in_sail_monad : bool;  (** Indicates whether we are in an expression of `SailM _` *)
  in_except_monad : document option;
      (** Indicates whether we are in an expression of `ExceptM _ _` what the return type is. *)
}

let context_init env global =
  {
    global;
    env;
    kid_id_renames = global.kid_id_renames;
    kid_id_renames_rev = global.kid_id_renames_rev;
    loop_level = 0;
    in_sail_monad = false;
    in_except_monad = None;
  }
let context_with_env ctx env = { ctx with env }

let add_single_kid_id_rename ctx id kid =
  let kir =
    match Bindings.find_opt id ctx.kid_id_renames_rev with
    | Some kid -> KBindings.add kid None ctx.kid_id_renames
    | None -> ctx.kid_id_renames
  in
  {
    ctx with
    kid_id_renames = KBindings.add kid (Some id) kir;
    kid_id_renames_rev = Bindings.add id kid ctx.kid_id_renames_rev;
  }

let add_global_kid_id_rename (global : global_context) id kid =
  let kir =
    match Bindings.find_opt id global.kid_id_renames_rev with
    | Some kid -> KBindings.add kid None global.kid_id_renames
    | None -> global.kid_id_renames
  in
  {
    global with
    kid_id_renames = KBindings.add kid (Some id) kir;
    kid_id_renames_rev = Bindings.add id kid global.kid_id_renames_rev;
  }

let implicit_parens x = enclose (string "{") (string "}") x
let leftarrow = string "←"
let leftarrowdo = string "← do"

let rec fix_id name =
  match name with
  (* Lean keywords to avoid, to expand as needed *)
  | "_lean_wildcard" -> "_"
  | "rec" | "def" | "at" | "alias" | "break" | "meta" | "class" -> name ^ "'"
  | "main" ->
      the_main_function_has_been_seen := true;
      "sail_main"
  | "?" -> "questionMark"
  | _ -> if String.contains name '#' then fix_id (String.concat "_" (String.split_on_char '#' name)) else name

let rename_ctor ctx (Id_aux (i, _) as id) =
  if not (Env.is_union_constructor id ctx.env) then None
  else (
    match Bindings.find_opt id ctx.global.ctor_renames with
    | None -> Some (string_of_id id |> string)
    | Some pref -> Some (string pref ^^ dot ^^ (string_of_id id |> string))
  )

let doc_id_ctor ?(ren_ctor = false) ctx (Id_aux (i, _) as id) =
  match (ren_ctor, rename_ctor ctx id) with
  | true, Some ren -> ren
  | _, _ -> (
      match i with
      | And_bool -> string "and_bool"
      | Or_bool -> string "or_bool"
      | Id i -> string (fix_id i)
      | Operator x -> string (Util.zencode_string ("op " ^ x))
    )

let doc_id_typ_ctor ctx env (Id_aux (i, _) as id) =
  let is_shadowed () = IdSet.mem id ctx.global.defined_functions || not (is_unbound (Env.lookup_id id env)) in
  match i with
  | And_bool -> string "and_bool"
  | Or_bool -> string "or_bool"
  | Id i -> if is_shadowed () then string (ctx.global.out_name_camel ^ "." ^ fix_id i) else string (fix_id i)
  | Operator x -> string (Util.zencode_string ("op " ^ x))

let doc_kid ctx (Kid_aux (Var x, _) as ki) =
  match KBindings.find_opt ki ctx.kid_id_renames with
  | Some (Some i) -> doc_id_ctor ctx i
  | _ -> "k_" ^ String.sub x 1 (String.length x - 1) |> fix_id |> string

(* TODO do a proper renaming and keep track of it *)

let is_enum env id = match Env.lookup_id id env with Enum _ -> true | _ -> false

let pat_is_plain_binder ?(suffix = "") env (P_aux (p, _)) =
  match p with
  | P_id id when not (is_enum env id) -> Some (Some id, None)
  | P_id _ -> Some (Some (Id_aux (Id ("id" ^ suffix), Unknown)), None)
  | P_typ (typ, P_aux (P_id id, _)) when not (is_enum env id) -> Some (Some id, Some typ)
  | P_wild | P_typ (_, P_aux (P_wild, _)) -> Some (None, None)
  | P_var (_, _) -> Some (Some (Id_aux (Id ("var" ^ suffix), Unknown)), None)
  | P_app (_, _) -> Some (Some (Id_aux (Id ("app" ^ suffix), Unknown)), None)
  | P_vector _ -> Some (Some (Id_aux (Id ("vect" ^ suffix), Unknown)), None)
  | P_tuple _ -> Some (Some (Id_aux (Id ("tuple" ^ suffix), Unknown)), None)
  | P_list _ -> Some (Some (Id_aux (Id ("list" ^ suffix), Unknown)), None)
  | P_cons (_, _) -> Some (Some (Id_aux (Id ("cons" ^ suffix), Unknown)), None)
  | P_lit (L_aux (L_unit, _)) -> Some (Some (Id_aux (Id "_", Unknown)), None)
  | P_lit _ -> Some (Some (Id_aux (Id ("lit" ^ suffix), Unknown)), None)
  | P_typ _ -> Some (Some (Id_aux (Id ("typ" ^ suffix), Unknown)), None)
  | P_struct _ -> Some (Some (Id_aux (Id ("struct_pat" ^ suffix), Unknown)), None)
  | _ -> None

(* Copied from the Coq PP *)
let args_of_typ l env typs =
  let arg i typ =
    let id = mk_id ("arg" ^ string_of_int i) in
    ((P_aux (P_id id, (l, mk_tannot env typ)), typ), E_aux (E_id id, (l, mk_tannot env typ)))
  in
  List.split (List.mapi arg typs)

(* Copied from the Coq PP *)
(* Sail currently has a single pattern to match against a list of
   argument types.  We need to tweak everything to match up,
   especially so that the function is presented in curried form.  In
   particular, if there's a single binder for multiple arguments
   (which rewriting can currently introduce) then we need to turn it
   into multiple binders and reconstruct it in the function body using
   the second return value of this function. *)
let rec untuple_args_pat typs (P_aux (paux, ((l, _) as annot)) as pat) =
  let env = env_of_annot annot in
  let identity body = body in
  match (paux, typs) with
  | P_tuple [], _ | P_lit (L_aux (L_unit, _)), _ ->
      let annot = (l, mk_tannot Env.empty unit_typ) in
      ([(P_aux (P_lit (mk_lit L_unit), annot), unit_typ)], identity)
  (* The type checker currently has a special case for a single arg type; if
     that is removed, then remove the next case. *)
  | P_tuple pats, [typ] -> ([(pat, typ)], identity)
  | P_tuple pats, _ -> (List.combine pats typs, identity)
  | P_wild, _ ->
      let wild typ = (P_aux (P_wild, (l, mk_tannot env typ)), typ) in
      (List.map wild typs, identity)
  | P_typ (_, pat), _ -> untuple_args_pat typs pat
  | P_as _, _ :: _ :: _ | P_id _, _ :: _ :: _ ->
      let argpats, argexps = args_of_typ l env typs in
      let argexp = E_aux (E_tuple argexps, annot) in
      let bindargs (E_aux (_, bannot) as body) = E_aux (E_let (pat, argexp, body), bannot) in
      (argpats, bindargs)
  | _, [typ] -> ([(pat, typ)], identity)
  | _, _ -> unreachable l __POS__ "Unexpected pattern/type combination"

let string_of_nexp_con (Nexp_aux (n, l)) =
  match n with
  | Nexp_constant _ -> "NExp_constant"
  | Nexp_id _ -> "Nexp_id"
  | Nexp_var _ -> "Nexp_var"
  | Nexp_app _ -> "Nexp_app"
  | Nexp_if _ -> "Nexp_if"
  | Nexp_times _ -> "Nexp_times"
  | Nexp_sum _ -> "Nexp_sum"
  | Nexp_minus _ -> "Nexp_minus"
  | Nexp_neg _ -> "Nexp_neg"
  | Nexp_exp _ -> "Nexp_exp"

let string_of_typ_con (Typ_aux (t, _)) =
  match t with
  | Typ_app _ -> "Typ_app"
  | Typ_var _ -> "Typ_var"
  | Typ_fn _ -> "Typ_fn"
  | Typ_tuple _ -> "Typ_tuple"
  | Typ_exist _ -> "Typ_exist"
  | Typ_bidir _ -> "Typ_bidir"
  | Typ_internal_unknown -> "Typ_internal_unknown"
  | Typ_id _ -> "Typ_id"

let doc_big_int i = if i >= Z.zero then string (Z.to_string i) else parens (string (Z.to_string i))

let is_unit t = match t with Typ_aux (Typ_id (Id_aux (Id "unit", _)), _) -> true | _ -> false

let is_lit e lit = match e with E_aux (E_lit (L_aux (lit', _)), _) -> lit = lit' | _ -> false

let is_true e = is_lit e L_true
let is_false e = is_lit e L_false

(* Adapted from Coq PP *)
(* These all take a local environment so that they can spot type names that are shadowed by let-bound variables. *)
let rec doc_nexp ctx env (Nexp_aux (n, l) as nexp) =
  let rec plussub (Nexp_aux (n, l) as nexp) =
    match n with
    | Nexp_sum (n1, n2) -> separate space [plussub n1; plus; mul n2]
    | Nexp_minus (n1, n2) -> separate space [plussub n1; minus; mul n2]
    | _ -> mul nexp
  and mul (Nexp_aux (n, l) as nexp) =
    match n with Nexp_times (n1, n2) -> separate space [mul n1; star; uneg n2] | _ -> uneg nexp
  and uneg (Nexp_aux (n, l) as nexp) =
    match n with Nexp_neg n -> parens (separate space [minus; uneg n]) | _ -> exp nexp
  and exp (Nexp_aux (n, l) as nexp) =
    match n with Nexp_exp n -> separate space [string "2"; caret; exp n] | _ -> app nexp
  and app (Nexp_aux (n, l) as nexp) =
    match n with
    | Nexp_if (i, t, e) ->
        separate space
          [string "if ("; doc_nconstraint ctx env i; string " : Bool) then"; atomic t; string "else"; atomic e]
    | Nexp_app (Id_aux (Id "div", _), [n1; n2]) -> separate space [atomic n1; string "/"; atomic n2]
    | Nexp_app (Id_aux (Id "mod", _), [n1; n2]) -> separate space [atomic n1; string "%"; atomic n2]
    | Nexp_app (Id_aux (Id "abs", _), [n1]) -> separate dot [atomic n1; string "natAbs"]
    | _ -> atomic nexp
  and atomic (Nexp_aux (n, l) as nexp) =
    match n with
    | Nexp_constant i -> doc_big_int i
    | Nexp_var ki -> doc_kid ctx ki
    | Nexp_id id -> doc_id_ctor ctx id
    | Nexp_sum _ | Nexp_minus _ | Nexp_times _ | Nexp_neg _ | Nexp_exp _ | Nexp_if _
    | Nexp_app (Id_aux (Id ("div" | "mod"), _), [_; _])
    | Nexp_app (Id_aux (Id "abs", _), [_]) ->
        parens (plussub nexp)
    | _ -> failwith ("NExp " ^ string_of_nexp_con nexp ^ " " ^ string_of_nexp nexp ^ " not translatable yet.")
  in
  atomic nexp

and doc_nconstraint ctx env (NC_aux (nc, _)) =
  match nc with
  | NC_and (n1, n2) -> flow (break 1) [doc_nconstraint ctx env n1; string "∧"; doc_nconstraint ctx env n2]
  | NC_or (n1, n2) -> flow (break 1) [doc_nconstraint ctx env n1; string "∨"; doc_nconstraint ctx env n2]
  | NC_equal (a1, a2) -> flow (break 1) [doc_typ_arg ctx env `All a1; string "="; doc_typ_arg ctx env `All a2]
  | NC_not_equal (a1, a2) -> flow (break 1) [doc_typ_arg ctx env `All a1; string "≠"; doc_typ_arg ctx env `All a2]
  | NC_app (f, args) -> parens (flow (break 1) (doc_id_ctor ctx f :: List.map (doc_typ_arg ctx env `All) args))
  | NC_false -> string "false"
  | NC_true -> string "true"
  | NC_ge (n1, n2) -> flow (break 1) [doc_nexp ctx env n1; string "≥"; doc_nexp ctx env n2]
  | NC_le (n1, n2) -> flow (break 1) [doc_nexp ctx env n1; string "≤"; doc_nexp ctx env n2]
  | NC_gt (n1, n2) -> flow (break 1) [doc_nexp ctx env n1; string ">"; doc_nexp ctx env n2]
  | NC_lt (n1, n2) -> flow (break 1) [doc_nexp ctx env n1; string "<"; doc_nexp ctx env n2]
  | NC_id i -> doc_id_ctor ctx i
  | NC_set (n, vs) ->
      flow (break 1)
        [string "List.elem"; doc_nexp ctx env n; brackets (separate_map comma_sp (fun x -> string (Z.to_string x)) vs)]
  | NC_var ki -> doc_kid ctx ki

and doc_typ_arg ctx env rel (A_aux (t, _)) =
  match t with
  | A_typ t -> doc_typ ctx env t
  | A_nexp n -> doc_nexp ctx env n
  | A_bool nc -> (
      match rel with `Only_relevant -> empty | `All -> parens (doc_nconstraint ctx env nc)
    )

and provably_nneg ctx x = Type_check.prove __POS__ ctx.env (nc_gteq x (nint 0))

and doc_typ ctx env (Typ_aux (t, _) as typ) =
  match t with
  | Typ_app (Id_aux (Id "vector", _), [A_aux (A_nexp m, _); A_aux (A_typ elem_typ, _)]) ->
      (* TODO: remove duplication with exists, below *)
      nest 2 (parens (flow space [string "Vector"; doc_typ ctx env elem_typ; doc_nexp ctx env m]))
  | Typ_id (Id_aux (Id "unit", _)) -> string "Unit"
  | Typ_id (Id_aux (Id "int", _)) -> string "Int"
  | Typ_id (Id_aux (Id "string", _)) -> string "String"
  | Typ_app (Id_aux (Id "atom_bool", _), _) | Typ_id (Id_aux (Id "bool", _)) -> string "Bool"
  | Typ_id (Id_aux (Id "bit", _)) -> parens (string "BitVec 1")
  | Typ_id (Id_aux (Id "nat", _)) -> string "Nat"
  | Typ_app (Id_aux (Id "bitvector", _), [A_aux (A_nexp m, _)]) | Typ_app (Id_aux (Id "bits", _), [A_aux (A_nexp m, _)])
    ->
      parens (string "BitVec " ^^ doc_nexp ctx env m)
  | Typ_app (Id_aux (Id "atom", _), [A_aux (A_nexp x, _)]) -> if provably_nneg ctx x then string "Nat" else string "Int"
  | Typ_app (Id_aux (Id "register", _), t_app) ->
      parens (string "RegisterRef " ^^ separate_map comma (doc_typ_app ctx env) t_app)
  | Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]) ->
      underscore (* TODO check if the type of implicit arguments can really be always inferred *)
  | Typ_app (Id_aux (Id "option", _), [A_aux (A_typ typ, _)]) -> parens (string "Option " ^^ doc_typ ctx env typ)
  | Typ_app (Id_aux (Id "list", _), args) ->
      parens (string "List" ^^ space ^^ separate_map space (doc_typ_arg ctx env `Only_relevant) args)
  | Typ_tuple ts -> parens (separate_map (space ^^ string "×" ^^ space) (doc_typ ctx env) ts)
  | Typ_id id -> doc_id_typ_ctor ctx env id
  | Typ_app (Id_aux (Id "range", _), [A_aux (A_nexp low, _); A_aux (A_nexp high, _)]) ->
      if provably_nneg ctx low then string "Nat" else string "Int"
  | Typ_app (Id_aux (Id "result", _), [A_aux (A_typ typ1, _); A_aux (A_typ typ2, _)]) ->
      parens (separate space [string "Result"; doc_typ ctx env typ1; doc_typ ctx env typ2])
  | Typ_var kid -> doc_kid ctx kid
  | Typ_app (id, args) ->
      parens (doc_id_typ_ctor ctx env id ^^ space ^^ separate_map space (doc_typ_arg ctx env `Only_relevant) args)
  | Typ_exist (kids, _, typ) ->
      let ctx =
        List.fold_left
          (fun ctx (KOpt_aux (KOpt_kind (_, kid), annot)) ->
            add_single_kid_id_rename ctx (Id_aux (Id "_lean_wildcard", annot)) kid
          )
          ctx kids
      in
      doc_typ ctx env typ
  | _ -> failwith ("Type " ^ string_of_typ_con typ ^ " " ^ string_of_typ typ ^ " not translatable yet.")

and doc_typ_app ctx env (A_aux (t, _) as typ) =
  match t with
  | A_typ t' -> doc_typ ctx env t'
  | A_bool nc -> doc_nconstraint ctx env nc
  | A_nexp m -> doc_nexp ctx env m

let captured_typ_var ((i, Typ_aux (t, _)) as typ) =
  match t with
  | Typ_app (Id_aux (Id "atom", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)])
  | Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]) ->
      Some (i, ki)
  | _ -> None

let doc_typ_id ctx env ((fid, typ), _) = flow (break 1) [doc_id_ctor ctx fid; colon; doc_typ ctx env typ]

let doc_kind ctx (kid : kid) (K_aux (k, _)) =
  match k with
  | K_int -> if provably_nneg ctx (Nexp_aux (Nexp_var kid, Unknown)) then string "Nat" else string "Int"
  | K_bool -> string "Bool"
  | K_type -> string "Type"

let doc_quant_item_all ctx env (QI_aux (qi, _)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (k, ki), _)) -> flow (break 1) [doc_kid ctx ki; colon; doc_kind ctx ki k]
  | QI_constraint c -> doc_nconstraint ctx env c

(* Used to annotate types with the original constraints *)
let doc_typ_quant_all ctx env qs = List.map (doc_quant_item_all ctx env) qs

let doc_typ_quant_in_comment ctx env tq =
  let typ_quants = doc_typ_quant_all ctx env tq in
  if List.length typ_quants > 0 then
    string "/-- Type quantifiers: " ^^ nest 2 (flow comma_sp typ_quants) ^^ string " -/" ^^ hardline
  else empty

let doc_quant_item_relevant ctx (QI_aux (qi, annot)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (k, ki), _)) -> Some (flow (break 1) [doc_kid ctx ki; colon; doc_kind ctx ki k])
  | QI_constraint c -> None

(* Used to translate type parameters of types, so we drop the constraints *)
let doc_typ_quant_relevant ctx tq =
  (* We go through the type variables with an environment that contains all the constraints,
     in order to detect when we can translate the Kind as Nat *)
  let ctx = context_init (Type_check.Env.add_typquant Unknown tq ctx.env) ctx.global in
  List.filter_map (doc_quant_item_relevant ctx) tq

let doc_quant_item_only_vars ctx (QI_aux (qi, annot)) =
  match qi with QI_id (KOpt_aux (KOpt_kind (k, ki), _)) -> Some (doc_kid ctx ki) | QI_constraint c -> None

(* Used to translate type parameters of type abbreviations *)
let doc_typ_quant_only_vars ctx tq = List.filter_map (doc_quant_item_only_vars ctx) tq

let lean_escape_string s = Str.global_replace (Str.regexp "\"") "\\\"" s

let doc_lit ~width (L_aux (lit, l)) =
  match lit with
  | L_unit -> string "()"
  | L_false -> string "false"
  | L_true -> string "true"
  | L_num i -> doc_big_int i
  | L_hex [] | L_bin [] -> string "BitVec.nil"
  | L_hex hex ->
      let width_specifier = if width then "#" ^ string_of_int (hex_lit_length hex) else "" in
      utf8string ("0x" ^ string_of_hex_lit ~group_separator:"" ~case:Uppercase hex ^ width_specifier)
  | L_bin bin -> (
      let width_specifier = if width then "#" ^ string_of_int (bin_lit_length bin) else "" in
      (* Print single bits as just 0 or 1 without a 0b prefix *)
      match bin with
      | [Non_empty (Bin_0, [])] -> string ("0" ^ width_specifier)
      | [Non_empty (Bin_1, [])] -> string ("1" ^ width_specifier)
      | _ -> utf8string ("0b" ^ string_of_bin_lit ~group_separator:"" bin ^ width_specifier)
    )
  | L_string s -> utf8string ("\"" ^ lean_escape_string s ^ "\"")
  | L_real r -> utf8string (Q.to_string (Util.Rational.from_rocq r))
(* TODO test if this is really working *)

let string_of_exp_con (E_aux (e, _)) =
  match e with
  | E_block _ -> "E_block"
  | E_ref _ -> "E_ref"
  | E_if _ -> "E_if"
  | E_loop _ -> "E_loop"
  | E_for _ -> "E_for"
  | E_vector_append _ -> "E_vector_append"
  | E_list _ -> "E_list"
  | E_cons _ -> "E_cons"
  | E_struct _ -> "E_struct"
  | E_struct_update _ -> "E_struct_update"
  | E_field _ -> "E_field"
  | E_match _ -> "E_match"
  | E_assign _ -> "E_assign"
  | E_sizeof _ -> "E_sizeof"
  | E_constraint _ -> "E_constraint"
  | E_exit _ -> "E_exit"
  | E_throw _ -> "E_throw"
  | E_try _ -> "E_try"
  | E_return _ -> "E_return"
  | E_assert _ -> "E_assert"
  | E_var _ -> "E_var"
  | E_undef -> "E_undef"
  | E_internal_plet _ -> "E_internal_plet"
  | E_internal_return _ -> "E_internal_return"
  | E_internal_assume _ -> "E_internal_assume"
  | E_internal_value _ -> "E_internal_value"
  | E_id _ -> "E_id"
  | E_lit _ -> "E_lit"
  | E_typ _ -> "E_typ"
  | E_app _ -> "E_app"
  | E_tuple _ -> "E_tuple"
  | E_vector _ -> "E_vector"
  | E_let _ -> "E_let"
  | E_config _ -> "E_config"

let rec is_anonymous_pat (P_aux (p, _) as full_pat) =
  match p with
  | P_wild -> true
  | P_id (Id_aux (Id s, _)) -> String.sub s 0 1 = "_"
  | P_lit (L_aux _) -> true
  | P_typ (_, p) -> is_anonymous_pat p
  | _ -> false

let string_of_pat_con (P_aux (p, _)) =
  match p with
  | P_app _ -> "P_app"
  | P_wild -> "P_wild"
  | P_lit _ -> "P_lit"
  | P_or _ -> "P_or"
  | P_not _ -> "P_not"
  | P_as _ -> "P_as"
  | P_typ _ -> "P_typ"
  | P_id _ -> "P_id"
  | P_var _ -> "P_var"
  | P_vector _ -> "P_vector"
  | P_vector_concat _ -> "P_vector_concat"
  | P_vector_subrange _ -> "P_vector_subrange"
  | P_tuple _ -> "P_tuple"
  | P_list _ -> "P_list"
  | P_cons _ -> "P_cons"
  | P_string_append _ -> "P_string_append"
  | P_struct _ -> "P_struct"

let string_of_def (DEF_aux (d, _)) =
  match d with
  | DEF_type _ -> "DEF_type"
  | DEF_constraint _ -> "DEF_constraint"
  | DEF_fundef _ -> "DEF_fundef"
  | DEF_mapdef _ -> "DEF_mapdef"
  | DEF_impl _ -> "DEF_impl"
  | DEF_let _ -> "DEF_let"
  | DEF_val (VS_aux (VS_val_spec (_, id, _), _)) -> "DEF_val " ^ string_of_id id
  | DEF_outcome _ -> "DEF_outcome"
  | DEF_instantiation _ -> "DEF_instantiation"
  | DEF_fixity _ -> "DEF_fixity"
  | DEF_overload _ -> "DEF_overload"
  | DEF_default _ -> "DEF_default"
  | DEF_scattered _ -> "DEF_scattered"
  | DEF_measure _ -> "DEF_measure"
  | DEF_loop_measures _ -> "DEF_loop_measures"
  | DEF_register _ -> "DEF_register"
  | DEF_internal_mutrec _ -> "DEF_internal_mutrec"
  | DEF_pragma _ -> "DEF_pragma"

(** Fix identifiers to match the standard Lean library. *)
let fixup_match_id (Id_aux (id, l) as id') =
  match id with
  | Id id ->
      Id_aux (Id (match id with "Some" -> "some" | "None" -> "none" | "early_return" -> "throw" | _ -> fix_id id), l)
  | _ -> id'

let rec update_ctx_pat (ctx : context) (P_aux (p, (l, annot)) as pat) =
  match p with
  | P_var (P_aux (P_id id, _), TP_aux (TP_var kid, tp_l)) -> add_single_kid_id_rename ctx id kid
  | P_typ (_, p') | P_as (p', _) | P_var (p', _) -> update_ctx_pat ctx p'
  | P_app (_, pats) | P_vector pats | P_vector_concat pats | P_tuple pats | P_list pats | P_string_append pats ->
      List.fold_left update_ctx_pat ctx pats
  | _ -> ctx

let rec doc_pat ?(need_parens = false) ?(in_vector = false) ctx in_match_bv (P_aux (p, (l, annot)) as pat) =
  let opt_parens doc = if need_parens then parens doc else doc in
  let env = env_of_tannot annot in
  match p with
  | P_wild -> underscore
  | P_lit lit -> doc_lit ~width:false lit
  | P_typ (Typ_aux (Typ_id (Id_aux (Id "bit", _)), _), p) when in_vector -> doc_pat ctx in_match_bv p ^^ string ":1"
  | P_typ (Typ_aux (Typ_app (Id_aux (Id id, _), [A_aux (A_nexp (Nexp_aux (Nexp_constant i, _)), _)]), _), p)
    when in_vector && (id = "bits" || id = "bitvector") ->
      doc_pat ctx in_match_bv p ^^ string ":" ^^ doc_big_int i
  | P_typ (ptyp, p) when in_vector -> doc_pat ctx in_match_bv p ^^ string ":" ^^ doc_typ ctx env ptyp
  | P_typ (ptyp, p) -> doc_pat ctx in_match_bv p
  | P_id id -> (
      match typ_of_pat pat with
      | Typ_aux (Typ_app (Id_aux (Id id', _), [A_aux (A_nexp (Nexp_aux (Nexp_constant i, _)), _)]), _)
        when in_vector && (id' = "bits" || id' = "bitvector") ->
          (fixup_match_id id |> doc_id_ctor ctx) ^^ string ":" ^^ doc_big_int i
      | _ ->
          let prefix = if Type_check.is_enum_member id ctx.env then string "." else empty in
          prefix ^^ (fixup_match_id id |> doc_id_ctor ctx)
    )
  | P_tuple pats -> separate (string ", ") (List.map (doc_pat ctx in_match_bv) pats) |> parens
  | P_list pats -> separate (string ", ") (List.map (doc_pat ctx in_match_bv) pats) |> brackets
  | P_vector pats
    when List.for_all (fun p -> match p with P_aux (P_lit _, _) -> true | _ -> false) pats && not in_match_bv ->
      string "0b" ^^ concat (List.map (doc_pat ~in_vector:true ctx in_match_bv) pats)
  | P_vector pats -> concat (List.map (doc_pat ~in_vector:true ctx in_match_bv) pats)
  | P_vector_concat pats -> doc_vector_concat ctx pats
  | P_app (Id_aux (Id "None", _), p) -> string "none"
  | P_app (cons, pats) ->
      opt_parens
        (string "."
        ^^ doc_id_ctor ctx (fixup_match_id cons)
        ^^ space
        ^^ separate_map (string ", ") (doc_pat ~need_parens:true ctx in_match_bv) pats
        )
  | P_var (p, _) -> doc_pat ctx in_match_bv p
  | P_as (pat, id) -> doc_pat ctx in_match_bv pat
  | P_struct (_, pats, _) ->
      let pats =
        List.map (fun (id, pat) -> separate space [doc_id_ctor ctx id; coloneq; doc_pat ctx in_match_bv pat]) pats
      in
      braces (space ^^ separate (comma ^^ space) pats ^^ space)
  | P_cons (hd_pat, tl_pat) ->
      parens (separate space [doc_pat ctx in_match_bv hd_pat; string "::"; doc_pat ctx in_match_bv tl_pat])
  | _ -> failwith ("Doc Pattern " ^ string_of_pat_con pat ^ " " ^ string_of_pat pat ^ " not translatable yet.")

and doc_vector_concat ctx pats =
  let rec doc_part (P_aux (aux, (l, _)) as pat) =
    match aux with
    | P_lit (L_aux (L_bin bin, _)) ->
        let bits = BitList.of_bin_lit bin in
        concat_map (function B0 -> char '0' | B1 -> char '1') bits
    | P_lit (L_aux (L_hex hex, _)) ->
        let bits = BitList.of_hex_lit hex in
        concat_map (function B0 -> char '0' | B1 -> char '1') bits
    | P_id id -> (
        match destruct_bitvector (env_of_pat pat) (typ_of_pat pat) with
        | Some (Nexp_aux (Nexp_constant n, _)) ->
            doc_id_ctor ctx (fixup_match_id id) ^^ char ':' ^^ string (Z.to_string n)
        | _ -> Reporting.unreachable l __POS__ "Found subpattern with unclear width in bitvector pattern"
      )
    | P_typ (_, pat) -> doc_part pat
    | P_vector pats -> separate_map comma doc_part pats
    | _ -> Reporting.unreachable l __POS__ ("Unexpected pattern in match_bv vector_concat pattern " ^ string_of_pat pat)
  in
  brackets (separate_map comma doc_part pats)

let doc_pat_typ_ascription ctx env (P_aux (p, (l, annot)) as pat) =
  match p with P_typ (ptyp, p) -> Some (doc_typ ctx env ptyp) | _ -> None

(* Copied from the Coq PP *)
let rebind_cast_pattern_vars pat typ exp =
  let rec aux pat typ =
    match (pat, typ) with
    | P_aux (P_typ (target_typ, P_aux (P_id id, (l, ann))), _), source_typ when not (is_enum (env_of exp) id) ->
        if Typ.compare target_typ source_typ == 0 then []
        else (
          let l = Parse_ast.Generated l in
          let cast_annot = Type_check.replace_typ source_typ ann in
          let e_annot = Type_check.mk_tannot (env_of exp) source_typ in
          [(pat, E_aux (E_id id, (l, e_annot)))]
        )
    | P_aux (P_tuple pats, _), Typ_aux (Typ_tuple typs, _) -> List.concat (List.map2 aux pats typs)
    | _ -> []
  in
  let add_lb (E_aux (_, ann) as exp) (pat, bind) = E_aux (E_let (pat, bind, exp), ann) in
  (* Don't introduce new bindings at the top-level, we'd just go into a loop. *)
  let lbs =
    match (pat, typ) with
    | P_aux (P_tuple pats, _), Typ_aux (Typ_tuple typs, _) -> List.concat (List.map2 aux pats typs)
    | _ -> []
  in
  List.fold_left add_lb exp lbs

let wrap_with_pure (needs_return : bool) ?(with_parens = false) (d : document) =
  if needs_return then (
    let d = if with_parens then parens d else d in
    parens (nest 2 (flow space [string "pure"; d]))
  )
  else d

let wrap_with_left_arrow (needs_left_arrow : bool) (d : document) =
  if needs_left_arrow then parens (nest 2 (flow space [leftarrow; d])) else d

let wrap_with_do (with_arrow : bool) (needs_return : bool) (d : document) =
  let ar_do = if with_arrow then string "← do" else string "do" in
  if needs_return then parens (nest 2 (flow hardline [ar_do; d])) else d

let get_fn_implicits (Typ_aux (t, _)) : bool list =
  let arg_implicit arg =
    match arg with
    | Typ_aux (Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]), _) -> true
    | _ -> false
  in
  match t with Typ_fn (args, cod) -> List.map arg_implicit args | _ -> []

let rec is_bitvector_pattern (P_aux (pat, _)) =
  match pat with P_vector _ | P_vector_concat _ -> true | P_as (pat, _) -> is_bitvector_pattern pat | _ -> false

let is_match_bv =
  List.exists (function Pat_aux (Pat_exp (pat, _), _) | Pat_aux (Pat_when (pat, _, _), _) -> is_bitvector_pattern pat)

let rec doc_implicit_args ?(docs = []) ns ims d_args =
  match (ns, ims, d_args) with
  | [], [], [] -> docs
  | n :: ns, im :: ims, d_arg :: d_args ->
      (* It would be nice to be able to know if the argument was in the source code. *)
      let docs = if im then parens (string n ^^ space ^^ coloneq ^^ space ^^ d_arg) :: docs else docs in
      doc_implicit_args ~docs ns ims d_args
  | _, _, _ -> []

let op_of_id id =
  match id with
  | Some "_lean_and" -> `Binop "&&"
  | Some "_lean_or" -> `Binop "||"
  | Some "_lean_beq" -> `Binop "=="
  | Some "_lean_bne" -> `Binop "!="
  | Some "_lean_not" -> `Unop "!"
  | Some "_lean_add" -> `Binop "+"
  | Some "_lean_addi" -> `Binop "+i"
  | Some "_lean_sub" -> `Binop "-"
  | Some "_lean_subi" -> `Binop "-i"
  | Some "_lean_mul" -> `Binop "*"
  | Some "_lean_muli" -> `Binop "*i"
  | Some "_lean_div" -> `Binop "/"
  | Some "_lean_app" -> `Binop "+++" (* see issue sail#1630 *)
  | Some "_lean_bvand" -> `Binop "&&&"
  | Some "_lean_bvor" -> `Binop "|||"
  | Some "_lean_bvxor" -> `Binop "^^^"
  | Some "_lean_shiftl" -> `Binop "<<<"
  | Some "_lean_shiftr" -> `Binop ">>>"
  | Some "_lean_lt" -> `Binop "<b"
  | Some "_lean_ge" -> `Binop "≥b"
  | Some "_lean_le" -> `Binop "≤b"
  | Some "_lean_gt" -> `Binop ">b"
  | Some "_lean_pow2" -> `Unop "2 ^"
  | Some "_lean_pow2i" -> `Unop "2 ^i"
  | _ -> `NotOp

let unnop_of_id id = match id with Some "_lean_pow2" -> Some "2 ^ " | _ -> None

let is_loop id =
  match string_of_id id with "while#" | "while#t" | "foreach#" | "until#" | "until#t" -> true | _ -> false

let has_loop (e : 'a exp) =
  let e_app (id, args) = is_loop id || List.fold_left ( || ) false args in
  let e_return _ = true in
  fold_exp { (pure_exp_alg false ( || )) with e_app; e_return } e

let is_effect_id id = match string_of_id id with "while#" | "foreach#" | "early_return" -> true | _ -> false

let has_effect_app e =
  let e_app (id, args) = is_effect_id id || List.fold_left ( || ) false args in
  let e_return _ = true in
  fold_exp { (pure_exp_alg false ( || )) with e_app; e_return } e

let has_effect e = effectful (effect_of e) || has_effect_app e

let doc_loop_var ctx (E_aux (e, (l, _)) as exp) =
  match e with
  | E_id id ->
      let id_pp = doc_id_ctor ctx id in
      let typ = typ_of exp in
      (id_pp, id_pp)
  | E_lit (L_aux (L_unit, _)) -> (string "()", underscore)
  | _ -> raise (Reporting.err_unreachable l __POS__ ("Bad expression for variable in loop: " ^ string_of_exp exp))

let make_loop_vars ctx extra_binders varstuple =
  match varstuple with
  | E_aux (E_tuple vs, _) ->
      let vs = List.map (doc_loop_var ctx) vs in
      let mkpp f vs = separate (string ", ") (List.map f vs) in
      let tup_pp = mkpp (fun (pp, _) -> pp) vs in
      let match_pp = mkpp (fun (_, pp) -> pp) vs in
      (parens tup_pp, separate space ((string "λ" :: extra_binders) @ [parens match_pp; string "=>"]))
  | _ ->
      let exp_pp, match_pp = doc_loop_var ctx varstuple in
      (exp_pp, separate space ((string "λ" :: extra_binders) @ [match_pp; string "=>"]))

let name_loop_vars ctx =
  let ll = ctx.loop_level in
  ctx.loop_level <- ll + 1;
  match ll with 0 -> (string "loop_vars", ctx) | _ -> (string "loop_vars_" ^^ string (string_of_int ll), ctx)

let prepend_monad ctx exp doc =
  match (ctx.in_sail_monad, ctx.in_except_monad) with
  | true, Some ty -> [string "SailME"; ty; doc]
  | true, None -> [string "SailM"; doc]
  | false, Some ty -> [string "ExceptM"; ty; doc]
  | false, None -> [string "Id"; doc]

let match_or_match_bv (is_match_bv : bool) brs = if is_match_bv then "match_bv " else "match "

let rec doc_match_clause (is_bv : bool) (as_monadic : bool) ctx (Pat_aux (cl, l) as p) =
  match cl with
  | Pat_exp (pat, branch) ->
      group
        (nest 2
           (string "| " ^^ doc_pat ctx is_bv pat ^^ string " =>"
           ^^ string (if is_bv && as_monadic then " do" else "")
           ^^ break 1 ^^ wrap_exp as_monadic ctx branch
           )
        )
  | Pat_when (pat, when_, branch) when is_bv ->
      group
        (nest 2
           (string "| " ^^ doc_pat ctx is_bv pat ^^ string " if " ^^ doc_exp false ctx when_ ^^ string " =>"
           ^^ string (if is_bv && as_monadic then " do" else "")
           ^^ break 1 ^^ wrap_exp as_monadic ctx branch
           )
        )
  | Pat_when (pat, when_, branch) ->
      failwith ("The Lean backend does not support 'when' clauses in patterns:\n" ^ string_of_pexp p)

and wrap_exp as_monadic ctx e =
  let with_arrow = not as_monadic in
  let d = doc_exp as_monadic ctx e in
  match e with
  | E_aux (arg', _) -> (
      match arg' with
      | E_typ (_, e) when has_effect e -> wrap_with_do with_arrow true d
      | E_typ (_, e) when has_early_return e -> parens d
      | E_let _ | E_internal_plet _ | E_if _ | E_match _ | E_var _ | E_block _ ->
          if has_effect e then wrap_with_do with_arrow true d else parens d
      | _ when has_loop e -> wrap_with_do with_arrow true d
      | _ -> d
    )

(* TODO: refactor this function *)
and doc_loop l as_monadic ctx loop_kind args =
  let lambda effects lambda_pp d =
    let lambda_pp = if effects then lambda_pp ^^ string " do" else lambda_pp in
    parens (prefix 2 1 (group lambda_pp) d)
  in
  let cond, varstuple, body, measure =
    match args with
    | [cond; varstuple; body] -> (cond, varstuple, body, None)
    | [cond; varstuple; body; measure] -> (cond, varstuple, body, Some measure)
    | _ -> raise (Reporting.err_unreachable l __POS__ "Unexpected number of arguments for loop combinator")
  in
  let body =
    match body with
    | E_aux
        ( E_internal_plet
            ( P_aux ((P_wild | P_typ (_, P_aux (P_wild, _))), _),
              E_aux
                ( E_assert
                    (E_aux (E_lit (L_aux (L_true, _)), _), E_aux (E_lit (L_aux (L_string "loop dummy assert", _)), _)),
                  _
                ),
              body'
            ),
          _
        ) ->
        body'
    | _ -> body
  in
  let body_effects = has_effect body in
  let (E_aux (_, annot)) = cond in
  let cond_effects = has_effect cond in
  let vartuple_pp, base_lambda = make_loop_vars ctx [] varstuple in
  let vars_pp, body_ctx = name_loop_vars ctx in
  let body_pp = doc_exp body_effects body_ctx body in
  let vars_dec_pp = string "let mut " ^^ vars_pp ^^ string " := " ^^ vartuple_pp in
  let cond_pp = doc_exp cond_effects ctx cond in
  let cond_pp = lambda cond_effects base_lambda cond_pp in
  let loop_cond = wrap_with_left_arrow cond_effects (prefix 2 1 cond_pp vars_pp) in
  let measure = Option.map (fun m -> parens (string "fuel :=" ^^ doc_exp false ctx m)) measure in
  match loop_kind with
  | `While ->
      let loop_head = prefix 2 1 (string "while " ^^ loop_cond) (string "do") in
      let arrow = if body_effects then leftarrowdo else coloneq in
      let loop_body_1 = string "let " ^^ vartuple_pp ^^ space ^^ coloneq ^^ space ^^ vars_pp in
      let loop_body = loop_body_1 ^^ hardline ^^ prefix 2 1 (vars_pp ^^ space ^^ arrow) body_pp in
      let full_loop = prefix 2 1 loop_head loop_body in
      separate hardline [vars_dec_pp; full_loop; wrap_with_pure as_monadic vars_pp]
  | `WhileFuel | `UntilFuel ->
      let measure = Option.get measure in
      let cond_pp = parens (string "fun " ^^ vartuple_pp ^^ string " => " ^^ doc_exp true ctx cond) in
      let init = doc_exp false ctx varstuple in
      let loop_fn = match loop_kind with `WhileFuel -> "whileFuelM" | _ -> "untilFuelM" in
      let loop_head = string loop_fn ^^ space ^^ measure ^^ space ^^ cond_pp ^^ space ^^ init in
      let arrow = if body_effects then leftarrowdo else coloneq in
      let fun_header = string "fun " ^^ vartuple_pp ^^ space ^^ string "=> do" in
      let body_pp = doc_exp true body_ctx body in
      let loop_body = prefix 2 1 fun_header body_pp in
      let full_loop = prefix 2 1 loop_head loop_body in
      let full_loop = string "let" ^^ space ^^ vars_pp ^^ space ^^ leftarrow ^^ space ^^ full_loop in
      separate hardline [full_loop; wrap_with_pure as_monadic vars_pp]
  | `Until ->
      let loop_head = string "repeat" in
      let loop_footer = flow (break 1) [string "until"; loop_cond] in
      let arrow = if body_effects then leftarrowdo else coloneq in
      let loop_body_1 = string "let " ^^ vartuple_pp ^^ space ^^ coloneq ^^ space ^^ vars_pp in
      let loop_body = loop_body_1 ^^ hardline ^^ prefix 2 1 (vars_pp ^^ space ^^ arrow) body_pp in
      let full_loop = prefix 2 1 loop_head loop_body in
      separate hardline [vars_dec_pp; full_loop; loop_footer; wrap_with_pure as_monadic vars_pp]

and doc_exp (as_monadic : bool) ctx (E_aux (e, (l, annot)) as full_exp) =
  let env = env_of_tannot annot in
  let d_of_arg ?(with_arrow = true) ctx arg =
    let wrap, arg_monadic =
      match arg with
      | E_aux (arg', _) -> (
          match arg' with
          | E_typ (_, e) when has_effect e -> ((fun x -> wrap_with_do with_arrow true x), true)
          | E_typ (_, e) when has_early_return e -> (parens, false)
          | E_let _ | E_internal_plet _ | E_if _ | E_match _ | E_var _ | E_block _ ->
              if has_effect arg then ((fun x -> wrap_with_do with_arrow true x), true) else (parens, false)
          | _ when has_loop arg -> ((fun x -> wrap_with_do with_arrow true x), true)
          | _ -> ((fun x -> x), not with_arrow) (* for [sailTryCatch] the argument should be a computation *)
        )
    in
    wrap (doc_exp arg_monadic ctx arg)
  in
  let d_of_field (FE_aux (FE_fexp (field, e), _) as fexp) = doc_fexp (has_effect e) ctx fexp in
  match e with
  | E_id id ->
      if Env.is_register id env then wrap_with_left_arrow (not as_monadic) (string "readReg " ^^ doc_id_ctor ctx id)
      else wrap_with_pure as_monadic (doc_id_ctor ~ren_ctor:true ctx id)
  | E_lit l -> wrap_with_pure as_monadic (doc_lit ~width:true l)
  | E_app (Id_aux (Id "None", _), _) -> wrap_with_pure as_monadic (string "none")
  | E_app (Id_aux (Id "Some", _), args) ->
      wrap_with_pure as_monadic
        (let d_id = string "some" in
         let d_args = List.map (d_of_arg ctx) args in
         nest 2 (parens (flow (break 1) (d_id :: d_args)))
        )
  | E_app (Id_aux (Id "__id", _), [e]) -> doc_exp as_monadic ctx e
  | E_app (Id_aux (Id "while#", _), args) -> doc_loop l as_monadic ctx `While args
  | E_app (Id_aux (Id "while#t", _), args) -> doc_loop l as_monadic ctx `WhileFuel args
  | E_app (Id_aux (Id "until#", _), args) -> doc_loop l as_monadic ctx `Until args
  | E_app (Id_aux (Id "until#t", _), args) -> doc_loop l as_monadic ctx `UntilFuel args
  | E_app (Id_aux (Id "foreach#", _), args) -> (
      match args with
      | [from_exp; to_exp; step_exp; ord_exp; vartuple; body] ->
          let loopvar, body =
            match body with
            | E_aux
                ( E_if
                    ( _,
                      E_aux
                        ( E_let
                            ( ( P_aux (P_typ (_, P_aux (P_var (P_aux (P_id id, _), _), _)), _)
                              | P_aux (P_var (P_aux (P_id id, _), _), _)
                              | P_aux (P_id id, _) ),
                              _,
                              body
                            ),
                          _
                        ),
                      _
                    ),
                  _
                ) ->
                (id, body)
            | _ -> raise (Reporting.err_unreachable l __POS__ ("Unable to find loop variable in " ^ string_of_exp body))
          in
          let from_exp_pp, to_exp_pp, step_exp_pp =
            (doc_exp false ctx from_exp, doc_exp false ctx to_exp, doc_exp false ctx step_exp)
          in
          let step_exp_pp = if is_true ord_exp then step_exp_pp else minus ^^ step_exp_pp in
          let loopvar_pp = doc_id_ctor ctx loopvar in
          let effects = has_effect body in
          let vartuple_pp, body_lambda = make_loop_vars ctx [loopvar_pp] vartuple in
          let body_lambda = if effects then body_lambda ^^ string " do" else body_lambda in
          let vars_pp, body_ctx = name_loop_vars ctx in
          let body_pp = doc_exp (as_monadic && effects) body_ctx body in
          let vars_dec_pp = string "let mut " ^^ vars_pp ^^ string " := " ^^ vartuple_pp in
          let loop_bracket = brackets (separate colon [from_exp_pp; to_exp_pp; step_exp_pp]) ^^ string "i" in
          let loop_head = flow (break 1) [string "for"; loopvar_pp; string "in"; loop_bracket; string "do"] in
          let arrow = if effects then leftarrowdo else coloneq in
          let loop_body_1 = string "let " ^^ vartuple_pp ^^ space ^^ coloneq ^^ space ^^ vars_pp in
          let loop_body = loop_body_1 ^^ hardline ^^ prefix 2 1 (vars_pp ^^ space ^^ arrow) body_pp in
          let full_loop = prefix 2 1 loop_head loop_body in
          separate hardline [vars_dec_pp; full_loop; wrap_with_pure as_monadic vars_pp]
      | _ -> raise (Reporting.err_unreachable l __POS__ "Unexpected number of arguments for loop combinator")
    )
  | E_for (loopvar, from_exp, to_exp, step_exp, Ord_aux (order, _), body) ->
      let combinator = match order with Ord_inc -> "foreach_Z_up" | Ord_dec -> "foreach_Z_down" in
      let from_exp_pp, to_exp_pp, step_exp_pp =
        (doc_exp false ctx from_exp, doc_exp false ctx to_exp, doc_exp false ctx step_exp)
      in
      let step_exp_pp = match order with Ord_inc -> step_exp_pp | Ord_dec -> minus ^^ step_exp_pp in
      let loop_bracket = brackets (separate colon [from_exp_pp; to_exp_pp; step_exp_pp]) ^^ string "i" in
      let loopvar_pp = doc_id_ctor ctx loopvar in
      let body_effect = has_effect body in
      let enter_monad = if body_effect then empty else string "Id.run" in
      let loop_head =
        flow (break 1) (remove_empties [enter_monad; string "for"; loopvar_pp; string "in"; loop_bracket; string "do"])
      in
      let loop_body = doc_exp body_effect ctx body in
      let full_loop = prefix 2 1 loop_head loop_body in
      full_loop
  | E_app ((Id_aux (Id "early_return", _) as f), [arg]) ->
      let throw = if ctx.in_sail_monad then string "SailME.throw " else string "throw " in
      nest 2 (throw ^^ d_of_arg ctx arg)
  | E_app (f, args) -> (
      let _, f_typ = Env.get_val_spec f env in
      let implicits = get_fn_implicits f_typ in
      let arg_names = Bindings.find_opt f ctx.global.fun_args in
      let arg_names = Option.value ~default:[] arg_names in
      let extern_id = if Env.is_extern f env "lean" then Some (Env.get_extern f env "lean") else None in
      let d_id = Option.fold ~some:string ~none:(doc_id_ctor ~ren_ctor:true ctx f) extern_id in
      let d_args = List.map (d_of_arg ctx) args in
      let d_imargs = doc_implicit_args arg_names implicits d_args in
      let d_args = List.map snd (List.filter (fun x -> not (fst x)) (List.combine implicits d_args)) in
      let fn_monadic = not (Effects.function_is_pure f ctx.global.effect_info) in
      match op_of_id extern_id with
      | `Binop op ->
          let e1 = List.nth d_args 0 in
          let e2 = List.nth d_args 1 in
          let res = e1 ^^ space ^^ string op ^^ space ^^ e2 in
          wrap_with_pure as_monadic (parens res) |> nest 2
      | `Unop op ->
          let e = List.nth d_args 0 in
          let res = string op ^^ space ^^ e in
          wrap_with_pure as_monadic (parens res) |> nest 2
      | `NotOp ->
          nest 2
            (wrap_with_left_arrow ((not as_monadic) && fn_monadic)
               (wrap_with_pure (as_monadic && not fn_monadic) (parens (flow (break 1) ((d_id :: d_imargs) @ d_args))))
            )
    )
  | E_vector vals ->
      if is_bitvector_typ (typ_of full_exp) then
        nest 2
          (wrap_with_pure as_monadic
             (parens (flow space [string "BitVec.join1"; brackets (separate_map comma_sp (d_of_arg ctx) vals)]))
          )
      else
        string "#v"
        ^^ wrap_with_pure as_monadic (brackets (nest 2 (separate_map comma_sp (d_of_arg ctx) (List.rev vals))))
  | E_typ (typ, e) ->
      if has_effect e then doc_exp as_monadic ctx e
      else wrap_with_pure as_monadic (parens (separate space [doc_exp false ctx e; colon; doc_typ ctx env typ]))
  | E_tuple es -> wrap_with_pure as_monadic (parens (separate_map (comma ^^ space) (d_of_arg ctx) es))
  | E_let (lpat, lexp, e') | E_internal_plet (lpat, lexp, e') ->
      let has_loop = has_loop lexp in
      let is_arrow_do = match e with E_let _ when not has_loop -> false | _ -> true in
      let id_typ = doc_pat ctx false lpat in
      let typ_ascription = doc_pat_typ_ascription ctx env lpat in
      let ctx = update_ctx_pat ctx lpat in
      let pp_let_line_f l = group (nest 2 (flow (break 1) l)) in
      let pp_let_line =
        if has_effect lexp || has_loop then
          if is_unit (typ_of lexp) && is_anonymous_pat lpat then doc_exp true ctx lexp
          else (
            match (is_arrow_do, typ_ascription) with
            | true, None -> pp_let_line_f [separate space [string "let"; id_typ; leftarrowdo]; doc_exp true ctx lexp]
            | false, None -> pp_let_line_f [separate space [string "let"; id_typ; leftarrow]; doc_exp true ctx lexp]
            | true, Some asc ->
                pp_let_line_f
                  ([
                     separate space [string "let"; id_typ; leftarrow; string "(("; string "do"];
                     doc_exp true ctx lexp;
                     string ")";
                     colon;
                   ]
                  @ prepend_monad ctx lexp asc
                  @ [string ")"]
                  )
            | false, Some asc ->
                pp_let_line_f
                  ([
                     separate space [string "let"; id_typ; leftarrow; string "(("];
                     doc_exp true ctx lexp;
                     string ")";
                     colon;
                   ]
                  @ prepend_monad ctx lexp asc
                  @ [string ")"]
                  )
          )
        else (
          match typ_ascription with
          | Some asc ->
              pp_let_line_f [separate space [string "let"; id_typ; colon; asc; coloneq]; doc_exp false ctx lexp]
          | None -> pp_let_line_f [separate space [string "let"; id_typ; coloneq]; doc_exp false ctx lexp]
        )
      in
      pp_let_line ^^ hardline ^^ doc_exp as_monadic ctx e'
  | E_internal_return e -> doc_exp false ctx e (* ??? *)
  | E_struct (_, fexps) ->
      let args = List.map d_of_field fexps in
      wrap_with_pure as_monadic (braces (space ^^ align (separate hardline args) ^^ space))
  | E_field (exp, id) ->
      (* TODO *)
      wrap_with_pure as_monadic (doc_exp false ctx exp ^^ dot ^^ doc_id_ctor ctx id)
  | E_struct_update (exp, fexps) ->
      let args = List.map d_of_field fexps in
      (* TODO *)
      wrap_with_pure as_monadic
        (braces (space ^^ doc_exp false ctx exp ^^ string " with " ^^ separate (comma ^^ space) args ^^ space))
  | E_match (discr, brs) ->
      let is_match_bv = is_match_bv brs in
      let as_monadic' =
        List.exists (fun x -> effectful (effect_of_annot (match x with Pat_aux (_, (_, annot)) -> annot))) brs
        || as_monadic
      in
      let cases = separate_map hardline (doc_match_clause is_match_bv as_monadic' ctx) brs in
      string (match_or_match_bv is_match_bv brs) ^^ d_of_arg ctx discr ^^ string " with" ^^ hardline ^^ cases
  | E_assign ((LE_aux (le_act, tannot) as le), e) ->
      wrap_with_left_arrow (not as_monadic)
        ( match le_act with
        | LE_id id | LE_typ (_, id) -> string "writeReg " ^^ doc_id_ctor ctx id ^^ space ^^ d_of_arg ctx e
        | LE_deref e' -> string "writeRegRef " ^^ d_of_arg ctx e' ^^ space ^^ d_of_arg ctx e
        | _ -> failwith ("assign " ^ string_of_lexp le ^ "not implemented yet")
        )
  | E_if (i, t, e) ->
      let statements_monadic = as_monadic || has_effect t || has_effect e in
      nest 2 (string "if (" ^^ nest 1 (d_of_arg ctx i) ^^ string " : Bool)")
      ^^ hardline
      ^^ prefix 2 1 (string "then") (wrap_exp statements_monadic ctx t)
      ^^ hardline
      ^^ prefix 2 1 (string "else") (wrap_exp statements_monadic ctx e)
      |> wrap_with_left_arrow (statements_monadic && not as_monadic)
  | E_ref id -> parens (string ".Reg " ^^ doc_id_ctor ctx id)
  | E_exit _ -> string "throw Error.Exit"
  | E_throw e ->
      let arrow = if as_monadic then empty else leftarrow in
      arrow ^^ string "sailThrow " ^^ parens (doc_exp false ctx e)
  | E_try (e, cases) ->
      let x = E_aux (E_id (Id_aux (Id "the_exception", Unknown)), (Unknown, annot)) in
      let cases = nest 2 (doc_exp true ctx (E_aux (E_match (x, cases), (Unknown, annot)))) in
      let try_catch = if has_early_return e then string "sailTryCatchE " else string "sailTryCatch " in
      let arrow = if as_monadic then empty else leftarrow in
      nest 2
        (arrow ^^ try_catch
        ^^ parens (d_of_arg ~with_arrow:false ctx e)
        ^^ space
        ^^ parens (string "fun the_exception => " ^^ hardline ^^ cases)
        )
  | E_assert (e1, e2) -> string "sail_assert " ^^ d_of_arg ctx e1 ^^ space ^^ d_of_arg ctx e2
  | E_list es -> brackets (separate_map comma_sp (doc_exp as_monadic ctx) es)
  | E_cons (hd_e, tl_e) -> parens (separate space [doc_exp false ctx hd_e; string "::"; doc_exp false ctx tl_e])
  | _ -> failwith ("Expression " ^ string_of_exp_con full_exp ^ " " ^ string_of_exp full_exp ^ " not translatable yet.")

and doc_fexp with_arrow ctx (FE_aux (FE_fexp (field, e), _)) =
  let arrow = if with_arrow then leftarrow ^^ space else empty in
  doc_id_ctor ctx field ^^ string " := " ^^ arrow ^^ nest 2 (doc_exp with_arrow ctx e)

let doc_binder ctx env i t =
  let parenthesizer =
    match t with
    | Typ_aux (Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var ki, _)), _)]), _) ->
        implicit_parens
    | _ -> parens
  in
  (* Overwrite the id if it's captured *)
  let ctx = match captured_typ_var (i, t) with Some (i, ki) -> add_single_kid_id_rename ctx i ki | _ -> ctx in
  (ctx, separate space [doc_id_ctor ctx i; colon; doc_typ ctx env t] |> parenthesizer)

(** Find all patterns in the arguments of the sail function that Lean cannot handle in a [def], and add them as let
    bindings in the prelude of the translation of the function. This assumes that the pattern is irrefutable. *)
let add_function_pattern ctx fixup_binders (P_aux (pat, pat_annot) as pat_full) var typ =
  match pat with
  | P_id _ | P_typ (_, P_aux (P_id _, _)) | P_tuple [] | P_lit _ | P_wild -> fixup_binders
  | _ ->
      fun (E_aux (_, body_annot) as body : tannot exp) ->
        E_aux (E_let (pat_full, E_aux (E_id var, (Unknown, mk_tannot ctx.env typ)), body), body_annot) |> fixup_binders

(** Find all the [int] and [atom] types in the function pattern and express them as paths that use the lean variables,
    so that we can use them in the return type of the function. For example, see the function [two_tuples_atom] in the
    test case test/lean/typquant.sail. *)
let rec add_path_renamings ~path ctx (P_aux (pat, pat_annot)) (Typ_aux (typ, typ_annot) as typ_full) =
  match (pat, typ) with
  | P_tuple pats, Typ_tuple typs ->
      List.fold_left
        (fun (ctx, i) (pat, typ) -> (add_path_renamings ~path:(Printf.sprintf "%s.%i" path i) ctx pat typ, i + 1))
        (ctx, 1) (List.combine pats typs)
      |> fst
  | P_id id, typ -> (
      match captured_typ_var (id, typ_full) with
      | Some (_, kid) -> add_single_kid_id_rename ctx (mk_id path) kid
      | None -> ctx
    )
  | _ -> ctx

let doc_funcl_init global (FCL_aux (FCL_funcl (id, pexp), annot)) =
  let env = env_of_tannot (snd annot) in
  let tq, typ = Env.get_val_spec_orig id env in
  let arg_typs, ret_typ, _ =
    match typ with
    | Typ_aux (Typ_fn (arg_typs, ret_typ), _) -> (arg_typs, ret_typ, no_effect)
    | _ -> failwith ("Function " ^ string_of_id id ^ " does not have function type")
  in
  let pat, _, exp, _ = destruct_pexp pexp in
  let pats, fixup_binders = untuple_args_pat arg_typs pat in
  let binders : (tannot pat * id * typ) list =
    pats
    |> List.mapi (fun i (pat, typ) ->
        match pat_is_plain_binder ~suffix:(Printf.sprintf "_%i" i) env pat with
        | Some (Some id, _) -> (pat, id, typ)
        | Some (None, _) ->
            (pat, mk_id ~loc:(pat_loc pat) (Printf.sprintf "x_%i" i), typ)
            (* TODO fresh name or wildcard instead of x *)
        | _ ->
            ( pat,
              Id_aux (Id "TODO_ARG_PATTERN", Unknown),
              Typ_aux (Typ_id (Id_aux (Id "TODO_ARG_PATTERN", Unknown)), Unknown)
            )
        (*failwith "Argument pattern not translatable yet."*)
    )
  in
  let ctx = context_init env global in
  let ctx, binders, fixup_binders =
    List.fold_left
      (fun (ctx, bs, fixup_binders) (pat, i, t) ->
        let ctx, d = doc_binder ctx env i t in
        let fixup_binders = add_function_pattern ctx fixup_binders pat i t in
        let ctx = add_path_renamings ~path:(string_of_id i) ctx pat t in
        (ctx, bs @ [d], fixup_binders)
      )
      (ctx, [], fixup_binders) binders
  in
  let typ_quant_comment = doc_typ_quant_in_comment ctx env tq in
  (* Use auto-implicits for type quanitifiers for now and see if this works *)
  let doc_ret_typ_orig = doc_typ ctx env ret_typ in
  let is_monadic = not (Effects.function_is_pure id ctx.global.effect_info) in
  let early_return = has_early_return exp in
  let has_loop = has_loop exp in
  (* Add monad for stateful functions *)
  let doc_ret_typ = if is_monadic then string "SailM " ^^ doc_ret_typ_orig else doc_ret_typ_orig in
  let decl_val = [doc_ret_typ; coloneq] in
  (* Add do block for stateful functions *)
  let dec_val_end =
    match (is_monadic, early_return, has_loop) with
    | true, true, _ -> [string "SailME.run"; string "do"]
    | true, _, _ -> [string "do"]
    | false, false, true -> [string "Id.run"; string "do"]
    | false, true, _ -> [string "ExceptM.run"; string "do"]
    | _ -> []
  in
  let ctx =
    { ctx with in_sail_monad = is_monadic; in_except_monad = (if early_return then Some doc_ret_typ_orig else None) }
  in
  let decl_val = decl_val @ dec_val_end in
  let partiality = if IdSet.mem id !opt_partial_functions then string "partial" else empty in
  let computability = if IdSet.mem id !opt_noncomputable_functions then string "noncomputable" else empty in
  ( typ_quant_comment,
    separate space
      (remove_empties [partiality; computability; string "def"; doc_id_ctor ctx id] @ binders @ [colon] @ decl_val),
    ctx,
    fixup_binders
  )

let mapping_regex = Str.regexp "_\\(forward\\|backwards\\)\\(_matches\\)?$"

(* Mappings with string concatenation on the LHS are not translated to
executable code by sail, so we detect the pattern to replace the forward mapping
direction by a function that throws an exception. cf #260 *)
let untranslatable_mapping id exp =
  let rec exp_disc e =
    match e with
    | E_aux (E_let (_, _, e), _) -> exp_disc e
    | E_aux (E_app (_, [E_aux (E_exit _, _)]), _) -> true
    | _ -> false
  in
  let rec exp_match e =
    match e with E_aux (E_let (_, _, e), _) -> exp_match e | E_aux (E_match (e, _), _) -> exp_disc e | _ -> false
  in

  let id = string_of_id id in
  if Str.string_match mapping_regex id 0 then false else exp_match exp

let doc_funcl_body fixup_binders ctx (FCL_aux (FCL_funcl (id, pexp), annot)) =
  let env = env_of_tannot (snd annot) in
  let _, _, exp, _ = destruct_pexp pexp in
  (* If an argument was [x : (Int, Int)], which is transformed to [(arg0: Int) (arg1: Int)],
     this adds a let binding at the beginning of the function, of the form [let x := (arg0, arg1)] *)
  let exp = fixup_binders exp in
  let is_monadic = has_effect exp || not (Effects.function_is_pure id ctx.global.effect_info) in
  if untranslatable_mapping id exp then string "throw Error.Exit" else doc_exp is_monadic (context_with_env ctx env) exp

let doc_termination fixup_binders ctx fnpat (Rec_aux (meas, _)) =
  match meas with
  | Rec_nonrec | Rec_rec -> empty
  | Rec_measure (pat, exp) ->
      (* TODO: actually use the pattern *)
      let term =
        doc_exp false ctx
          (fixup_binders
             (E_aux
                ( E_let (pat, Rewrites.pat_to_exp (env_of_pat fnpat) fnpat, exp),
                  (Unknown, mk_tannot ctx.env (typ_of exp))
                )
             )
          )
      in
      let term_by = string "termination_by " ^^ parens term ^^ string ".toNat" in
      hardline ^^ term_by

let pat_of_funcl (FCL_aux (FCL_funcl (_, funcl), _)) =
  match funcl with Pat_aux (Pat_exp (pat, _), _) -> pat | Pat_aux (Pat_when (pat, _, _), _) -> pat

let doc_funcl ctx meas funcl =
  let comment, signature, ctx, fixup_binders = doc_funcl_init ctx.global funcl in
  let fnpat = pat_of_funcl funcl in
  let termination = doc_termination fixup_binders ctx fnpat meas in
  comment ^^ nest 2 (signature ^^ hardline ^^ doc_funcl_body fixup_binders ctx funcl) ^^ termination

let string_of_pexp p =
  let pat, guard, exp, _ = destruct_pexp p in
  let guard_str = match guard with None -> "" | Some guard -> " if " ^ string_of_exp guard in
  "| " ^ string_of_pat pat ^ guard_str ^ " -> " ^ string_of_exp exp ^ "\n"

let doc_fundef ctx (FD_aux (FD_function (meas, typa, fcls), fannot) as full_fundef) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [funcl] -> doc_funcl ctx meas funcl
  | funcls ->
      failwith
        (List.fold_left
           (fun acc (FCL_aux (FCL_funcl (id, pexp), annot)) -> acc ^ string_of_pexp pexp)
           "FD_function with more than one clause :\n" funcls
        )

let doc_type_union ctx (Tu_aux (Tu_ty_id (ty, i), _)) =
  nest 2 (flow space [pipe; doc_id_ctor ctx i; parens (flow space [underscore; colon; doc_typ ctx ctx.env ty])])

let string_of_type_def_con (TD_aux (td, _)) =
  match td with
  | TD_abbrev _ -> "TD_abbrev"
  | TD_record _ -> "TD_record"
  | TD_variant _ -> "TD_variant"
  | TD_abstract _ -> "TD_abstract"
  | TD_bitfield _ -> "TD_bitfield"
  | TD_enum _ -> "TD_enum"

let doc_typdef ctx (TD_aux (td, tannot) as full_typdef) =
  match td with
  | TD_enum (id, members, _) ->
      let ids = List.map fst members in
      let ids = List.map (doc_id_ctor ctx) ids in
      let ids = List.map (fun i -> space ^^ pipe ^^ space ^^ i) ids in
      let derivers = if List.length ids == 0 then [string "Repr"] else [string "Inhabited"; string "Repr"] in
      let derivers = if IdSet.mem id !non_beq_types then derivers else string "BEq" :: derivers in
      let enums_doc = concat ids in
      let _ = opens := IdSet.add id !opens in
      let id = doc_id_ctor ctx id in
      nest 2
        (flow (break 1) [string "inductive"; id; string "where"]
        ^^ enums_doc ^^ hardline ^^ string "deriving" ^^ space ^^ separate comma_sp derivers ^^ hardline
        ^^ string "open" ^^ space ^^ id
        )
  | TD_record (id, tq, fields, _) ->
      let fields = List.map (doc_typ_id ctx ctx.env) fields in
      let fields_doc = separate hardline fields in
      let rectyp = doc_typ_quant_relevant ctx tq in
      let rectyp = List.map (fun d -> parens d) rectyp |> separate space in
      let derivers = [string "Inhabited"; string "Repr"] in
      let derivers = if IdSet.mem id !non_beq_types then derivers else string "BEq" :: derivers in
      doc_typ_quant_in_comment ctx ctx.env tq
      ^^ nest 2
           (flow (break 1) (remove_empties [string "structure"; doc_id_ctor ctx id; rectyp; string "where"])
           ^^ hardline ^^ fields_doc ^^ hardline ^^ string "deriving" ^^ space ^^ separate comma_sp derivers
           )
  | TD_abbrev (id, tq, A_aux (A_typ (Typ_aux (Typ_app (Id_aux (Id "range", _), _), _) as t), _)) ->
      let vars = doc_typ_quant_relevant ctx tq in
      let vars = List.map parens vars in
      let vars = separate space vars in
      nest 2
        (flow (break 1) (remove_empties [string "abbrev"; doc_id_ctor ctx id; vars; coloneq; doc_typ ctx ctx.env t]))
  | TD_abbrev (id, tq, A_aux (A_typ t, _)) when string_of_id id = "fp_bits" ->
      string (Printf.sprintf "-- Abbreviation %s skipped" (string_of_id id)) (* FIXME *)
  | TD_abbrev (id, tq, A_aux (A_typ t, _)) ->
      let vars = doc_typ_quant_only_vars ctx tq in
      let vars = separate space vars in
      nest 2
        (flow (break 1) (remove_empties [string "abbrev"; doc_id_ctor ctx id; vars; coloneq; doc_typ ctx ctx.env t]))
  | TD_abbrev (id, tq, A_aux (A_nexp ne, _)) ->
      let vars = doc_typ_quant_relevant ctx tq in
      let vars = List.map parens vars in
      let vars = separate space vars in
      nest 2
        (flow (break 1)
           [string "abbrev"; doc_id_ctor ctx id; vars; colon; string "Int"; coloneq; doc_nexp ctx ctx.env ne]
        )
  | TD_abbrev (id, tq, A_aux (A_bool nc, _)) ->
      let vars = doc_typ_quant_relevant ctx tq in
      let vars = List.map parens vars in
      let vars = separate space vars in
      nest 2
        (flow (break 1)
           [string "abbrev"; doc_id_ctor ctx id; vars; colon; string "Bool"; coloneq; doc_nconstraint ctx ctx.env nc]
        )
  | TD_variant (id, tq, ar, _) ->
      let pp_tus = concat (List.map (fun tu -> hardline ^^ doc_type_union ctx tu) ar) in
      let rectyp = doc_typ_quant_relevant ctx tq in
      let rectyp = List.map (fun d -> parens d) rectyp |> separate space in
      let _ = opens := IdSet.add id !opens in
      let derivers = [string "Repr"] in
      let derivers = if IdSet.mem id !non_beq_types then derivers else string "BEq" :: derivers in
      let derivers = if List.length ar == 0 then derivers else string "Inhabited" :: derivers in
      doc_typ_quant_in_comment ctx ctx.env tq
      ^^ nest 2
           (nest 2 (flow space (remove_empties [string "inductive"; doc_id_ctor ctx id; rectyp; string "where"]))
           ^^ pp_tus ^^ hardline ^^ string "deriving" ^^ space ^^ separate comma_sp derivers ^^ hardline
           ^^ string "open" ^^ space ^^ doc_id_ctor ctx id
           )
  | _ -> failwith ("Type definition " ^ string_of_type_def_con full_typdef ^ " not translatable yet.")

(* Copied from the Coq PP *)
let doc_val ctx pat exp =
  let global, id, pat_typ =
    match pat with
    | P_aux (P_typ (typ, P_aux (P_id id, _)), _) -> (ctx.global, id, Some typ)
    | P_aux (P_id id, _) -> (ctx.global, id, None)
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)), _) when Id.compare id (id_of_kid kid) == 0 ->
        let global = add_global_kid_id_rename ctx.global id kid in
        (global, id, None)
    | P_aux (P_typ (typ, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)), _)), _)
      when Id.compare id (id_of_kid kid) == 0 ->
        let global = add_global_kid_id_rename ctx.global id kid in
        (global, id, Some typ)
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_app (app_id, [TP_aux (TP_var kid, _)]), _)), _)
      when Id.compare app_id (mk_id "atom") == 0 && Id.compare id (id_of_kid kid) == 0 ->
        let global = add_global_kid_id_rename ctx.global id kid in
        (global, id, None)
    | P_aux
        (P_typ (typ, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_app (app_id, [TP_aux (TP_var kid, _)]), _)), _)), _)
      when Id.compare app_id (mk_id "atom") == 0 && Id.compare id (id_of_kid kid) == 0 ->
        let global = add_global_kid_id_rename ctx.global id kid in
        (global, id, Some typ)
    | _ -> failwith ("Pattern " ^ string_of_pat_con pat ^ " " ^ string_of_pat pat ^ " not translatable yet.")
  in
  let typpp = match pat_typ with None -> empty | Some typ -> space ^^ colon ^^ space ^^ doc_typ ctx ctx.env typ in
  let idpp = doc_id_ctor ctx id in
  let base_pp =
    if has_effect exp then string "unwrapValue" ^^ space ^^ parens (doc_exp true ctx exp) else doc_exp false ctx exp
  in
  (global, nest 2 (group (string "def" ^^ space ^^ idpp ^^ typpp ^^ space ^^ coloneq ^/^ base_pp)))

let should_print_function_def def =
  match def with
  | DEF_aux (DEF_fundef fdef, dannot) -> not (Env.is_extern (id_of_fundef fdef) dannot.env "lean")
  | DEF_aux (DEF_let (pat, exp), _) -> true
  | _ -> false

let rec doc_defs_rec ctx defs types (former_funcs : document list) (docdefs : document) =
  match defs with
  | [] -> (types, former_funcs @ [docdefs])
  | DEF_aux (DEF_fundef fdef, dannot) :: defs' ->
      let env = dannot.env in
      let pp_f =
        if Env.is_extern (id_of_fundef fdef) env "lean" then docdefs
        else docdefs ^^ group (doc_fundef ctx fdef) ^/^ hardline
      in
      doc_defs_rec ctx defs' types former_funcs pp_f
  | DEF_aux (DEF_internal_mutrec fdefs, dannot) :: defs' ->
      let funs = separate_map hardline (fun fdef -> doc_fundef ctx fdef) fdefs in
      let res = string "mutual" ^^ hardline ^^ funs ^^ hardline ^^ string "end" ^^ hardline in
      doc_defs_rec ctx defs' types former_funcs (docdefs ^^ hardline ^^ res ^^ hardline)
  | DEF_aux (DEF_type tdef, _) :: defs' when List.mem (string_of_id (id_of_type_def tdef)) !opt_extern_types ->
      doc_defs_rec ctx defs' types former_funcs docdefs
  | DEF_aux (DEF_type tdef, _) :: defs' ->
      doc_defs_rec ctx defs' (types ^^ group (doc_typdef ctx tdef) ^/^ hardline) former_funcs docdefs
  | DEF_aux (DEF_let (pat, exp), _) :: defs' ->
      let global, pp_val = doc_val ctx pat exp in
      let ctx = { ctx with global } in
      doc_defs_rec ctx defs' types former_funcs (docdefs ^^ group pp_val ^/^ hardline)
  | DEF_aux (DEF_pragma ("include_start", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("file_start", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("include_end", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("file_end", Pragma_line (file, _)), _) :: defs'
    when Filename.check_suffix file ".sail" ->
      if docdefs = empty then doc_defs_rec ctx defs' types former_funcs docdefs
      else doc_defs_rec ctx defs' types (former_funcs @ [docdefs]) empty
  | d :: defs' ->
      if should_print_function_def d then failwith "this case of doc_defs_rec should be unreachable"
      else doc_defs_rec ctx defs' types former_funcs docdefs

let doc_defs ctx defs = doc_defs_rec ctx defs empty [] empty

let add_node_to_map_and_ref_set (cg : Callgraph.callgraph) (map : int Bindings.t) (acc : IntSet.t) (idx : int)
    (m : Callgraph.node) =
  let map = Bindings.add (Callgraph.node_id m) idx map in
  let deps = Callgraph.G.children cg m in
  let deps : int list = List.filter_map (fun n -> Bindings.find_opt (Callgraph.node_id n) map) deps in
  let acc = List.fold_left (fun map i -> if i < idx then IntSet.add i map else map) acc deps in
  (map, acc)

let add_def_to_map_and_ref_set cg map acc idx (d : (tannot, env) def) =
  let is = Callgraph.nodes_of_def d in
  Callgraph.NodeSet.fold (fun n (map, acc) -> add_node_to_map_and_ref_set cg map acc idx n) is (map, acc)

let rec collect_imports_rec (cg : Callgraph.callgraph) (defs : (tannot, env) def list) (map : int Bindings.t)
    (accs : IntSet.t list) (acc : IntSet.t) (idx : int) (nonempty_print : bool) : IntSet.t list =
  match defs with
  | [] -> accs @ [acc]
  | (DEF_aux ((DEF_fundef _ | DEF_internal_mutrec _ | DEF_let _), _) as d) :: defs' ->
      let map, acc = add_def_to_map_and_ref_set cg map acc idx d in
      collect_imports_rec cg defs' map accs acc idx true
  | DEF_aux (DEF_type tdef, _) :: defs' -> collect_imports_rec cg defs' map accs acc idx nonempty_print
  | DEF_aux (DEF_pragma ("include_start", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("file_start", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("include_end", Pragma_line (file, _)), _) :: defs'
  | DEF_aux (DEF_pragma ("file_end", Pragma_line (file, _)), _) :: defs'
    when Filename.check_suffix file ".sail" ->
      if not nonempty_print then collect_imports_rec cg defs' map accs acc idx nonempty_print
      else collect_imports_rec cg defs' map (accs @ [acc]) IntSet.empty (idx + 1) false
  | d :: defs' ->
      if should_print_function_def d then failwith "this case of collect_imports_rec should be unreachable"
      else collect_imports_rec cg defs' map accs acc idx nonempty_print

let collect_imports (cg : Callgraph.callgraph) (defs : (tannot, env) def list) =
  collect_imports_rec cg defs Bindings.empty [] IntSet.empty 0 false

(* Remove all imports for now, they will be printed in other files. Probably just for testing. *)
let rec remove_imports (defs : (Libsail.Type_check.tannot, Libsail.Type_check.env) def list) depth =
  match defs with
  | [] -> []
  | DEF_aux (DEF_pragma ("include_start", _), _) :: ds -> remove_imports ds (depth + 1)
  | DEF_aux (DEF_pragma ("include_end", _), _) :: ds -> remove_imports ds (depth - 1)
  | d :: ds -> if depth > 0 then remove_imports ds depth else d :: remove_imports ds depth

let add_reg_typ typ_map (typ, id, _) =
  let typ_id = State.id_of_regtyp IdSet.empty typ in
  Bindings.add typ_id (id, typ) typ_map

let register_enums ctx registers =
  opens := IdSet.add (mk_id "Register") !opens;
  separate hardline
    [
      string "inductive Register : Type where";
      separate_map hardline (fun (_, id, _) -> string "  | " ^^ doc_id_ctor ctx id) registers;
      string "  deriving DecidableEq, Hashable, Repr";
      string "open Register";
      empty;
    ]

let type_enum ctx registers =
  separate hardline
    [
      string "abbrev RegisterType : Register → Type";
      separate_map hardline
        (fun (typ, id, _) -> string "  | ." ^^ doc_id_ctor ctx id ^^ string " => " ^^ doc_typ ctx ctx.env typ)
        registers;
      empty;
    ]

let inhabit_enum_v2 ctx typ_map =
  separate_map hardline
    (fun (_, (id, typ)) ->
      string "instance : Inhabited (RegisterRef "
      ^^ doc_typ ctx ctx.env typ ^^ string ") where" ^^ hardline ^^ string "  default := .Reg " ^^ doc_id_ctor ctx id
    )
    typ_map

let inhabit_enum_v1 ctx typ_map =
  separate_map hardline
    (fun (_, (id, typ)) ->
      string "instance : Inhabited (RegisterRef RegisterType "
      ^^ doc_typ ctx ctx.env typ ^^ string ") where" ^^ hardline ^^ string "  default := .Reg " ^^ doc_id_ctor ctx id
    )
    typ_map

let doc_reg_info env global registers =
  let ctx = context_init env global in
  separate hardline [register_enums ctx registers; type_enum ctx registers; empty]

let doc_monad_abbrev ~version defs =
  let find_exc_typ defs =
    let is_exc_typ_def = function
      | DEF_aux (DEF_type td, _) -> string_of_id (id_of_type_def td) = "exception"
      | _ -> false
    in
    if List.exists is_exc_typ_def defs then empty else string "abbrev exception := Unit\n"
  in
  let excdef = find_exc_typ defs in
  let pp_register_type =
    if version = 1 then string "PreSailM RegisterType trivialChoiceSource exception" else string "PreSailM exception"
  in
  let pp_register_type_e =
    if version = 1 then string "PreSailME RegisterType trivialChoiceSource exception" else string "PreSailME exception"
  in
  let monad = separate space [string "abbrev"; string "SailM"; coloneq; pp_register_type] in
  let monad_e =
    separate space [string "abbrev"; string "SailME"; coloneq; pp_register_type_e] ^^ hardline ^^ hardline
  in
  separate hardline (remove_empties [excdef; monad; monad_e])

let doc_instantiations_v1 ctx env defs registers =
  let params = Monad_params.find_monad_parameters env in
  let arch =
    match params with
    | None -> empty
    | Some params ->
        nest 2
          (separate hardline
             [
               string "instance : Arch where";
               string "va_size := 64";
               string "pa := " ^^ doc_typ ctx env params.pa_type;
               string "abort := " ^^ doc_typ ctx env params.abort_type;
               string "translation := " ^^ doc_typ ctx env params.translation_summary_type;
               string "trans_start := " ^^ doc_typ ctx env params.trans_start_type;
               string "trans_end := " ^^ doc_typ ctx env params.trans_end_type;
               string "fault := " ^^ doc_typ ctx env params.fault_type;
               string "tlb_op := " ^^ doc_typ ctx env params.tlbi_type;
               string "cache_op := " ^^ doc_typ ctx env params.cache_op_type;
               string "barrier := " ^^ doc_typ ctx env params.barrier_type;
               string "arch_ak := " ^^ doc_typ ctx env params.arch_ak_type;
               string "sys_reg_id := " ^^ doc_typ ctx env params.sys_reg_id_type ^^ hardline;
             ]
          )
        ^^ hardline
  in
  let type_map = List.fold_left add_reg_typ Bindings.empty registers in
  let type_map = Bindings.bindings type_map in
  separate hardline [arch; empty; doc_monad_abbrev ~version:1 defs; empty; inhabit_enum_v1 ctx type_map]

let doc_instantiations_v2 ctx defs registers =
  let has_regs = registers != [] in
  let type_substs, id_substs = Monad_params.find_instantiations defs in
  let ts x d =
    KBindings.find_opt (mk_kid x) type_substs |> Option.fold ~none:(string d) ~some:(doc_typ_app ctx ctx.env)
  in
  let is x =
    Bindings.find_opt (mk_id x) id_substs |> Option.fold ~none:(string "fun _ => false") ~some:(doc_id_ctor ctx)
  in
  let pr ?(d = "Unit") x = string (x ^ " := ") ^^ ts x d in
  let fn x = string (x ^ " := ") ^^ is x in
  let arch =
    string "@[reducible]" ^^ hardline
    ^^ nest 2
         (separate hardline
            [
              string "instance : Arch where";
              pr "addr_size" ~d:"64";
              pr "addr_space";
              pr "CHERI" ~d:"false";
              pr "cap_size_log" ~d:"0";
              pr "register" ~d:"Register";
              pr "register_type" ~d:"RegisterType";
              pr "mem_acc";
              fn "mem_acc_is_explicit";
              fn "mem_acc_is_ifetch";
              fn "mem_acc_is_ttw";
              fn "mem_acc_is_relaxed";
              fn "mem_acc_is_rel_acq_rcpc";
              fn "mem_acc_is_rel_acq_rcsc";
              fn "mem_acc_is_standalone";
              fn "mem_acc_is_exclusive";
              fn "mem_acc_is_atomic_rmw";
              pr "trans_start";
              pr "trans_end";
              pr "abort";
              pr "barrier";
              pr "cache_op";
              pr "tlbi";
              pr "exn";
              pr "sys_reg_id";
            ]
         )
  in
  let type_map = List.fold_left add_reg_typ Bindings.empty registers in
  let type_map = Bindings.bindings type_map in
  separate hardline [arch; empty; doc_monad_abbrev ~version:2 defs; empty; inhabit_enum_v2 ctx type_map]
(* let doc_monad_abbrev env global registers defs (has_registers : bool) = *)

let doc_instantiations symbols ctx env defs regs =
  if Preprocess.have_symbol "CONCURRENCY_INTERFACE_V2" symbols then doc_instantiations_v2 ctx defs regs
  else doc_instantiations_v1 ctx env defs regs

let main_function_stub effect_info has_registers =
  let open Effects in
  let main_function =
    if Option.fold ~none:false ~some:effectful (Bindings.find_opt (mk_id "main") effect_info.functions) then "sail_main"
    else "(λ() ↦ (pure (sail_main ()) : SailM Unit))"
  in
  let main_call = if has_registers then Printf.sprintf "(sail_model_init >=> %s)" main_function else main_function in
  nest 2
    (separate hardline
       [
         string "def main (_ : List String) : IO UInt32 := do";
         Printf.ksprintf string "main_of_sail_main default %s" main_call;
         empty;
       ]
    )

let populate_fun_args defs =
  let add_args args (DEF_aux (d, _)) =
    match d with
    | DEF_fundef (FD_aux (FD_function (_, _, [FCL_aux (FCL_funcl (id, Pat_aux (Pat_exp (P_aux (p, _), _), _)), _)]), _))
      -> (
        match p with
        | P_tuple ps ->
            let arg =
              List.map
                (fun (P_aux (p, _)) ->
                  match p with P_id id | P_typ (_, P_aux (P_id id, _)) -> string_of_id id | _ -> ""
                )
                ps
            in
            Bindings.add id arg args
        | P_id arg -> Bindings.add id [string_of_id arg] args
        | P_typ (_, P_aux (P_id arg, _)) -> Bindings.add id [string_of_id arg] args
        | _ -> args
      )
    | _ -> args
  in
  List.fold_left (fun args d -> add_args args d) Bindings.empty defs

let rec collect_import_files_aux defs file_stack last_namespace ret =
  match defs with
  | [] -> ret
  | DEF_aux (DEF_pragma ("include_start", Pragma_line (file, _)), _) :: ds
  | DEF_aux (DEF_pragma ("file_start", Pragma_line (file, _)), _) :: ds
    when Filename.check_suffix file ".sail" ->
      collect_import_files_aux ds (file :: file_stack) last_namespace ret
  | DEF_aux (DEF_pragma ("include_end", Pragma_line (file, _)), _) :: ds
  | DEF_aux (DEF_pragma ("file_end", Pragma_line (file, _)), _) :: ds
    when Filename.check_suffix file ".sail" -> (
      match file_stack with
      | f :: fs -> collect_import_files_aux ds fs last_namespace ret
      | _ -> failwith "should not be reachable"
    )
  | d :: ds -> (
      match file_stack with
      | f :: _ ->
          if should_print_function_def d && not (last_namespace = Some f) then
            collect_import_files_aux ds file_stack (Some f) (ret @ [f])
          else collect_import_files_aux ds file_stack last_namespace ret
      | _ -> failwith "should not be reachable"
    )

let collect_import_files defs base =
  let res = collect_import_files_aux defs [base] None [] in
  if res = [] then [base] else res

(* Computes the constructors which have the same name as a type, and associate them with
their types so that we can prefix them in the output. *)
let compute_ctor_renames (env : Type_check.env) =
  (* let print_tu tu = Printf.printf "-> %s\n" (type_union_id tu |> string_of_id) in *)
  let variants = Env.get_variants env in
  (* list of (typ, ctor) *)
  let ctors =
    Bindings.fold
      (fun id (_, tus) acc ->
        List.fold_left (fun acc tu -> Bindings.add (type_union_id tu) (string_of_id id) acc) acc tus
      )
      variants Bindings.empty
  in
  Bindings.filter (fun ctor typ -> Env.bound_typ_id env ctor) ctors

let pp_ast_lean symbols (env : Type_check.env) effect_info ({ defs; _ } as ast : Libsail.Type_check.typed_ast)
    out_name_camel types_file imp_funcs_files funcs_file =
  let regs = State.find_registers defs in
  let fun_args = populate_fun_args defs in
  let ctor_renames = compute_ctor_renames env in
  let global =
    {
      effect_info;
      fun_args;
      ctor_renames;
      kid_id_renames = KBindings.empty;
      kid_id_renames_rev = Bindings.empty;
      out_name_camel;
      defined_functions = Env.get_defined_val_specs env;
    }
  in
  let ctx = context_init env global in
  let inst_defs, defs = Callgraph.partition_instantiation_definitions false defs in
  let ast = { ast with defs } in
  let _, instantiation_deps = doc_defs ctx inst_defs in
  let instantiation_deps =
    match instantiation_deps with [x] -> x | _ -> failwith "expected a single block of instantiation defs"
  in
  let instantiations = doc_instantiations symbols ctx env defs regs in
  let has_registers = List.length regs > 0 in
  let register_refs =
    if has_registers then doc_reg_info env global regs
    else string "abbrev Register := PEmpty\nabbrev RegisterType : Register -> Type := PEmpty.elim\n\n"
  in
  let types, all_fundefss = doc_defs ctx defs in
  let imp_fundefss, main_fundefs =
    if imp_funcs_files = [] then ([], concat all_fundefss) else (Util.butlast all_fundefss, Util.last all_fundefss)
  in
  let main_fundefs = main_fundefs ^^ string ("end " ^ out_name_camel ^ ".Functions") ^^ hardline in
  let main_function =
    if !the_main_function_has_been_seen then (
      let stub = main_function_stub effect_info has_registers in
      [string ("open " ^ out_name_camel); string ("open " ^ out_name_camel ^ ".Functions\n\n") ^^ stub]
    )
    else []
  in
  let opens = IdSet.fold (fun id doc -> string "open " ^^ doc_id_ctor ctx id ^^ hardline ^^ doc) !opens empty in
  print types_file (types ^^ register_refs ^^ instantiation_deps ^^ instantiations);
  let _ =
    List.map2
      (fun file defs -> print ~len:!opt_line_width file (separate hardline (remove_empties [opens; defs])))
      imp_funcs_files imp_fundefss
  in
  print ~len:!opt_line_width funcs_file (separate hardline (remove_empties ([opens; main_fundefs] @ main_function)));
  !the_main_function_has_been_seen
