(* ========================================================================= *)
(* Simplistic HOL Light prettyprinter, using the OCaml "Format" library.     *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2017                         *)
(*     (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018              *)
(* ========================================================================= *)

needs "nets.ml";;

(* ------------------------------------------------------------------------- *)
(* Character discrimination.                                                 *)
(* ------------------------------------------------------------------------- *)

let isspace,issep,isbra,issymb,isalpha,isnum,isalnum =
  let charcode s = Char.code(String.get s 0) in
  let spaces = " \t\n\r"
  and separators = ",;"
  and brackets = "()[]{}"
  and symbs = "\\!@#$%^&*-+|\\<=>/?~.:"
  and alphas = "'abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ"
  and nums = "0123456789" in
  let allchars = spaces^separators^brackets^symbs^alphas^nums in
  let csetsize = itlist (max o charcode) (explode allchars) 256 in
  let ctable = Array.make csetsize 0 in
  do_list (fun c -> Array.set ctable (charcode c) 1) (explode spaces);
  do_list (fun c -> Array.set ctable (charcode c) 2) (explode separators);
  do_list (fun c -> Array.set ctable (charcode c) 4) (explode brackets);
  do_list (fun c -> Array.set ctable (charcode c) 8) (explode symbs);
  do_list (fun c -> Array.set ctable (charcode c) 16) (explode alphas);
  do_list (fun c -> Array.set ctable (charcode c) 32) (explode nums);
  let isspace c = Array.get ctable (charcode c) = 1
  and issep c  = Array.get ctable (charcode c) = 2
  and isbra c  = Array.get ctable (charcode c) = 4
  and issymb c = Array.get ctable (charcode c) = 8
  and isalpha c = Array.get ctable (charcode c) = 16
  and isnum c = Array.get ctable (charcode c) = 32
  and isalnum c = Array.get ctable (charcode c) >= 16 in
  isspace,issep,isbra,issymb,isalpha,isnum,isalnum;;

(* ------------------------------------------------------------------------- *)
(* Reserved words.                                                           *)
(* ------------------------------------------------------------------------- *)

let reserve_words,unreserve_words,is_reserved_word,reserved_words =
  let reswords = ref ["(";  ")"; "[";   "]";  "{";   "}";
                      ":";  ";";  ".";  "|";
                      "let"; "in"; "and"; "if"; "then"; "else";
                      "match"; "with"; "function"; "->"; "when"] in
  (fun ns  -> reswords := union (!reswords) ns),
  (fun ns  -> reswords := subtract (!reswords) ns),
  (fun n  -> mem n (!reswords)),
  (fun () -> !reswords);;

(* ------------------------------------------------------------------------- *)
(* Functions to access the global tables controlling special parse status.   *)
(*                                                                           *)
(*  o List of binders;                                                       *)
(*                                                                           *)
(*  o List of prefixes (right-associated unary functions like negation).     *)
(*                                                                           *)
(*  o List of infixes with their precedences and associations.               *)
(*                                                                           *)
(* Note that these tables are independent of constant/variable status or     *)
(* whether an identifier is symbolic.                                        *)
(* ------------------------------------------------------------------------- *)

let unparse_as_binder,parse_as_binder,parses_as_binder,binders =
  let binder_list = ref ([]:string list) in
  (fun n  -> binder_list := subtract (!binder_list) [n]),
  (fun n  -> binder_list := union (!binder_list) [n]),
  (fun n  -> mem n (!binder_list)),
  (fun () -> !binder_list);;

let unparse_as_prefix,parse_as_prefix,is_prefix,prefixes =
  let prefix_list = ref ([]:string list) in
  (fun n  -> prefix_list := subtract (!prefix_list) [n]),
  (fun n  -> prefix_list := union (!prefix_list) [n]),
  (fun n  -> mem n (!prefix_list)),
  (fun () -> !prefix_list);;

let unparse_as_infix,parse_as_infix,get_infix_status,infixes =
  let cmp (s,(x,a)) (t,(y,b)) =
     x < y || x = y && a > b || x = y && a = b && s < t in
  let infix_list = ref ([]:(string * (int * string)) list) in
  (fun n     -> infix_list := filter (((<>) n) o fst) (!infix_list)),
  (fun (n,d) -> infix_list := sort cmp
     ((n,d)::(filter (((<>) n) o fst) (!infix_list)))),
  (fun n     -> assoc n (!infix_list)),
  (fun ()    -> !infix_list);;

(* ------------------------------------------------------------------------- *)
(* Interface mapping.                                                        *)
(* ------------------------------------------------------------------------- *)

let the_interface = ref ([] :(string * (string * hol_type)) list);;

let the_overload_skeletons = ref ([] : (string * hol_type) list);;

(* ------------------------------------------------------------------------- *)
(* Now the printer.                                                          *)
(* ------------------------------------------------------------------------- *)

include Format;;

set_max_boxes 100;;

(* ------------------------------------------------------------------------- *)
(* Flag determining whether interface/overloading is reversed on printing.   *)
(* ------------------------------------------------------------------------- *)

let reverse_interface_mapping = ref true;;

(* ------------------------------------------------------------------------- *)
(* Determine binary operators that print without surrounding spaces.         *)
(* ------------------------------------------------------------------------- *)

let unspaced_binops = ref [","; ".."; "$"];;

(* ------------------------------------------------------------------------- *)
(* Binary operators to print at start of line when breaking.                 *)
(* ------------------------------------------------------------------------- *)

let prebroken_binops = ref ["==>"];;

(* ------------------------------------------------------------------------- *)
(* Force explicit indications of bound variables in set abstractions.        *)
(* ------------------------------------------------------------------------- *)

let print_unambiguous_comprehensions = ref false;;

(* ------------------------------------------------------------------------- *)
(* Print the universal set UNIV:A->bool as "(:A)".                           *)
(* ------------------------------------------------------------------------- *)

let typify_universal_set = ref true;;

(* ------------------------------------------------------------------------- *)
(* Flag controlling whether hypotheses print.                                *)
(* ------------------------------------------------------------------------- *)

let print_all_thm = ref true;;

(* ------------------------------------------------------------------------- *)
(* Flag controlling whether types of subterms must be printed.               *)
(* 0: Do not print the types of subterms                                     *)
(* 1 (default) : Only print types containing invented type variables         *)
(* 2: Print the types of constants and variables                             *)
(* ------------------------------------------------------------------------- *)

let print_types_of_subterms = ref 1;;

(* ------------------------------------------------------------------------- *)
(* Get the name of a constant or variable.                                   *)
(* ------------------------------------------------------------------------- *)

let name_of tm =
  match tm with
    Var(x,ty) | Const(x,ty) -> x
  | _ -> "";;

(* ------------------------------------------------------------------------- *)
(* Colors                                                                    *)
(* ------------------------------------------------------------------------- *)

(* These numbers are ANSI color codes. *)
(* Const *)
let printer_color_const:string option ref = ref (Some "32") (* green *);;
(* Reserved words, excluding non-alphabets *)
let printer_color_resword:string option ref = ref (Some "34") (* blue *);;
(* Binders *)
let printer_color_binder:string option ref = ref (Some "35") (* purple *);;
(* Infixes *)
let printer_color_infix:string option ref = ref None;;
(* Prefixes *)
let printer_color_prefix:string option ref = ref None;;
(* Types *)
let printer_color_type:string option ref = ref (Some "36") (* light blue *);;
(* Type variables *)
let printer_color_typevar:string option ref = ref (Some "34") (* blue *);;
(* Invented type variables *)
let printer_color_itypevar:string option ref = ref (Some "31") (* red *);;

let pp_print_colored_string (colorcode:string option) fmt (contents:string) =
  match colorcode with
    Some thecode ->
    (* \027 is decimal 27 (oct 33) which corresponds to
        "Set foreground color" in Select Graphic Rendition *)
      let ansicmd = "\027[" ^ thecode ^ "m" in
      let endcmd = "\027[0m" in
      (pp_print_as fmt 0 ansicmd; (* consider ansicmd as 0-len string *)
       pp_print_string fmt contents;
       pp_print_as fmt 0 endcmd)
  | None -> pp_print_string fmt contents;;

let pp_print_colored_const, pp_print_colored_resword, pp_print_colored_binder,
    pp_print_colored_infix, pp_print_colored_prefix, pp_print_colored_tyvar =
  (fun fmt s -> pp_print_colored_string (!printer_color_const) fmt s),
  (fun fmt s -> pp_print_colored_string (!printer_color_resword) fmt s),
  (fun fmt s -> pp_print_colored_string (!printer_color_binder) fmt s),
  (fun fmt s -> pp_print_colored_string (!printer_color_infix) fmt s),
  (fun fmt s -> pp_print_colored_string (!printer_color_prefix) fmt s),
  (fun fmt s -> pp_print_colored_string
      (if s.[0] = '?' (* invented type var? *)
        then (!printer_color_itypevar) else (!printer_color_typevar)) fmt s);;

(* ------------------------------------------------------------------------- *)
(* Printer for types.                                                        *)
(* ------------------------------------------------------------------------- *)

let pp_print_type,pp_print_qtype =
  let soc sep flag ss =
    if ss = [] then "" else
    let s = end_itlist (fun s1 s2 -> s1^sep^s2) ss in
    if flag then "("^s^")" else s in
  let rec sot pr ty =
    try dest_vartype ty with Failure _ ->
    try string_of_num(dest_finty ty) with Failure _ ->
    match dest_type ty with
      con,[] -> con
    | "fun",[ty1;ty2] -> soc "->" (pr > 0) [sot 1 ty1; sot 0 ty2]
    | "sum",[ty1;ty2] -> soc "+" (pr > 2) [sot 3 ty1; sot 2 ty2]
    | "prod",[ty1;ty2] -> soc "#" (pr > 4) [sot 5 ty1; sot 4 ty2]
    | "cart",[ty1;ty2] -> soc "^" (pr > 6) [sot 6 ty1; sot 7 ty2]
    | con,args -> (soc "," true (map (sot 0) args))^con in
  (fun fmt ty -> pp_print_string fmt (sot 0 ty)),
  (fun fmt ty -> pp_print_string fmt "`:"; pp_print_string fmt (sot 0 ty);
                 pp_print_string fmt "`");;

(* Reimplementation of pp_print_type/pp_print_qtype, using prettyprinter
   to properly color strings *)
let pp_print_colored_type,pp_print_colored_qtype =
  let color_print_str fmt (s:string) =
    pp_print_colored_string (!printer_color_type) fmt s in
  (* ss is a list of printers whose format arg is not applied yet. *)
  let soc sep flag ss fmt =
    if ss = [] then () else
    let () = if flag then color_print_str fmt "(" in
    let tuple_printer = end_itlist (fun pp pp_next ->
        fun fmt -> (pp fmt; color_print_str fmt sep; pp_next fmt))
        ss in
    let () = tuple_printer fmt in
    if flag then color_print_str fmt ")" else () in

  let rec sot pr ty fmt =
    try pp_print_colored_tyvar fmt (dest_vartype ty)
    with Failure _ ->
    try color_print_str fmt (string_of_num(dest_finty ty)) with Failure _ ->
    match dest_type ty with
      con,[] -> color_print_str fmt con
    | "fun",[ty1;ty2] -> soc "->" (pr > 0) [sot 1 ty1; sot 0 ty2] fmt
    | "sum",[ty1;ty2] -> soc "+" (pr > 2) [sot 3 ty1; sot 2 ty2] fmt
    | "prod",[ty1;ty2] -> soc "#" (pr > 4) [sot 5 ty1; sot 4 ty2] fmt
    | "cart",[ty1;ty2] -> soc "^" (pr > 6) [sot 6 ty1; sot 7 ty2] fmt
    | con,args ->
      (soc "," true (map (sot 0) args) fmt; color_print_str fmt con)
  in
  (fun fmt ty -> sot 0 ty fmt),
  (fun fmt ty -> pp_print_string fmt "`:"; sot 0 ty fmt;
                 pp_print_string fmt "`");;

(* ------------------------------------------------------------------------- *)
(* Allow the installation of user printers. Must fail quickly if N/A.        *)
(* ------------------------------------------------------------------------- *)

let install_user_printer,install_user_color_printer,
    delete_user_printer,delete_user_color_printer,
    try_user_printer,try_user_color_printer =
  let user_printers = ref ([]:(string*(formatter->term->unit))list)
  and user_color_printers = ref ([]:(string*(formatter->term->unit))list) in
  (fun pr -> user_printers := pr::(!user_printers)),
  (fun pr -> user_color_printers := pr::(!user_color_printers)),
  (fun s -> user_printers := snd(remove (fun (s',_) -> s = s')
                                        (!user_printers))),
  (fun s -> user_color_printers := snd(remove (fun (s',_) -> s = s')
                                              (!user_color_printers))),
  (fun fmt -> fun tm -> tryfind (fun (_,pr) -> pr fmt tm) (!user_printers)),
  (fun fmt -> fun tm ->
    tryfind (fun (_,pr) -> pr fmt tm) (!user_color_printers));;

(* ------------------------------------------------------------------------- *)
(* Printer for terms.                                                        *)
(* ------------------------------------------------------------------------- *)

let pp_print_term,pp_print_colored_term =
  let reverse_interface (s0,ty0) =
    if not(!reverse_interface_mapping) then s0 else
    try fst(find (fun (s,(s',ty)) -> s' = s0 && can (type_match ty ty0) [])
                 (!the_interface))
    with Failure _ -> s0 in
  let DEST_BINARY c tm =
    try let il,r = dest_comb tm in
        let i,l = dest_comb il in
        if i = c ||
           (is_const i && is_const c &&
            reverse_interface(dest_const i) = reverse_interface(dest_const c))
        then l,r else fail()
    with Failure _ -> failwith "DEST_BINARY"
  and ARIGHT s =
    match snd(get_infix_status s) with
    "right" -> true | _ -> false in
  let rec powerof10 n =
    if abs_num n </ num 1 then false
    else if n =/ num 1 then true
    else powerof10 (n // num 10) in
  let bool_of_term t =
    match t with
      Const("T",_) -> true
    | Const("F",_) -> false
    | _ -> failwith "bool_of_term" in
  let code_of_term t =
    let f,tms = strip_comb t in
    if not(is_const f && fst(dest_const f) = "ASCII")
       || not(length tms = 8) then failwith "code_of_term"
    else
       itlist (fun b f -> if b then 1 + 2 * f else 2 * f)
              (map bool_of_term (rev tms)) 0 in
  let rec dest_clause tm =
    let pbod = snd(strip_exists(body(body tm))) in
    let s,args = strip_comb pbod in
    if name_of s = "_UNGUARDED_PATTERN" && length args = 2 then
      [rand(rator(hd args));rand(rator(hd(tl args)))]
    else if name_of s = "_GUARDED_PATTERN" && length args = 3 then
      [rand(rator(hd args)); hd(tl args); rand(rator(hd(tl(tl args))))]
    else failwith "dest_clause" in
  let rec dest_clauses tm =
    let s,args = strip_comb tm in
    if name_of s = "_SEQPATTERN" && length args = 2 then
      dest_clause (hd args)::dest_clauses(hd(tl args))
    else [dest_clause tm] in
  let pdest_cond tm =
    match tm with
      Comb(Comb(Comb(Const("COND",_),i),t),e) -> (i,t),e
    | _ -> failwith "pdest_cond" in
  let print_colored_term (use_color:bool) fmt =
    let color_switch pp =
      if use_color then pp else pp_print_string in

    (* ----- Phase A: shape-based handlers (run before strip_comb). Each
       prints on success or raises Failure to fall through. ----- *)

    let try_user_printers tm =
      if use_color then
        try try_user_color_printer fmt tm
        with _ -> try_user_printer fmt tm
      else
        try_user_printer fmt tm in

    let print_numeral tm =
      pp_print_string fmt (string_of_num(dest_numeral tm)) in

    let rec print_term prec tm =
      try try_user_printers tm with Failure _ ->
      try print_numeral tm with Failure _ ->
      try print_string_or_list tm with Failure _ ->
      if is_gabs tm then print_binder prec tm else
      let hop,args = strip_comb tm in
      let s = reverse_interface (name_of hop, type_of hop) in
      (* ----- Phase B: name-keyed handlers. ----- *)
      try print_empty_set s tm args with Failure _ ->
      try print_universal_set s tm args with Failure _ ->
      try print_finite_set s tm with Failure _ ->
      try print_set_comprehension s tm with Failure _ ->
      try print_let_term s prec tm with Failure _ ->
      try print_decimal s args with Failure _ ->
      try print_match s prec args with Failure _ ->
      try print_function s prec args with Failure _ ->
      try print_cond s prec tm args with Failure _ ->
      (* ----- Phase C: parser-status-based handlers. ----- *)
      try print_prefix_app s prec args with Failure _ ->
      try print_binder_app s prec tm args with Failure _ ->
      try print_infix_app s prec tm hop args with Failure _ ->
      (* ----- Phase D: leaf or generic application. ----- *)
      if (is_const hop || is_var hop) && args = [] then
        print_atom hop s
      else
        print_generic_app prec tm

    and print_string_or_list tm =
      let tms = dest_list tm in
      try if fst(dest_type(hd(snd(dest_type(type_of tm))))) <> "char"
          then fail() else
          let ccs = map (String.make 1 o Char.chr o code_of_term) tms in
          let s = "\"" ^ String.escaped (implode ccs) ^ "\"" in
          pp_print_string fmt s
      with Failure _ ->
          pp_open_box fmt 0; pp_print_string fmt "[";
          pp_open_box fmt 0; print_term_sequence true ";" 0 tms;
          pp_close_box fmt (); pp_print_string fmt "]";
          pp_close_box fmt ()

    and print_empty_set s tm args =
      if s = "EMPTY" && is_const tm && args = [] then
        pp_print_string fmt "{}"
      else fail()

    and print_universal_set s tm args =
      if s = "UNIV" && !typify_universal_set && is_const tm && args = [] then
        let ty = fst(dest_fun_ty(type_of tm)) in
        (pp_print_string fmt "(:";
         pp_print_type fmt ty;
         pp_print_string fmt ")")
      else fail()

    and print_finite_set s tm =
      if s <> "INSERT" then fail() else
      let mems,oth = splitlist (dest_binary "INSERT") tm in
      if is_const oth && fst(dest_const oth) = "EMPTY" then
        (pp_open_box fmt 0; pp_print_string fmt "{"; pp_open_box fmt 0;
         print_term_sequence true "," 14 mems;
         pp_close_box fmt (); pp_print_string fmt "}"; pp_close_box fmt ())
      else fail()

    and print_set_comprehension s tm =
      if s <> "GSPEC" then fail() else
      let evs,bod = strip_exists(body(rand tm)) in
      let bod1,fabs = dest_comb bod in
      let bod2,babs = dest_comb bod1 in
      let c = rator bod2 in
      if fst(dest_const c) <> "SETSPEC" then fail() else
      pp_print_string fmt "{";
      print_term 0 fabs;
      pp_print_string fmt " | ";
      (let fvs = frees fabs and bvs = frees babs in
       if not(!print_unambiguous_comprehensions) &&
          set_eq evs
           (if (length fvs <= 1 || bvs = []) then fvs
            else intersect fvs bvs)
       then ()
       else (print_term_sequence false "," 14 evs;
             pp_print_string fmt " | "));
      print_term 0 babs;
      pp_print_string fmt "}"

    and print_let_term s prec tm =
      if s <> "LET" then fail() else
      let eqs,bod = dest_let tm in
      (if prec = 0 then pp_open_hvbox fmt 0
       else (pp_open_hvbox fmt 1; pp_print_string fmt "(");
       color_switch pp_print_colored_resword fmt "let ";
       print_term 0 (mk_eq(hd eqs));
       do_list (fun (v,t) ->
           pp_print_break fmt 1 0;
           color_switch pp_print_colored_resword fmt "and ";
           print_term 0 (mk_eq(v,t)))
         (tl eqs);
       color_switch pp_print_colored_resword fmt " in";
       pp_print_break fmt 1 0;
       print_term 0 bod;
       if prec = 0 then () else pp_print_string fmt ")";
       pp_close_box fmt ())

    and print_decimal s args =
      if s <> "DECIMAL" then fail() else
      let n_num = dest_numeral (hd args)
      and n_den = dest_numeral (hd(tl args)) in
      if not(powerof10 n_den) then fail() else
      let s_num = string_of_num(quo_num n_num n_den) in
      let s_den = implode(tl(explode(string_of_num
                      (n_den +/ (mod_num n_num n_den))))) in
      pp_print_string fmt
       ("#"^s_num^(if n_den =/ num 1 then "" else ".")^s_den)

    and print_match s prec args =
      if s <> "_MATCH" || length args <> 2 then fail() else
      let cls = dest_clauses(hd(tl args)) in
      (if prec = 0 then () else pp_print_string fmt "(";
       pp_open_hvbox fmt 0;
       color_switch pp_print_colored_resword fmt "match ";
       print_term 0 (hd args);
       color_switch pp_print_colored_resword fmt " with";
       pp_print_break fmt 1 2;
       print_clauses cls;
       pp_close_box fmt ();
       if prec = 0 then () else pp_print_string fmt ")")

    and print_function s prec args =
      if s <> "_FUNCTION" || length args <> 1 then fail() else
      let cls = dest_clauses(hd args) in
      (if prec = 0 then () else pp_print_string fmt "(";
       pp_open_hvbox fmt 0;
       color_switch pp_print_colored_resword fmt "function";
       pp_print_break fmt 1 2;
       print_clauses cls;
       pp_close_box fmt ();
       if prec = 0 then () else pp_print_string fmt ")")

    and print_cond s prec tm args =
      if s <> "COND" || length args <> 3 then fail() else
      ((if prec = 0 then () else pp_print_string fmt "(");
       pp_open_hvbox fmt (-1);
       (let ccls,ecl = splitlist pdest_cond tm in
        if length ccls <= 4 then
         (color_switch pp_print_colored_resword fmt "if ";
          print_term 0 (hd args);
          pp_print_break fmt 0 0;
          color_switch pp_print_colored_resword fmt " then ";
          print_term 0 (hd(tl args));
          pp_print_break fmt 0 0;
          color_switch pp_print_colored_resword fmt " else ";
          print_term 0 (hd(tl(tl args)))
         )
        else
         (color_switch pp_print_colored_resword fmt "if ";
          print_term 0 (fst(hd ccls));
          color_switch pp_print_colored_resword fmt " then ";
          print_term 0 (snd(hd ccls));
          pp_print_break fmt 0 0;
          do_list (fun (i,t) ->
            color_switch pp_print_colored_resword fmt " else if ";
            print_term 0 i;
            color_switch pp_print_colored_resword fmt " then ";
            print_term 0 t;
            pp_print_break fmt 0 0) (tl ccls);
          color_switch pp_print_colored_resword fmt " else ";
          print_term 0 ecl));
       pp_close_box fmt ();
       (if prec = 0 then () else pp_print_string fmt ")"))

    and print_prefix_app s prec args =
      if not (is_prefix s && length args = 1) then fail() else
      (if prec = 1000 then pp_print_string fmt "(" else ();
       color_switch pp_print_colored_prefix fmt s;
       (if isalnum s ||
         s = "--" &&
         length args = 1 &&
         (try let l,_ = dest_comb(hd args) in
              let s0 = name_of l and ty0 = type_of l in
              reverse_interface (s0,ty0) = "--" ||
              mem (fst(dest_const l)) ["real_of_num"; "int_of_num"]
          with Failure _ -> false) ||
         s = "~" && length args = 1 && is_neg(hd args)
        then pp_print_string fmt " " else ());
       print_term 999 (hd args);
       if prec = 1000 then pp_print_string fmt ")" else ())

    and print_binder_app s prec tm args =
      if not (parses_as_binder s && length args = 1 && is_gabs (hd args))
      then fail() else
      print_binder prec tm

    and print_infix_app s prec tm hop args =
      if length args <> 2 || not (can get_infix_status s) then fail() else
      let bargs =
        if ARIGHT s then
          let tms,tmt = splitlist (DEST_BINARY hop) tm in tms@[tmt]
        else
          let tmt,tms = rev_splitlist (DEST_BINARY hop) tm in tmt::tms in
      let newprec = fst(get_infix_status s) in
      (if newprec <= prec then
        (pp_open_hvbox fmt 1; pp_print_string fmt "(")
       else pp_open_hvbox fmt 0;
       print_term newprec (hd bargs);
       do_list (fun x -> if mem s (!unspaced_binops) then ()
                         else if mem s (!prebroken_binops)
                         then pp_print_break fmt 1 0
                         else pp_print_string fmt " ";
                         color_switch pp_print_colored_infix fmt s;
                         if mem s (!unspaced_binops)
                         then pp_print_break fmt 0 0
                         else if mem s (!prebroken_binops)
                         then pp_print_string fmt " "
                         else pp_print_break fmt 1 0;
                         print_term newprec x) (tl bargs);
       if newprec <= prec then pp_print_string fmt ")" else ();
       pp_close_box fmt ())

    and print_atom hop s =
      let s' = if parses_as_binder s || can get_infix_status s || is_prefix s
               then "("^s^")" else s in
      let rec has_invented_typevar (ty:hol_type): bool =
        if is_vartype ty then (dest_vartype ty).[0] = '?'
        else List.exists has_invented_typevar (snd (dest_type ty)) in
      if !print_types_of_subterms = 2 ||
         (!print_types_of_subterms = 1 && has_invented_typevar (type_of hop))
      then
        (pp_open_box fmt 0;
        pp_print_string fmt "(";
        (if (is_const hop) then color_switch pp_print_colored_const fmt s'
         else pp_print_string fmt s');
        (* If s' ends in a symbolic character, juxtaposing ":" would lex as a
           single identifier (e.g. "&:" is one Ident), so insert a space. *)
        (if String.length s' > 0 &&
            issymb (String.sub s' (String.length s' - 1) 1)
         then pp_print_string fmt " " else ());
        pp_print_string fmt ":";
        (if use_color then pp_print_colored_type else pp_print_type)
          fmt (type_of hop);
        pp_print_string fmt ")";
        pp_close_box fmt ())
      else
        (if (is_const hop) then color_switch pp_print_colored_const fmt s'
         else pp_print_string fmt s')

    and print_generic_app prec tm =
      let l,r = dest_comb tm in
      (pp_open_hvbox fmt 0;
       if prec = 1000 then pp_print_string fmt "(" else ();
       print_term 999 l;
       (if try mem (fst(dest_const l)) ["real_of_num"; "int_of_num"]
           with Failure _ -> false
        then () else pp_print_space fmt ());
       print_term 1000 r;
       if prec = 1000 then pp_print_string fmt ")" else ();
       pp_close_box fmt ())

    and print_term_sequence break sep prec tms =
      if tms = [] then () else
      (print_term prec (hd tms);
       let ttms = tl tms in
       if ttms = [] then () else
       (pp_print_string fmt sep;
        (if break then pp_print_space fmt ());
        print_term_sequence break sep prec ttms))

    and print_binder prec tm =
      let absf = is_gabs tm in
      let s,s' = if absf then "\\","\\" else
                 let bt = rator tm in
                 let sn = name_of bt in
                 sn,reverse_interface(sn,type_of bt) in
      let rec collectvs tm =
        if absf then
          if is_abs tm then
            let v,t = dest_abs tm in
            let vs,bod = collectvs t in (false,v)::vs,bod
          else if is_gabs tm then
            let v,t = dest_gabs tm in
            let vs,bod = collectvs t in (true,v)::vs,bod
          else [],tm
        else if is_comb tm && name_of(rator tm) = s then
          if is_abs(rand tm) then
            let v,t = dest_abs(rand tm) in
            let vs,bod = collectvs t in (false,v)::vs,bod
          else if is_gabs(rand tm) then
            let v,t = dest_gabs(rand tm) in
            let vs,bod = collectvs t in (true,v)::vs,bod
          else [],tm
        else [],tm in
      let vs,bod = collectvs tm in
      ((if prec = 0 then pp_open_hvbox fmt 4
        else (pp_open_hvbox fmt 5; pp_print_string fmt "("));
       color_switch pp_print_colored_binder fmt s';
       (if isalnum s' then pp_print_string fmt " " else ());
       do_list (fun (b,x) ->
         (if b then pp_print_string fmt "(" else ());
         print_term 0 x;
         (if b then pp_print_string fmt ")" else ());
         pp_print_string fmt " ") (butlast vs);
       (if fst(last vs) then pp_print_string fmt "(" else ());
       print_term 0 (snd(last vs));
       (if fst(last vs) then pp_print_string fmt ")" else ());
       pp_print_string fmt ".";
       pp_print_space fmt ();
       print_term 0 bod;
       (if prec = 0 then () else pp_print_string fmt ")");
       pp_close_box fmt ())
    and print_clauses cls =
      match cls with
        [c] -> print_clause c
      | c::cs -> (print_clause c;
                  pp_print_break fmt 1 0;
                  pp_print_string fmt "| ";
                  print_clauses cs)
    and print_clause cl =
      match cl with
      [p;g;r] -> (print_term 1 p;
                  pp_print_string fmt " when ";
                  print_term 1 g;
                  pp_print_string fmt " -> ";
                  print_term 1 r)
    | [p;r] -> (print_term 1 p;
                pp_print_string fmt " -> ";
                print_term 1 r)
    in print_term 0
  in
  print_colored_term false, print_colored_term true;;

(* ------------------------------------------------------------------------- *)
(* Print term with quotes.                                                   *)
(* ------------------------------------------------------------------------- *)

let pp_print_qterm, pp_print_colored_qterm =
  let fn use_color fmt tm =
    pp_print_string fmt "`";
    (if use_color then pp_print_colored_term else pp_print_term) fmt tm;
    pp_print_string fmt "`" in
  fn false, fn true;;

(* ------------------------------------------------------------------------- *)
(* Printer for theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

let pp_print_thm, pp_print_colored_thm =
  let fn use_color fmt th =
    let asl,tm = dest_thm th in
    (if not (asl = []) then
      (if !print_all_thm then
        ((if use_color then pp_print_colored_term else pp_print_term)
            fmt (hd asl);
        do_list (fun x ->
            pp_print_string fmt ",";
            pp_print_space fmt ();
            (if use_color then pp_print_colored_term else pp_print_term)
              fmt x)
          (tl asl))
      else pp_print_string fmt "...";
      pp_print_space fmt ())
    else ();
    pp_open_hbox fmt();
    pp_print_string fmt "|- ";
    (if use_color then pp_print_colored_term else pp_print_term) fmt tm;
    pp_close_box fmt ())
  in
  fn false, fn true;;

(* ------------------------------------------------------------------------- *)
(* Print on standard output.                                                 *)
(* ------------------------------------------------------------------------- *)

let print_type = pp_print_type std_formatter;;
let print_qtype = pp_print_qtype std_formatter;;
let print_term = pp_print_term std_formatter;;
let print_qterm = pp_print_qterm std_formatter;;
let print_thm = pp_print_thm std_formatter;;

(* ------------------------------------------------------------------------- *)
(* Conversions to string.                                                    *)
(* ------------------------------------------------------------------------- *)

let print_to_string printer =
  let buf = Buffer.create 16 in
  let fmt = formatter_of_buffer buf in
  let () = pp_set_max_boxes fmt 100 in
  let print = printer fmt in
  let flush = pp_print_flush fmt in
  fun x ->
    let () = pp_set_margin fmt (get_margin ()) in
    let () = print x in
    let () = flush () in
    let s = Buffer.contents buf in
    let () = Buffer.reset buf in
    s;;

let string_of_type = print_to_string pp_print_type;;
let string_of_term = print_to_string pp_print_term;;
let string_of_thm = print_to_string pp_print_thm;;
