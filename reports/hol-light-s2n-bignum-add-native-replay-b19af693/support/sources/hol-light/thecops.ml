(* ========================================================================= *)
(* Proof-producing HOL Light implementations of leanCoP and nanoCoP.         *)
(*                                                                           *)
(*           (c) Copyright, Michael Faerber 2018                             *)
(*                 (c) Cezary Kaliszyk 2014                                  *)
(* ========================================================================= *)

needs "metis.ml";;

(* ------------------------------------------------------------------------- *)
(* hashek.ml                                                                 *)
(* ------------------------------------------------------------------------- *)

module Hashek = struct

let hashek_def = new_definition `hashek = T`
let hashek_tm = `hashek`
let hashek_thm = prove (`hashek`, SIMP_TAC[hashek_def])
let hashek_prop =
  prove(`((x /\ hashek) ==> (y /\ hashek)) ==> (x ==> y)`, SIMP_TAC[hashek_def])
let hashek_eq = prove (`~ hashek <=> F`, SIMP_TAC[hashek_def])

let MARK_CONCL label =
  USE_THEN label (fun th -> UNDISCH_TAC (concl th)) THEN

  (fun g ->
     assert (is_imp (snd g));
     (* the first part of the implication *may* be a negation,
        but does not necessarily have to be *)
     assert (snd (dest_imp (snd g)) = `F`);
     ALL_TAC g) THEN

  REWRITE_TAC [TAUT `!t. (~t ==> F <=> t)`] THEN
  POP_ASSUM_LIST (fun l -> ASSUME_TAC (if l = [] then TRUTH else end_itlist CONJ l)) THEN

  (fun g -> assert (length (fst g) = 1); ALL_TAC g) THEN

  W(MAP_EVERY(UNDISCH_TAC o concl o snd) o fst) THEN
  MATCH_MP_TAC hashek_prop THEN
  DISCH_THEN (fun th -> EVERY (map ASSUME_TAC (CONJUNCTS th))) THEN
  REFUTE_THEN ASSUME_TAC

let MARK_ASSUMS = RULE_ASSUM_TAC (DISCH `hashek`)

end

(* ------------------------------------------------------------------------- *)
(* strom.ml                                                                  *)
(* ------------------------------------------------------------------------- *)

module Strom =
struct

type 'a strom = unit -> 'a
exception End_of_strom

let nil () = raise End_of_strom

let cons x l =
  let past = ref false in
  (fun () -> if !past then l () else (past := true; x))

let append xs ys =
  let past = ref false in
  (fun () -> if !past then ys ()
             else try xs () with End_of_strom -> (past := true; ys ()))

let of_list l =
  let r = ref l in
  (fun () -> match !r with
      [] -> raise End_of_strom
    | x :: xs -> r := xs; x)

let rec to_list l = try let x = l () in x :: to_list l with End_of_strom -> []

let iter f l =
  let rec iter () = let x = l () in f x; iter () in
  try iter () with End_of_strom -> ()

let map (f : 'a -> 'b) (l : 'a strom) () = f (l ())

let mapi (f : int -> 'a -> 'b) (l : 'a strom) =
  let i = ref 0 in
  fun () -> let h = !i in incr i; f h (l ())

let take n l =
  let i = ref n in
  fun () -> if !i = 0 then raise End_of_strom else (decr i; l ())

let take_while p l () =
  let x = l () in
  if p x then x else raise End_of_strom

let rec filter p l () =
  let x = l () in
  if p x then x else filter p l ()

let rec filter_map f l () =
  match f (l ()) with
    None -> filter_map f l ()
  | Some y -> y

let concat (ls : 'a strom strom) =
  let last = ref nil in
  let rec concat () =
    try !last () with End_of_strom -> (last := ls (); concat ()) in
  concat

let rec concat_map (f : 'a -> 'b strom) (l : 'a strom) =
  let last = ref nil in
  let rec concat_map () =
    try !last () with End_of_strom -> (last := f (l ()); concat_map ()) in
  concat_map

let next_opt l = try Some (l ()) with End_of_strom -> None

let cache (f : unit -> 'a strom) =
  let result = ref None in
  fun () -> match !result with None -> let l = f () in result := Some l; l () | Some l -> l ()

let cut xs ys =
  let cut = ref false
  and past = ref false in
  fun () ->
    if !past then ys ()
    else if !cut then nil ()
    else
      try let x = xs () in (cut := true; x)
      with End_of_strom -> (past := true; ys ())

let integers_from n =
  let i = ref n in
  fun () -> let h = !i in incr i; h

end

(* ------------------------------------------------------------------------- *)
(* term.ml                                                                   *)
(* ------------------------------------------------------------------------- *)

module Fol_term = struct

open Utils

let var v = Fvar v

let negate_lit (i, l) = (-i, l)

let rec term_max_var acc = function
    Fvar x -> max acc x
  | Fnapp (_, l) -> List.fold_left term_max_var acc l
let lit_max_var acc (_, a) = List.fold_left term_max_var acc a

let rec map_term_vars f = function
    Fvar v -> f v
  | Fnapp (p, t) -> Fnapp (p, List.map (map_term_vars f) t)
let map_lit_vars f (p, a) = (p, List.map (map_term_vars f) a)

let map_term fv fa = function
    Fvar v -> fv v
  | Fnapp (p, a) -> fa (p, a)

let rec term_ground t = map_term (const false) lit_ground t
and lit_ground (p, a) = List.for_all term_ground a


end

(* ------------------------------------------------------------------------- *)
(* print.ml                                                                  *)
(* ------------------------------------------------------------------------- *)

module Print = struct

let rec pp_interleave sep fn f = function
    x :: (_ :: _ as xs) -> fn f x; sep f; pp_interleave sep fn f xs
  | x :: [] -> fn f x
  | [] -> ()

let pp_iter sep = pp_interleave (fun f -> pp_print_string f sep)

let pp_iter_sp sep fn =
  let sep f = pp_print_char f ' '; pp_print_string f sep; pp_print_space f () in
  pp_interleave sep fn

let pp_enclose start stop fn f x =
  pp_print_string f start; fn f x; pp_print_string f stop

let pp_enclose_cut start stop fn =
  pp_enclose start stop (fun f x -> fn f x; pp_print_cut f ())

let pp_enum sep start stop fn =
  pp_enclose start stop (pp_iter sep fn)

let pp_with_box i fn f x =
  pp_open_box f i; fn f x; pp_close_box f ()

let pp_nl fn f x = fn f x; pp_print_newline f ()

let pp_print_null f x = ()


let pp_print_var f i =
  pp_print_char f (Char.chr (65 + i mod 26));
  if i > 25 then pp_print_int f (i / 26)

let rec pp_print_fterm f = function
    Fvar i -> pp_print_var f i
  | Fnapp (i, l) ->
      pp_print_term f (Meson.hol_of_const i);
      if l <> [] then pp_enum "," "(" ")" pp_print_fterm f l

let pp_print_lit f (i, l) =
  if i < 0 then pp_print_char f '~';
  pp_print_term f (Meson.hol_of_const (abs i));
  if l <> [] then pp_enum "," "(" ")" pp_print_fterm f l

let string_of_fterm = print_to_string pp_print_fterm
let string_of_lit = print_to_string pp_print_lit
let string_of_lits = print_to_string (pp_iter ", " pp_print_lit)

end

(* ------------------------------------------------------------------------- *)
(* database.ml                                                               *)
(* ------------------------------------------------------------------------- *)

module Database = struct

type contrapositive = (fol_term list * fol_atom list * int * (int * thm))

let clause_max_var cl = 1 + List.fold_left Fol_term.lit_max_var (-1) cl

let mapentry ((cl_rest, (p, args)), th) =
  (args, cl_rest, clause_max_var ((p, args) :: cl_rest), th)

(* for every predicate, store list of possible contrapositives *)
let db : (int, contrapositive list) Hashtbl.t = Hashtbl.create 10017

let axioms2db ths =
  Hashtbl.clear db;
  Mapping.fol_of_hol_clauses ths |>
  List.iter (fun (p, l) -> Hashtbl.add db (-p) (map mapentry l))

let db_entries lit =
  try Hashtbl.find db (fst lit) with Not_found -> []

end

(* ------------------------------------------------------------------------- *)
(* substitution.ml                                                           *)
(* ------------------------------------------------------------------------- *)

type lit = int * fol_term list
type iterm = fol_term

let rec offset_term off tm = match tm with
    Fvar v -> Fvar (v + off)
  | Fnapp (f, a) -> Fnapp (f, List.map (offset_term off) a)

let offset_lit off (p, pa) = p, List.map (offset_term off) pa


module type Substitution = sig
  type t
  exception Unify

  val unify_lit : t -> lit -> lit -> t
  val unify_tms : t -> iterm list -> iterm list -> t
  val unify_tms_off : int -> t -> iterm list -> iterm list -> t
  val eq_lit : t -> lit -> lit -> bool
  val inst_tm : t -> iterm -> iterm
  val inst_lit : t -> lit -> lit
  val ground_lit : t -> lit -> bool
  val empty : int -> t
  val to_list : t -> (int * iterm) list
end

module Substlist : Substitution with type t = (int * iterm) list =
struct

exception Unify

type t = (int * iterm) list

let rec istriv sub x = function
    Fvar y -> (*Printf.printf "V: %d %d\n" x y;*) y = x || (try let t = List.assoc y sub in istriv sub x t with Not_found -> false)
  | Fnapp (f, a) -> List.exists (istriv sub x) a && raise Unify;;

let add_subst sub x t =
  if istriv sub x t then sub else (x, t) :: sub

let rec unify_tm sub tm1 tm2 = match tm1,tm2 with
    Fnapp (f,fargs), Fnapp (g,gargs) -> if f <> g then raise Unify
      else unify_tms sub fargs gargs
  | tm, Fvar x | Fvar x, tm ->
      (try let t = List.assoc x sub in unify_tm sub tm t
      with Not_found -> add_subst sub x tm)
and unify_tms sub l1 l2 = List.fold_left2 unify_tm sub l1 l2

let unify_lit env (h1, l1) (h2, l2) =
  if h1 <> h2 then raise Unify else unify_tms env l1 l2

(* Unification with renaming of the second argument *)
let rec unify_tm_off off sub t1 t2 = match t1,t2 with
    Fnapp (f,fargs), Fnapp (g,gargs) -> if f <> g then raise Unify else
        unify_tms_off off sub fargs gargs
  | _, Fvar x -> let x = x + off in
     (try let t = List.assoc x sub in unify_tm_off 0 sub t1 t
     with Not_found -> add_subst sub x t1)
  | Fvar x, _ ->
     (try let t = List.assoc x sub in unify_tm_off off sub t t2
     with Not_found -> add_subst sub x (offset_term off t2))
and unify_tms_off off = List.fold_left2 (unify_tm_off off)

let rec eq_var_tm sub x = function
    Fvar y -> y = x || (try let t = List.assoc y sub in eq_var_tm sub x t with Not_found -> false)
  | Fnapp (f, a) -> false

let rec eq_term sub tm1 tm2 =
  match tm1,tm2 with
    Fnapp (f,fa), Fnapp (g,ga) -> f = g && eq_terms sub fa ga
  | _, Fvar x -> (try let t = List.assoc x sub in eq_term sub tm1 t with Not_found -> eq_var_tm sub x tm1)
  | Fvar x, _ -> (try let t = List.assoc x sub in eq_term sub t tm2 with Not_found -> eq_var_tm sub x tm2)
and eq_terms sub = List.for_all2 (eq_term sub)

let eq_lit sub (p,pa) (q,qa) = p = q && eq_terms sub pa qa

(* In leanCoP: only for printing, in resolve is used by unify_rename2 *)
let rec inst_tm sub = function
    Fvar v -> (try let t = List.assoc v sub in inst_tm sub t with Not_found -> Fvar v)
  | Fnapp (f,args) -> Fnapp (f, List.map (inst_tm sub) args)
let inst_lit sub (p, l) = (p, List.map (inst_tm sub) l)

let rec ground_tm sub = function
    Fvar v -> (try let t = List.assoc v sub in ground_tm sub t with Not_found -> false)
  | Fnapp (f,args) -> List.for_all (ground_tm sub) args
let ground_lit sub (p, l) = List.for_all (ground_tm sub) l

let empty _ = []

let to_list sub = sub

end


module Substarray : Substitution =
struct

type t = (iterm option array * int list ref) * int list

exception Unify

let rec restore_subst ((suba, env), subl) =
  while not (!env == subl) do
    match !env with
      h::t -> suba.(h) <- None; env := t
    | [] -> failwith "restore_subst"
  done

let rec istriv suba x = function
  | Fvar y -> y = x || (match suba.(y) with Some t -> istriv suba x t | None -> false)
  | Fnapp (f, a) -> List.exists (istriv suba x) a && raise Unify

let add_subst ((suba, env), subl as sub) x tm =
  if istriv suba x tm then sub
  else (suba.(x) <- Some tm; env := x :: !env; ((suba, env), !env))

let rec unify_tm ((suba, env), subl as sub) tm1 tm2 = match tm1,tm2 with
  | Fnapp (f,fargs), Fnapp (g,gargs) -> if f <> g then raise Unify
      else List.fold_left2 unify_tm sub fargs gargs
  | tm, Fvar x | Fvar x, tm -> (match suba.(x) with
    | Some t -> unify_tm sub tm t
    | None -> add_subst sub x tm)

let unify_tms sub l1 l2 = restore_subst sub; List.fold_left2 unify_tm sub l1 l2

let unify_lit env ((h1 : int), l1) (h2, l2) =
  if h1 <> h2 then raise Unify else unify_tms env l1 l2

let rec offset_vars off = function
  | Fvar x -> Fvar (x + off)
  | Fnapp (x, l) -> Fnapp (x, List.map (offset_vars off) l)

(* Unification with renaming of the second argument *)
let rec unify_tm_off off ((suba, env), subl as sub) t1 t2 = match t1,t2 with
  | Fnapp (f,fargs), Fnapp (g,gargs) -> if f <> g then raise Unify else
        List.fold_left2 (unify_tm_off off) sub fargs gargs
  | _, Fvar x -> let x = x + off in (match suba.(x) with
     | Some t -> unify_tm_off 0 sub t1 t
     | None -> add_subst sub x t1)
  | Fvar x,_ -> (match suba.(x) with
     | Some t -> unify_tm_off off sub t t2
     | None -> let t2' = offset_vars off t2 in add_subst sub x t2')

let unify_tms_off off sub l1 l2 =
  restore_subst sub; List.fold_left2 (unify_tm_off off) sub l1 l2


let rec eq_var_tm suba x = function
  | Fvar y -> y = x || (match suba.(y) with Some t -> eq_var_tm suba x t | None -> false)
  | Fnapp (f, a) -> false

let rec eq_tm suba tm1 tm2 =
  match tm1,tm2 with
  | Fnapp (f,fargs), Fnapp (g,gargs) -> f = g && List.for_all2 (eq_tm suba) fargs gargs
  | _, Fvar x -> (match suba.(x) with Some t -> eq_tm suba tm1 t | None -> eq_var_tm suba x tm1)
  | Fvar x, _ -> (match suba.(x) with Some t -> eq_tm suba t tm2 | None -> eq_var_tm suba x tm2)

let eq_lit ((suba, _), _ as sub) (p1,args1) (p2,args2) =
  p1 = p2 && (restore_subst sub; List.for_all2 (eq_tm suba) args1 args2)

let empty n =
  let suba = Array.make n (None : iterm option)
  and env = ref []
  and subl = []
  in ((suba, env), subl)

let to_list ((suba, env), subl) = List.map
  (fun v -> match suba.(v) with None -> failwith "convert_subst" | Some t -> v, t) subl

let rec inst_term suba = function
    Fvar x -> (match suba.(x) with Some t -> inst_term suba t | None -> Fvar x)
  | Fnapp (f, a) -> Fnapp (f, List.map (inst_term suba) a)

let inst_tm ((suba, _), _ as sub) t =
  restore_subst sub; inst_term suba t

let inst_lit ((suba, _), _ as sub) (p, l) =
  restore_subst sub; (p, List.map (inst_term suba) l)

let rec ground_tm suba = function
    Fvar x -> (match suba.(x) with Some t -> ground_tm suba t | None -> false)
  | Fnapp (f, a) -> List.for_all (ground_tm suba) a

let ground_lit ((suba, _), _ as sub) (p, l) =
  restore_subst sub; List.for_all (ground_tm suba) l

end

module Substoff (Sub : Substitution) = struct

include Sub

let eq (sub, off) l1 l2 = eq_lit sub l1 l2

let unify (sub, off) l1 l2 = try Some (unify_lit sub l1 l2, off) with Unify -> None

let unify_rename_subst off l1 l2 sub list =
  unify_tms_off off sub l1 l2, List.map (offset_lit off) list

let unify_rename (s, off) args1 (args2, rest, vars, _) =
  try Some (if vars = 0 then ((unify_tms s args1 args2, off), rest) else
    let s, rest = unify_rename_subst off args1 args2 s rest in ((s, off + vars), rest))
  with Unify -> None

end

(* ------------------------------------------------------------------------- *)
(* cop.ml                                                                    *)
(* ------------------------------------------------------------------------- *)

module Cop = struct

module Subst = Substoff (Substarray)

type search_opts =
{ cut1 : bool
; cut2 : bool
; cut3 : bool
; comp : int
; improved_lemmas : bool
; improved_regularity : bool
; add_eq_symmetry : bool
}

let search_opts =
{ cut1 = true
; cut2 = true
; cut3 = true
; comp = 7
; improved_lemmas = true
; improved_regularity = true
; add_eq_symmetry = true
}

let rec deepen f i = match f i with Some x -> x | None -> deepen f (i+1)
let rec deepen_to n f i =
  if i > n then None
  else match f i with None -> deepen_to n f (i+1) | s -> s

let strategy opt f =
  if opt.cut1 || opt.cut2 || opt.cut3 then
    match deepen_to opt.comp (f opt) 0 with
      None -> deepen (f {opt with cut1 = false; cut2 = false; cut3 = false}) 0
    | Some prf -> prf
  else
    deepen (f opt) 0

end

(* ------------------------------------------------------------------------- *)
(* equality.ml                                                               *)
(* ------------------------------------------------------------------------- *)

module Equality = struct

(* Version of Meson.create_equality_axioms with added symmetry rule *)
let create_equality_axioms =
  let eq_thms = (CONJUNCTS o prove)
   (`(x:A = x) /\ (~(x = y) \/ y = x) /\
     (~(x:A = y) \/ ~(x = z) \/ (y = z))`,
    REWRITE_TAC[] THEN ASM_CASES_TAC `x:A = y` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT) in
  let imp_elim_CONV = REWR_CONV
    (TAUT `(a ==> b) <=> ~a \/ b`) in
  let eq_elim_RULE =
    MATCH_MP(TAUT `(a <=> b) ==> b \/ ~a`) in
  let veq_tm = rator(rator(concl(hd eq_thms))) in
  let create_equivalence_axioms (eq,_) =
    let tyins = type_match (type_of veq_tm) (type_of eq) [] in
    map (INST_TYPE tyins) eq_thms in
  let rec tm_consts tm acc =
    let fn,args = strip_comb tm in
    if args = [] then acc
    else itlist tm_consts args (insert (fn,length args) acc) in
  let rec fm_consts tm ((preds,funs) as acc) =
    try fm_consts(snd(dest_forall tm)) acc with Failure _ ->
    try fm_consts(snd(dest_exists tm)) acc with Failure _ ->
    try let l,r = dest_conj tm in fm_consts l (fm_consts r acc)
    with Failure _ -> try
        let l,r = dest_disj tm in fm_consts l (fm_consts r acc)
    with Failure _ -> try
        let l,r = dest_imp tm in fm_consts l (fm_consts r acc)
    with Failure _ -> try
         fm_consts (dest_neg tm) acc with Failure _ ->
    try let l,r = dest_eq tm in
        if type_of l = bool_ty
        then fm_consts r (fm_consts l acc)
        else failwith "atomic equality"
    with Failure _ ->
    let pred,args = strip_comb tm in
    if args = [] then acc else
    insert (pred,length args) preds,itlist tm_consts args funs in
  let create_congruence_axiom pflag (tm,len) =
    let atys,rty = splitlist (fun ty -> let op,l = dest_type ty in
                                        if op = "fun" then hd l,hd(tl l)
                                        else fail())
                             (type_of tm) in
    let ctys = fst(chop_list len atys) in
    let largs = map genvar ctys
    and rargs = map genvar ctys in
    let th1 = rev_itlist (C (curry MK_COMB)) (map (ASSUME o mk_eq)
        (zip largs rargs)) (REFL tm) in
    let th2 = if pflag then eq_elim_RULE th1 else th1 in
    itlist (fun e th -> CONV_RULE imp_elim_CONV (DISCH e th)) (hyp th2) th2 in
  fun tms -> let preds,funs = itlist fm_consts tms ([],[]) in
             let eqs0,noneqs = partition
                (fun (t,_) -> is_const t && fst(dest_const t) = "=") preds in
             if eqs0 = [] then [] else
             let pcongs = map (create_congruence_axiom true) noneqs
             and fcongs = map (create_congruence_axiom false) funs in
             let preds1,_ =
               itlist fm_consts (map concl (pcongs @ fcongs)) ([],[]) in
             let eqs1 = filter
               (fun (t,_) -> is_const t && fst(dest_const t) = "=") preds1 in
             let eqs = union eqs0 eqs1 in
             let equivs =
               itlist (union' equals_thm o create_equivalence_axioms)
                      eqs [] in
             equivs@pcongs@fcongs

let create_eq_axs sym = match sym with
    true -> create_equality_axioms
  | false -> Meson.create_equality_axioms

end

(* ------------------------------------------------------------------------- *)
(* prepare.ml                                                                *)
(* ------------------------------------------------------------------------- *)

module Prepare = struct

let PREPARE_COP_TAC ths =
  (* mostly from Meson *)
  REFUTE_THEN (LABEL_TAC "copconcl") THEN
  Meson.POLY_ASSUME_TAC (map GEN_ALL ths) THEN

  (* CoP-specific part *)
  (Hashek.MARK_CONCL "copconcl" ORELSE Hashek.MARK_ASSUMS) THEN

    (* unmodified Meson parts start here *)
    W(MAP_EVERY(UNDISCH_TAC o concl o snd) o fst) THEN
    SELECT_ELIM_TAC THEN
    W(fun (asl,w) -> MAP_EVERY (fun v -> SPEC_TAC(v,v)) (frees w)) THEN
    CONV_TAC(PRESIMP_CONV THENC
             TOP_DEPTH_CONV BETA_CONV THENC
             LAMBDA_ELIM_CONV THENC
             CONDS_CELIM_CONV THENC
             Meson.QUANT_BOOL_CONV) THEN
    REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
    REFUTE_THEN ASSUME_TAC THEN
    RULE_ASSUM_TAC(CONV_RULE(NNF_CONV THENC SKOLEM_CONV)) THEN
    REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
    ASM_FOL_TAC

end

(* ------------------------------------------------------------------------- *)
(* proof.ml                                                                  *)
(* ------------------------------------------------------------------------- *)

module Proof =
struct

type ('l, 'c) proof =
    Lemma
  | Reduction
  | Extension of 'c * ('l * ('l, 'c) proof) list

end

(* ------------------------------------------------------------------------- *)
(* search.ml                                                                 *)
(* ------------------------------------------------------------------------- *)

module Search = struct

open Print
open Fol_term
open Strom
open Proof
open Utils
open Cop

let cut p xs ys = Strom.(if p then cut xs ys else append xs ys)

let rec prove_lit opt sub (path, lem, lim) lit =
  (*if !verbosenc then (Format.printf "%d %s\n%!" !plits (string_of_lit (pred_of_lit lit)); incr plits);*)

  if !copverb then Format.printf "Lit: %s\n%!" (string_of_lit (Subst.inst_lit (fst sub) lit));
  if !copverb then Format.printf "Path: %s\n%!" (string_of_lits (List.map (Subst.inst_lit (fst sub)) path));
  if !copverb then Format.printf "Lemmas: %s\n%!" (string_of_lits (List.map (Subst.inst_lit (fst sub)) lem));

  let neglit = negate_lit lit in
  let lemmas =
    if opt.improved_lemmas then begin
      if List.exists (Subst.eq sub lit) lem then
       (if !copverb then Format.printf "lemma\n%!"; cons (sub, lem, Lemma) nil) else nil
    end
    else
      Strom.of_list lem |> Strom.filter (Subst.eq sub lit) |>
      Strom.map (fun l -> if !copverb then Format.printf "lemma\n%!"; (sub, lit :: lem, Lemma))
  and reductions = Strom.filter_map
    (fun p ->
      if !copverb then Format.printf "Reduction try %s (for lit %s, lim %d)\n%!" (string_of_lit p) (string_of_lit (Subst.inst_lit (fst sub) lit)) lim;
      Subst.unify sub neglit p >>=
      (fun sub1 -> if !copverb then Format.printf "Reduction works\n%!";
        Some (sub1, lit :: lem, Reduction))
    ) (Strom.of_list path)
  and extensions = Database.db_entries neglit
    |> Strom.of_list
    |> Strom.concat_map (fun ((_, _, vars, hsh) as contra) ->
(*
      if !copverb then Format.printf "Extension try %s (for lit %s, lim %d)\n%!" (Hashtbl.find Database.Clausal.no_contr hsh) (string_of_lit (Subst.inst_lit (fst sub) lit)) lim;
*)
      if lim < 0 && vars > 0 then nil
      else match Subst.unify_rename sub (snd lit) contra with
        Some (sub1, cla1) ->
(*
          if !copverb then Format.printf "Extension clause %s found\n%!" (List.map (Subst.inst_lit (fst sub1)) cla1 |> string_of_clause);
          incr Stats.infer;
*)

          prove_clause opt sub1 (lit :: path, lem, lim - 1) (cla1, hsh)
          |> Strom.map (fun (sub2, prfs) -> (sub2, lit :: lem, Extension (hsh, prfs)))
      | None -> nil) in
  cut opt.cut1 lemmas (cut opt.cut2 reductions (cut opt.cut3 extensions nil))
and prove_clause opt sub (path, lem, lim) (cl, cl_hsh) = match cl with
    lit :: lits ->
    if (List.exists (fun x -> List.exists (Subst.eq sub x) path)) cl then (if !copverb then Format.printf "regularity\n%!"; nil)
    else
    prove_lit opt sub (path, lem, lim) lit
    (*|> Litdata.trace_proofs lit cl_hsh*)
    |> Strom.concat_map
       (fun (sub1, lem1, prf1) -> prove_clause opt sub1 (path, lem1, lim) (lits, cl_hsh) |> Strom.map
       (fun (sub2, prfs) -> (sub2, (lit, prf1) :: prfs)))
  | [] -> cons (sub, []) nil

end

(* ------------------------------------------------------------------------- *)
(* recon.ml                                                                  *)
(* ------------------------------------------------------------------------- *)

module Recon = struct

open Proof
open Utils

let hol_negate tm = try dest_neg tm with Failure _ -> mk_neg tm;;

let rec hashek_of_proof sub lem lit =
  let liti = Mapping.hol_of_literal (Substarray.inst_lit sub lit) in
  function
    Lemma -> find (fun x -> concl x = liti) lem
  | Reduction -> ASSUME liti
  | Extension (contra, prfs) ->
      let _, ths = List.fold_map (fun lem (lit, prf) ->
        let p = hashek_of_proof sub lem lit prf in p :: lem, p) lem prfs in
      let cth = Meson.make_hol_contrapos contra in
      let hth = if ths = [] then cth else MATCH_MP cth (end_itlist CONJ ths) in
      let ith = PART_MATCH I hth liti in
      Meson.finish_RULE (DISCH (hol_negate (concl ith)) ith)

end

(* ------------------------------------------------------------------------- *)
(* leancop.ml                                                                *)
(* ------------------------------------------------------------------------- *)

(*
  Some examples that are not provable by MESON or METIS in reasonable time:
   LEANCOP [EXTENSION; IN_INSERT] (concl INSERT_COMM);;
   LEANCOP [EXTENSION; IN_DELETE] (concl DELETE_COMM);;
   LEANCOP [EXTENSION; IN_DELETE; IN_INTER] (concl DELETE_INTER);;
   LEANCOP [SUM_SUPERSET; SUBSET; IN_UNION] (concl SUM_UNION_RZERO);;
   LEANCOP [SUBSET; NSUM_SUPERSET; IN_UNION] (concl NSUM_UNION_RZERO);;
   LEANCOP [EXTENSION; NOT_IN_EMPTY; IN_INTERS; IN_INSERT] (concl INTERS_1);;
 *)

module Leancop = struct

open Cop

let start opt lim =
  if !copverb then Format.printf "Start %d\n%!" (lim+1);
  let sub0 = Subst.empty 1000000 in
  let hashek = Mapping.fol_of_literal [] [] Hashek.hashek_tm in
  let hashek_neg = Fol_term.negate_lit hashek in
  let prfs = Search.prove_lit opt (sub0, 0) ([], [], lim) hashek_neg in
  match Strom.next_opt prfs with
    Some (sub, _, prf) -> Some (fst sub, prf)
  | None -> None

(* Possible optimization:
   Reduce variable indexes to reduce used substitution and fit better in cache *)
let LEANCOP_DEEPEN opt ths =
  Meson.clear_contrapos_cache(); Mapping.reset_vars(); Mapping.reset_consts();
  let ths' = ths @ Equality.create_eq_axs opt.add_eq_symmetry (map concl ths) in
  Database.axioms2db ths';
  let sub, prf = strategy opt start in
  let hashek = Mapping.fol_of_literal [] [] Hashek.hashek_tm in
  let hashek_neg = Fol_term.negate_lit hashek in
  let th = Recon.hashek_of_proof sub [] hashek_neg prf in
  EQ_MP Hashek.hashek_eq th

let PREPARE_LEAN_TAC ths =
  Prepare.PREPARE_COP_TAC ths THEN
  RULE_ASSUM_TAC(CONV_RULE(PRENEX_CONV THENC WEAK_CNF_CONV)) THEN
  RULE_ASSUM_TAC(repeat
   (fun th -> SPEC(genvar(type_of(fst(dest_forall(concl th))))) th)) THEN
  REPEAT (FIRST_X_ASSUM (Meson.CONJUNCTS_THEN' ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(CONV_RULE(ASSOC_CONV DISJ_ASSOC)) THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC)

let PURE_LEANCOP opt gl =
  (FIRST_ASSUM CONTR_TAC ORELSE W(ACCEPT_TAC o LEANCOP_DEEPEN opt o map snd o fst)) gl

let GEN_LEANCOP_TAC opt ths = PREPARE_LEAN_TAC ths THEN PURE_LEANCOP opt
let LEANCOP_TAC ths = GEN_LEANCOP_TAC Cop.search_opts ths
let LEANCOP ths tm = prove(tm, LEANCOP_TAC ths)

end;;

(* ------------------------------------------------------------------------- *)
(* ncmatrix.ml                                                               *)
(* ------------------------------------------------------------------------- *)

module Ncmatrix = struct

open Utils
open Fol_term

type 't litmat = Lit of lit | Mat of 't imatrix
and 't imatrix = 't * 't matrix
and 't matrix = 't iclause list
and 't iclause = ('t * int list) * 't clause
and 't clause = 't  litmat list

let map_litmat fl fm = function
    Lit lit -> fl lit
  | Mat mat -> fm mat

let lit x = Lit x
let mat x = Mat x

let lit_of_litmat = function Lit l -> Some l | Mat _ -> None
let clause_lits c = List.filter_map lit_of_litmat c

let clause_of_matrix = function
    [(_, []), c] -> c
  | lm -> [Mat ((), lm)]

let rec strip_disj = function
    Disj (l, r) -> strip_disj l @ strip_disj r
  | x -> [x]
let rec strip_conj = function
    Conj (l, r) -> strip_conj l @ strip_conj r
  | x -> [x]
let rec strip_forallq acc = function
    Forallq (x, t) -> strip_forallq (x :: acc) t
  | t -> List.rev acc, t

let rec litmat_of_form = function
    Atom t -> Lit t
  | (Conj _ as t) | (Forallq _ as t) -> Mat ((), matrix_of_form t)
  | _ -> failwith "litmat_of_form"
and matrix_of_form t = List.map iclause_of_form (strip_conj t)
and clause_of_form t = List.map litmat_of_form (strip_disj t)
and iclause_of_form t =
  let univ, t' = strip_forallq [] t in ((), univ), clause_of_form t'

(* Original matrix_of_form from OCaml-nanoCoP is below.
   WARNING: Gives different results than version above, reconstruction fails!
*)
(*
let rec matrix_of_form fv = function
    Atom t -> [((), fv), [Lit t]]
  | Forallq (x, t) -> matrix_of_form (x::fv) t
  | Disj (l, r) ->
      let (cl, cr) = Pair.mapn (matrix_of_form [] %> clause_of_matrix) (l, r) in
      [((), fv), cl @ cr]
  | Conj (l, r) ->
      let (ml, mr) = Pair.mapn (matrix_of_form fv) (l, r) in ml @ mr
*)

let rec litmat_max_var acc = map_litmat (lit_max_var acc) (imatrix_max_var acc)
and imatrix_max_var acc (_, m) = matrix_max_var acc m
and iclause_max_var acc (_, c) = clause_max_var acc c
and matrix_max_var acc m = List.fold_left iclause_max_var acc m
and clause_max_var acc c = List.fold_left  litmat_max_var acc c

let  clause_offset c = 1 +  clause_max_var (-1) c
let iclause_offset c = 1 + iclause_max_var (-1) c

let clause_ground c =
  List.for_all (function Lit l -> lit_ground l | Mat _ -> false) c

let rec index_imatrix i (_, m)  = let j, m' = index_matrix (i+1) m in j, (i, m')
and index_matrix i m = List.fold_map index_iclause i m
and index_iclause i ((_, v), c) = let j, c' = index_clause (i+1) c in j, ((i, v), c')
and index_clause i c = List.fold_map index_litmat i c
and index_litmat i = function
    Lit l -> i, Lit l
  | Mat m -> let j, m' = index_imatrix i m in j, Mat m'
let index_matrix m = snd (index_matrix 0 m)

let rec map_imatrix f (t, m) = (f t, map_matrix f m)
and map_matrix f = List.map (map_iclause f)
and map_iclause f ((t, v), c) = ((f t, v), map_clause f c)
and map_clause f = List.map (map_litmat lit (mat % map_imatrix f))

let copy_matrix k = map_matrix (fun i -> i, k)
let copy_clause k = map_clause (fun i -> i, k)


let rec break_map f = function
    [] -> Some []
  | x::xs -> f x >>= fun y -> break_map f xs >>= fun ys -> Some (y::ys)

let rec litmat_positive lm = map_litmat lit_positive imatrix_positive lm
and lit_positive (p, a) = if p < 0 then Some (Lit (p, a)) else None
and imatrix_positive (i, m) =
  match matrix_positive m with [] -> None | m' -> Some (Mat (i, m'))
and matrix_positive m = List.filter_map iclause_positive m
and iclause_positive (i, c) = clause_positive c >>= (fun c' -> Some (i, c'))
and clause_positive c = break_map litmat_positive c

let rec map_litmat_vars f =
  map_litmat (lit % map_lit_vars (var % f)) (mat % map_imatrix_vars f)
and map_imatrix_vars f (i, m) = (i, map_matrix_vars f m)
and map_matrix_vars f m = List.map (map_iclause_vars f) m
and map_iclause_vars f ((i, v), c) = ((i, List.map f v), map_clause_vars f c)
and map_clause_vars f c = List.map (map_litmat_vars f) c

let offset_iclause off = map_iclause_vars ((+) off)
let offset_clause off = map_clause_vars ((+) off)
let offset_matrix off = map_matrix_vars ((+) off)

end

(* ------------------------------------------------------------------------- *)
(* ncprint.ml                                                                *)
(* ------------------------------------------------------------------------- *)

module Ncprint = struct

open Format
open Print
open Ncmatrix

let rec pp_print_litmat fi f = function
    Lit l -> pp_print_lit f l
  | Mat m -> pp_print_imatrix fi f m
and pp_print_imatrix fi f (i, m) =
  pp_open_box f 1;
  fi f i;
  pp_print_matrix fi f m;
  pp_close_box f ()
and pp_print_matrix fi =
  pp_with_box 1 (pp_enclose_cut "[" "]" (pp_iter_sp "&" (pp_print_iclause fi)))
and pp_print_iclause fi f ((i, v), c) =
  pp_open_box f 1;
  fi f i;
  pp_enum "," "{" "}" pp_print_var f v; pp_print_char f ':'; pp_print_space f ();
  pp_print_nclause fi f c;
  pp_close_box f ()
and pp_print_nclause fi =
  pp_with_box 1 (pp_enclose_cut "[" "]" (pp_iter_sp  "|" (pp_print_litmat fi)))

let pp_print_index = pp_enclose "<" ">" pp_print_int
(*let pp_print_index_copy = pp_enclose "<" ">" (pp_print_pair "," pp_print_int)*)


let string_of_litmat c = print_to_string (pp_print_litmat pp_print_null) c
let string_of_iclause c = print_to_string (pp_print_iclause pp_print_null) c
let string_of_iclause_i = print_to_string (pp_print_iclause pp_print_index)
let string_of_nclause c = print_to_string (pp_print_nclause pp_print_null) c
let string_of_matrix m = print_to_string (pp_print_matrix pp_print_null) m

let pp_print_matrix_ni fmt x = pp_print_matrix pp_print_null fmt x

let print_iclause c = pp_nl (pp_print_iclause pp_print_null) std_formatter c
let print_iclause_i = pp_nl (pp_print_iclause pp_print_index) std_formatter
let print_nclause c = pp_nl (pp_print_nclause pp_print_null) std_formatter c
let print_matrix_i = pp_nl (pp_print_matrix pp_print_index) Format.std_formatter

end

(* ------------------------------------------------------------------------- *)
(* ncproof.ml                                                                *)
(* ------------------------------------------------------------------------- *)

module Ncproof =
struct

type ('l, 'c, 'rd, 're) proof =
    Lemma
  | Reduction
  | Decomposition of 'c * 'rd * ('l * ('l, 'c, 'rd, 're) proof) list
  | Extension     of 'c * 're * ('l * ('l, 'c, 'rd, 're) proof) list

open Print
open Format

let rec pp_print_proof (fl, fc) sub f (lit, prf) =
  pp_open_vbox f 2;
  pp_print_string f (fl sub lit); pp_print_char f ' ';
  pp_print_prf (fl, fc) sub f prf;
  pp_close_box f ()
and pp_print_prf (fl, fc) sub f = function
    Reduction -> pp_print_string f "Red"
  | Lemma -> pp_print_string f "Lem"
  | Decomposition (cl, recon, prfs) ->
      pp_print_string f ("Dec " ^ fc cl);
      pp_print_proofs (fl, fc) sub f prfs
  | Extension (cl, recon, prfs) ->
      pp_print_string f ("Ext " ^ fc cl);
      pp_print_proofs (fl, fc) sub f prfs
and pp_print_proofs (fl, fc) sub f =
  List.iter (fun x -> pp_print_cut f (); pp_print_proof (fl, fc) sub f x)

let string_of_inst_litmat sub litmat = Ncprint.string_of_litmat litmat

let print_proofa (fl, fc) sub prf =
  pp_nl (pp_print_proof (fl, fc) sub) std_formatter prf

let print_proof_def sub prf =
  print_proofa (string_of_inst_litmat, Ncprint.string_of_nclause) sub prf


end

(* ------------------------------------------------------------------------- *)
(* extclause.ml                                                              *)
(* ------------------------------------------------------------------------- *)

module Extclause =
struct

open Ncmatrix
open Utils

type 'v litmat_ext =
    (* beta clause (left & right), whole clause *)
    Litext of ('v clause * 'v clause) * 'v clause
    (* matrix index, surrounding clause, path in clause *)
  | Matext of int * ('v clause * 'v clause) * 'v clause_ext
(* clause index, surrounding matrix, path in litmat *)
and 'v clause_ext = (int * 'v list) * ('v matrix * 'v matrix) * 'v litmat_ext

let offset_iv off (i, v) = (i, List.map ((+) off) v)

let rec offset_litmat_ext off = function
    Litext (claB, claC) ->
      Litext (Pair.mapn (offset_clause off) claB, offset_clause off claC)
  | Matext (j, claLR, clext) ->
      Matext (j, Pair.mapn (offset_clause off) claLR, offset_clause_ext off clext)
and offset_clause_ext off (iv, matLR, lmext) =
  offset_iv off iv, Pair.mapn (offset_matrix off) matLR, offset_litmat_ext off lmext

(* TODO: Understand why the reconstruction chokes on the
   OCaml-nanoCoP version of these functions.
*)
let rec claBC_of_litmat_ext = function
    Litext ((claL, claR), claC) -> (List.rev_append claL claR, claC)
  | Matext (j, (claL, claR), clext) ->
      let matB, matC = matBC_of_clause_ext clext
      and claLR = List.rev_append claL claR in
      matB @ claLR,
      (*Mat (j, matB) :: claLR,*) (* <--- TODO *)
      Mat (j, matC) :: claLR
and matBC_of_clause_ext (iv, (matL, matR), lmext) =
  let claB, claC = claBC_of_litmat_ext lmext in
  claB, (iv, claC) :: List.rev_append matL matR
  (*[iv, claB], (iv, claC) :: List.rev_append matL matR*) (* <--- TODO *)


let rec litext_of_litmat_ext = function
    Litext (claB, claC) -> claB, claC
  | Matext (_, _, clext) -> litext_of_clause_ext clext
and litext_of_clause_ext (_, _, lmext) = litext_of_litmat_ext lmext


let rec assert_iclause matLR (iv, (c : 'a clause)) =
  List.list_rest c |> List.concat_map (fun (lm, claLR) ->
    map_litmat
      (fun lit -> [lit, Litext (claLR, c)])
      (assert_imatrix claLR) lm)
    |> List.map (fun (lit, lmext) -> lit, (iv, matLR, lmext))
and assert_imatrix claLR (j, mat) =
  List.list_rest mat |> List.concat_map (fun (cla, matLR) -> assert_iclause matLR cla)
    |> List.map (fun (lit, claext) -> lit, Matext (j, claLR, claext))

(* WARNING: slightly less efficient version than in nanoCoP
   for easier reconstruction
*)
let assert_matrix mat =
  List.list_rest mat |> List.concat_map (fun (cla, matLR) -> assert_iclause matLR cla)

end

(* ------------------------------------------------------------------------- *)
(* ncdatabase.ml                                                             *)
(* ------------------------------------------------------------------------- *)

module Ncdatabase =
struct

open Ncmatrix
open Extclause

(* position of the literal in matrix, literal arguments, groundness, variable offset *)
type 'v contrapositive = 'v clause_ext * fol_term list * bool * int

let db : (int, int contrapositive list) Hashtbl.t = Hashtbl.create 10000

let insert_db db ((p, a), clext) =
  let matC = snd (matBC_of_clause_ext clext) in
  let off = 1 + Ncmatrix.matrix_max_var (-1) matC in
  let ground = litext_of_clause_ext clext |> snd |> Ncmatrix.clause_ground in
  (*Format.printf "Insert lit: %s with offset %d and claC: %s\n%!" (Print.string_of_lit (p,a)) off (Ncprint.string_of_matrix matC);*)
  let v = clext, a, ground, off in
  try Hashtbl.find db p |> (fun l -> v :: l) |> Hashtbl.replace db p
  with Not_found -> Hashtbl.add db p ([v])

let matrix2db m =
  let predb = assert_matrix m in
  Hashtbl.clear db;
  List.iter (insert_db db) (List.rev predb)

let db_entries lit = try Hashtbl.find db (fst lit) with Not_found -> []

end

(* ------------------------------------------------------------------------- *)
(* ncsearch.ml                                                               *)
(* ------------------------------------------------------------------------- *)

module Ncsearch = struct

open Cop
open Ncmatrix
open Extclause
open Strom
open Fol_term
open Utils


let unify_vars (sub, off) l1 l2 =
  try Some (Subst.unify_tms sub (List.map var l1) (List.map var l2), off)
  with Subst.Unify -> None

let unify_rename (sub, off) args1 (clext, args2, _, vars) =
  try Some (
    if vars = 0 then ((Subst.unify_tms sub args1 args2, off), clext)
    else
      (Subst.unify_tms_off off sub args1 args2, off + vars),
      offset_clause_ext off clext)
  with Subst.Unify -> None


(* epsilon operator on lists *)
let pick f l =
  let rec go acc = function
    x :: xs -> begin match f x with
      Some y -> (y, fun z -> List.rev_append acc (z::xs))
    | None -> go (x::acc) xs end
  | [] -> failwith "pick: no element found" in
  go [] l

let nth_clause i ((((j, k), v), _) as c) = if i = j then Some c else None
let nth_matrix i = function
    Lit _ -> None
  | Mat ((j, k), _ as m) -> if i = j then Some m else None

let unique f l = List.length (List.filter_map f l) = 1

let rec prove_ec k sub ((i, v), _, lmext as clext) mi pi =
  assert (unique (nth_clause i) mi);
  assert (List.length pi = k);
  (*if !copverb then Format.printf "prove_ec: ClaB = %s\n%!" (Ncprint.string_of_matrix (fst (matBC_of_clause_ext clext)));*)
  let ((((i, k1), v1), cla1), miAB) = pick (nth_clause i) mi in
  let alt1 () =
    match lmext with Matext (j, _, clext') when List.mem (j, k1) pi ->
      begin match unify_vars sub v v1 with None -> nil | Some sub2 ->
        let (((j, k1'), mi2), claDE) = pick (nth_matrix j) cla1 in
        assert (unique (nth_matrix j) cla1);
        assert (k1 = k1');
        prove_ec k sub2 clext' mi2 pi |> Strom.map
          (fun (sub3, (prefix, postfix), claB1, mi3) ->
            (sub3, (((i, v1), j) :: prefix, postfix), claB1, miAB (((i, k1), v1), claDE (Mat ((j, k1), mi3))))
          )
      end
    | _ -> nil
  and alt2 () =
    if List.mem (i, k1) pi && v = [] then nil
    else
      let (claB, claC) = claBC_of_litmat_ext lmext in
      let index cla = (((i, k), v), copy_clause k cla) in
      cons ((sub, ([], clext), index claB, miAB (index claC))) nil in
  Strom.(append (cache alt1) (cache alt2))

let cut p xs ys = Strom.(if p then cut xs ys else append xs ys)


open Ncproof
open Print
open Ncprint

let rec prove_lit opt sub (mi, path, pi, lem, lim) lit =
  if !copverb then Format.printf "Lit: %s\n%!" (string_of_lit (Subst.inst_lit (fst sub) lit));
  if !copverb then Format.printf "Path: %s\n%!" (string_of_lits path);
  if !copverb then Format.printf "Lemmas: %s\n%!" (string_of_lits lem);
  let neglit = negate_lit lit
  and k = lazy (List.length pi) in
  let lemmas =
    if List.exists (Subst.eq sub lit) lem then (if !copverb then Format.printf "lemma\n%!"; cons (sub, lem, Lemma) nil) else nil
  and reductions = Strom.of_list path |> Strom.filter_map
    (fun p -> if !copverb then Format.printf "Reduction try %s\n%!" (string_of_lit p);
      match Subst.unify sub neglit p with
        Some sub1 -> if !copverb then Format.printf "Reduction works\n%!";
        Some (sub1, lem, Reduction)
      | None -> None)
  and extensions = Ncdatabase.db_entries neglit
    |> Strom.of_list
    |> Strom.concat_map (fun ((_, args, ground, vars) as contra) ->
      if !copverb then Format.printf "Extension try (for lit %s, args (%s), lim %d, vars %d)\n%!" (string_of_lit (Subst.inst_lit (fst sub) lit)) (String.concat "," (List.map string_of_fterm args)) lim vars;
      if lim < 0 && not ground then nil
      else match unify_rename sub (snd lit) contra with
        Some (sub1, clext) ->
          if !copverb then Format.printf "Extension works (for lit %s, lim %d)\n%!" (string_of_lit (Subst.inst_lit (fst sub1) lit)) lim;
          if !copverb then Format.printf "Old/new offsets: %d/%d\n%!" (snd sub) (snd sub1);
          (*incr Stats.infer;
          Format.printf "ClaB: %s\n%!" (Ncprint.string_of_matrix (fst (matBC_of_clause_ext clext)));*)
          prove_ec (Lazy.force k) sub1 clext mi pi
          |> Strom.concat_map (fun (sub2, position, ((i, v), claB1), mi1) ->
            if !copverb then Format.printf "Extension clause %s found\n%!" (string_of_nclause claB1);
            prove_clause opt sub2 (mi1, lit :: path, i::pi, lem, lim - 1) claB1
            |> Strom.map (fun (sub3, prfs) ->
(*
              if verbosenc then Format.printf "Lit__: %s\n%!" (string_of_lit (inst_lit (fst sub3) lit));
              if verbosenc then Format.printf "ClaB1: %s\n%!" (string_of_nclause claB1);
*)
              (sub3, lit :: lem, Extension (Lit neglit :: claB1, position, prfs))))
      | None -> nil) in
  cut (Subst.ground_lit (fst sub) lit)
  (cut opt.cut1 lemmas (cut opt.cut2 reductions (cut opt.cut3 extensions nil))) nil
  |> Strom.map (fun (sub1, lem1, prf1) -> (sub1, lem1, (Lit lit, prf1)))
(* decomposition rule *)
and prove_mat opt sub (mi, path, pi, lem, lim) (j, mat1) =
  if !copverb then Format.printf "prove_mat\n%!";
  Strom.of_list mat1 |> Strom.concat_map
    (fun ((i, _) as idx, cla1) ->
      if !copverb then Format.printf "Decomposition chose: %s\n%!" (string_of_nclause cla1);
      prove_clause opt sub (mi, path, i::j::pi, lem, lim) cla1
      |> Strom.map (fun (sub1, prf1) -> (sub1, lem, (Mat (j, mat1), Decomposition (cla1, idx, prf1))))
    )
and prove_litmat opt sub st = map_litmat (prove_lit opt sub st) (prove_mat opt sub st)
and prove_clause opt sub (mi, path, pi, lem, lim) = function
  lm :: cla ->
    let check = List.exists (fun x -> List.exists (Subst.eq sub x) path) in
    let regularity =
      if opt.improved_regularity then check (clause_lits (lm :: cla))
      else (match lm with Mat _ -> false | Lit l -> check (l :: clause_lits cla)) in
    if regularity then (if !copverb then Format.printf "regularity\n%!"; nil)
    else prove_litmat opt sub (mi, path, pi, lem, lim) lm |> Strom.concat_map
      (fun (sub1, lem1, prf1) ->
        prove_clause opt sub1 (mi, path, pi, lem1, lim) cla
        |> Strom.map (fun (sub2, prf2) -> sub2, prf1 :: prf2)
      )
  (* axiom *)
  | [] -> if !copverb then Format.printf "axiom\n%!"; cons (sub, []) nil

end

(* ------------------------------------------------------------------------- *)
(* ncrecon.ml                                                                *)
(* ------------------------------------------------------------------------- *)

module Ncrecon = struct

open Utils
open Ncmatrix
open Ncproof
open Extclause


(* Given a theorem `|- p1 \/ ... \/ pn` as well as theorems
   `p1 |- c`, ..., `pn |- c`, return `|- c`.
*)
let rec DISJ_CASES_LIST th prfs =
  assert (List.length prfs = List.length (disjuncts (concl th)));
  assert (List.for_all2 List.mem (disjuncts (concl th)) (List.map hyp prfs));
  (* the conclusion of all proofs has to be the same *)
  assert (let c = concl (List.hd prfs) in
    List.fold_left (fun acc x -> acc && concl x = c) true prfs);
  match prfs with
    [] -> failwith "DISJ_CASES_LIST"
  | [p] -> MP (DISCH (concl th) p) th
  | [p1; p2] -> DISJ_CASES th p1 p2
  | p :: ps -> DISJ_CASES th p (DISJ_CASES_LIST (ASSUME (snd (dest_disj (concl th)))) ps);;

assert (DISJ_CASES_LIST (ASSUME `a \/ b \/ c`)
  [ TAUT `a ==> c \/ b \/ a` |> UNDISCH
  ; TAUT `b ==> c \/ b \/ a` |> UNDISCH
  ; TAUT `c ==> c \/ b \/ a` |> UNDISCH] |> concl = `c \/ b \/ a`);;


let CONTRADICTION x y =
  let xc, yc = concl x, concl y in
  if !copverb then Format.printf "contra: %s with %s\n%!" (string_of_term xc) (string_of_term yc);
  if is_neg xc && not (is_neg yc) then MP (NOT_ELIM x) y
  else if is_neg yc && not (is_neg xc) then MP (NOT_ELIM y) x
  else failwith "no contradiction found"

assert (concl (CONTRADICTION (ASSUME `~p`) (ASSUME `p:bool`)) = `F`);;
assert (concl (CONTRADICTION (ASSUME `p:bool`) (ASSUME `~p`)) = `F`);;


let flip_neg tm = if is_neg tm then dest_neg tm else mk_neg tm


let nth_disj j th =
  if !copverb then Format.printf "nth_disj %d %s\n%!" j (string_of_term (concl th));
  concl th |> disjuncts |> List.map ASSUME |> List.nth_rest j

let nth_conj i th =
  if !copverb then Format.printf "nth_conj %d %s\n%!" i (string_of_term (concl th));
  List.nth (CONJUNCTS th) i


let inst_var sub ty v =
  let ftm = Substarray.inst_tm sub (Fvar v) in
  try Mapping.hol_of_term ty ftm
  with Failure e -> failwith ("inst_var: " ^ e)

let spec_vars sub vs th =
  if !copverb then
    Format.printf "spec_vars: |vars| = %d, th = %s\n%!"
    (List.length vs) (string_of_term (concl th));
  let tys = concl th |> strip_forall |> fst |> List.map type_of in
  assert (List.length tys = List.length vs);
  List.fold_left2 (fun th ty v -> SPEC (inst_var sub ty v) th)
    th tys vs


type recon_data =
{ problem : thm
; mapping : (int * int) list
; sub : Substarray.t
}

let rec clause_index_mapping cl = cl |>
  List.mapi (fun idx -> function
      Lit _ -> []
    | Mat (j, mat) -> (j, idx) :: matrix_index_mapping mat) |>
  List.concat
and matrix_index_mapping mat = mat |>
  List.mapi (fun idx ((i, v), cl) -> (i, idx) :: clause_index_mapping cl) |>
  List.concat

let mk_recon_data (problem, mat, sub) =
  { problem = problem
  ; mapping = matrix_index_mapping mat
  ; sub = sub
  }

let prefix_problem data =
  let rel i = List.assoc i data.mapping in
  List.fold_left (fun th ((i, v), j) ->
    th |> nth_conj (rel i) |> spec_vars data.sub v |> nth_disj (rel j) |> fst)
    data.problem


let rec eat_proofs data =
  List.fold_map (fun (lem, prfs) th ->
    match prfs with
      prf :: prfs ->
        let bot = bot_of_proof data lem th prf in
        ((concl th, bot) :: lem, prfs), bot
    | [] -> failwith "eat_proofs"
  )

and bot_of_clause_ext data ((i, v), (matL, matR), lmext) acc th =
  let i' = List.assoc i data.mapping in
  assert (i' = List.length matL);
  assert (List.length (CONJUNCTS th) = 1 + List.length (matL @ matR));
  bot_of_litmat_ext data acc (nth_conj i' th |> spec_vars data.sub v) lmext
and bot_of_litmat_ext data acc thi = function
    Litext ((claL, claR), claC) ->
      let j = List.length claL in
      let thj, (thL, thR) = nth_disj j thi in
      let acc1, botsL = eat_proofs data acc  thL in
      let acc2, botsR = eat_proofs data acc1 thR in
      if !copverb then
        Format.printf "bot_of_litmat_ext: thi = %s\n%!" (string_of_thm thi);
      assert (let tmj = concl thj in not (is_conj tmj || is_disj tmj));
      let botj = CONTRADICTION thj (concl thj |> flip_neg |> ASSUME) in
      acc2, DISJ_CASES_LIST thi (botsL @ botj :: botsR)
  | Matext (j, (claL, claR), clext) ->
      let j' = List.assoc j data.mapping in
      assert (j' = List.length claL);
      let thj, (thL, thR) = nth_disj j' thi in
      let acc1, botj  = bot_of_clause_ext data clext acc thj in
      let acc2, botsL = eat_proofs data acc1 thL in
      let acc3, botsR = eat_proofs data acc2 thR in
      acc3, DISJ_CASES_LIST thi (botsL @ botj :: botsR)

and bot_of_proof data lem th = function
    Mat (j, mat), Decomposition (cla, ((i, k), v), prfs) ->
      let i' = List.assoc i data.mapping in
      assert (i' < List.length mat);
      assert (snd (List.nth mat i') = cla);
      if !copverb then
        Format.printf "Decomposition %d: %s\n%!" i' (string_of_term (concl th));
      let thi = nth_conj i' th |> spec_vars data.sub v in
      let djs = disjuncts (concl thi) in
      assert (List.length djs = List.length prfs);
      List.map ASSUME djs |> eat_proofs data (lem, prfs)
      |> snd |> DISJ_CASES_LIST thi
  | Lit lit, prf ->
      let liti = Mapping.hol_of_literal (Substarray.inst_lit data.sub lit) in
      if !copverb then
        Format.printf "bot_of_proof: lit = %s\n%!" (string_of_term liti);
      assert (liti = concl th);
      begin match prf with
        Reduction -> flip_neg liti |> ASSUME |> CONTRADICTION th
      | Lemma -> assert (List.mem_assoc liti lem); List.assoc liti lem
      | Extension (_, (prefix, postfix), prfs) ->
          let prefix_th = prefix_problem data prefix in
          if !copverb then
            Format.printf "prefix_th = %s\n%!" (string_of_thm prefix_th);
          let (_, prfs'), bot =
            bot_of_clause_ext data postfix (lem, prfs) prefix_th in
          assert (prfs' = []);
          assert (List.mem (concl th) (hyp bot));
          MP (DISCH (concl th) bot) th
      | _ -> failwith "bot_of_proof: not a well-formed proof"
      end
  | _ -> failwith "bot_of_proof: not a well-formed proof"

end

(* ------------------------------------------------------------------------- *)
(* nanocop.ml                                                                *)
(* ------------------------------------------------------------------------- *)

module Nanocop = struct

open Cop
open Ncmatrix
open Utils

let start mat opt lim =
  if !copverb then Format.printf "Start %d\n%!" (lim+1);
  let mati = copy_matrix 0 mat in
  let sub0 = Subst.empty 1000000 in
  let hashek = Mapping.fol_of_literal [] [] Hashek.hashek_tm in
  Strom.of_list mati |> Strom.filter_map (function
      (((i, _), v) as idx, ([Lit lit] as cla)) when lit = hashek ->
        Ncsearch.prove_clause opt (sub0, 0) (mati, [], [i, 0], [], lim) cla
        |> Strom.next_opt >>= (fun (sub, prfs) -> Some (sub, Ncproof.Decomposition (cla, idx, prfs))
        )
    | _ -> None
    )
  |> Strom.next_opt >>= (fun (sub, prf) -> Some (fst sub, (Mat ((-1, 0), mati), prf)))

let fol_of_thm th =
  let lconsts = freesl (hyp th) in
  let tm = concl th in
  assert (List.for_all (fun x -> List.mem x lconsts) (frees tm));
  Mapping.fol_of_form [] lconsts tm



let NANOCOP_DEEPEN opt ths =
  if !copverb then begin
    Format.printf "NANOCOP_DEEPEN with ths:\n%!";
    List.iter (Format.printf "  th: %s\n%!" o string_of_thm) ths
  end;
  Mapping.reset_vars(); Mapping.reset_consts();
  let gen_eq = map GEN_ALL o Equality.create_eq_axs opt.add_eq_symmetry o map concl in
  let ths' =
    if List.exists (fun th -> concl th = Hashek.hashek_tm) ths
    then ths else Hashek.hashek_thm :: ths in
  let ths' = setify (ths' @ gen_eq ths') in
  let th = end_itlist CONJ ths' in
  let fol = fol_of_thm th in
  let mat = Ncmatrix.index_matrix (Ncmatrix.matrix_of_form fol) in
  if !copverb then (
    Format.printf "Matrix:\n%!";
    Ncprint.print_matrix_i mat);
  Ncdatabase.matrix2db mat;
  if !copverb then Format.printf "Matrix loaded.\n%!";
  let (sub, prfs) = Cop.strategy opt (start mat) in
  if !copverb then begin
    Format.printf "Theorem\n%!";
    Ncproof.print_proof_def sub prfs
  end;
  let data = Ncrecon.mk_recon_data (th, mat, sub) in
  let bot  = Ncrecon.bot_of_proof data [] th prfs in
  if !copverb then (Format.printf "Reconstruction:\n%!"; print_thm bot);
  assert (set_eq (hyp bot) (hyp th));
  assert (concl bot = `F`);
  bot


(* Debugging tactic. *)
let PRINT_TAC g = if !copverb then print_goal g; ALL_TAC g
let PRINT_ID_TAC s g = if !copverb then print_endline s; PRINT_TAC g

let PREPARE_NANOCOP_TAC ths =
    Prepare.PREPARE_COP_TAC ths THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV(CHANGED_CONV(ASSOC_CONV DISJ_ASSOC)))) THEN
    RULE_ASSUM_TAC(CONV_RULE(DEPTH_CONV(CHANGED_CONV(ASSOC_CONV CONJ_ASSOC)))) THEN
    REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC)

let PURE_NANOCOP opt gl =
  (FIRST_ASSUM CONTR_TAC ORELSE W(ACCEPT_TAC o NANOCOP_DEEPEN opt o map snd o fst)) gl

let GEN_NANOCOP_TAC opt ths = PREPARE_NANOCOP_TAC ths THEN PURE_NANOCOP opt

let NANOCOP_TAC ths = GEN_NANOCOP_TAC Cop.search_opts ths
let NANOCOP ths tm = prove(tm, NANOCOP_TAC ths)

end

(* ------------------------------------------------------------------------- *)
(* Expose the key functions at the top level.                                *)
(* ------------------------------------------------------------------------- *)

let LEANCOP_TAC = Leancop.LEANCOP_TAC;;

let LEANCOP = Leancop.LEANCOP;;

let NANOCOP_TAC = Nanocop.NANOCOP_TAC;;

let NANOCOP = Nanocop.NANOCOP;;
