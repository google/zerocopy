(* ========================================================================= *)
(* More syntax constructors, and prelogical utilities like matching.         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*     (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018              *)
(* ========================================================================= *)

needs "fusion.ml";;

(* ------------------------------------------------------------------------- *)
(* Create probably-fresh variable                                            *)
(* ------------------------------------------------------------------------- *)

let genvar =
  let gcounter = ref 0 in
  fun ty -> let count = !gcounter in
             (gcounter := count + 1;
              mk_var("_"^(string_of_int count),ty));;

(* ------------------------------------------------------------------------- *)
(* Convenient functions for manipulating types.                              *)
(* ------------------------------------------------------------------------- *)

let dest_fun_ty ty =
  match ty with
    Tyapp("fun",[ty1;ty2]) -> (ty1,ty2)
  | _ -> failwith "dest_fun_ty";;

let rec occurs_in ty bigty =
  bigty = ty ||
  is_type bigty && exists (occurs_in ty) (snd(dest_type bigty));;

let rec tysubst alist ty =
  try rev_assoc ty alist with Failure _ ->
  if is_vartype ty then ty else
  let tycon,tyvars = dest_type ty in
  mk_type(tycon,map (tysubst alist) tyvars);;

(* ------------------------------------------------------------------------- *)
(* A bit more syntax.                                                        *)
(* ------------------------------------------------------------------------- *)

let bndvar tm =
  try fst(dest_abs tm)
  with Failure _ -> failwith "bndvar: Not an abstraction";;

let body tm =
  try snd(dest_abs tm)
  with Failure _ -> failwith "body: Not an abstraction";;

let list_mk_comb(h,t) = rev_itlist (C (curry mk_comb)) t h;;

let list_mk_abs(vs,bod) = itlist (curry mk_abs) vs bod;;

let strip_comb = rev_splitlist dest_comb;;

let strip_abs = splitlist dest_abs;;

(* ------------------------------------------------------------------------- *)
(* Generic syntax to deal with some binary operators.                        *)
(*                                                                           *)
(* Note that "mk_binary" only works for monomorphic functions.               *)
(* ------------------------------------------------------------------------- *)

let is_binary s tm =
  match tm with
    Comb(Comb(Const(s',_),_),_) -> s' = s
  | _ -> false;;

let dest_binary s tm =
  match tm with
    Comb(Comb(Const(s',_),l),r) when s' = s -> (l,r)
  | _ -> failwith "dest_binary";;

let mk_binary s =
  let c = mk_const(s,[]) in
  fun (l,r) -> try mk_comb(mk_comb(c,l),r)
               with Failure _ -> failwith "mk_binary";;

(* ------------------------------------------------------------------------- *)
(* Produces a sequence of variants, considering previous inventions.         *)
(* ------------------------------------------------------------------------- *)

let rec variants av vs =
  if vs = [] then [] else
  let vh = variant av (hd vs) in vh::(variants (vh::av) (tl vs));;

(* ------------------------------------------------------------------------- *)
(* Gets all variables (free and/or bound) in a term.                         *)
(* ------------------------------------------------------------------------- *)

let variables =
  let rec vars(acc,tm) =
    if is_var tm then insert tm acc
    else if is_const tm then acc
    else if is_abs tm then
      let v,bod = dest_abs tm in
      vars(insert v acc,bod)
    else
      let l,r = dest_comb tm in
      vars(vars(acc,l),r) in
  fun tm -> vars([],tm);;

(* ------------------------------------------------------------------------- *)
(* General substitution (for any free expression).                           *)
(* ------------------------------------------------------------------------- *)

let subst =
  let rec ssubst ilist tm =
    if ilist = [] then tm else
    try fst (find ((aconv tm) o snd) ilist) with Failure _ ->
    match tm with
      Comb(f,x) -> let f' = ssubst ilist f and x' = ssubst ilist x in
                   if f' == f && x' == x then tm else mk_comb(f',x')
    | Abs(v,bod) ->
          let ilist' = filter (not o (vfree_in v) o snd) ilist in
          mk_abs(v,ssubst ilist' bod)
    | _ -> tm in
  fun ilist ->
    let theta = filter (fun (s,t) -> compare s t <> 0) ilist in
    if theta = [] then (fun tm -> tm) else
    let ts,xs = unzip theta in
    fun tm ->
      let gs = variants (variables tm) (map (genvar o type_of) xs) in
      let tm' = ssubst (zip gs xs) tm in
      if tm' == tm then tm else vsubst (zip ts gs) tm';;

(* ------------------------------------------------------------------------- *)
(* Alpha conversion term operation.                                          *)
(* ------------------------------------------------------------------------- *)

let alpha v tm =
  let v0,bod = try dest_abs tm
               with Failure _ -> failwith "alpha: Not an abstraction"in
  if v = v0 then tm else
  if type_of v = type_of v0 && not (vfree_in v bod) then
    mk_abs(v,vsubst[v,v0]bod)
  else failwith "alpha: Invalid new variable";;

(* ------------------------------------------------------------------------- *)
(* Type matching.                                                            *)
(* ------------------------------------------------------------------------- *)

let rec type_match vty cty sofar =
  if is_vartype vty then
     try if rev_assoc vty sofar = cty then sofar else failwith "type_match"
     with Failure "find" -> (cty,vty)::sofar
  else
     let vop,vargs = dest_type vty and cop,cargs = dest_type cty in
     if vop = cop then itlist2 type_match vargs cargs sofar
     else failwith "type_match";;

(* ------------------------------------------------------------------------- *)
(* Conventional matching version of mk_const (but with a sanity test).       *)
(* ------------------------------------------------------------------------- *)

let mk_mconst(c,ty) =
  try let uty = get_const_type c in
      let mat = type_match uty ty [] in
      let con = mk_const(c,mat) in
      if type_of con = ty then con else fail()
  with Failure _ -> failwith "mk_const: generic type cannot be instantiated";;

(* ------------------------------------------------------------------------- *)
(* Like mk_comb, but instantiates type variables in rator if necessary.      *)
(* ------------------------------------------------------------------------- *)

let mk_icomb(tm1,tm2) =
  let "fun",[ty;_] = dest_type (type_of tm1) in
  let tyins = type_match ty (type_of tm2) [] in
  mk_comb(inst tyins tm1,tm2);;

(* ------------------------------------------------------------------------- *)
(* Instantiates types for constant c and iteratively makes combination.      *)
(* ------------------------------------------------------------------------- *)

let list_mk_icomb cname args =
  let atys,_ = nsplit dest_fun_ty args (get_const_type cname) in
  let tyin = itlist2 (fun g a -> type_match g (type_of a)) atys args [] in
  list_mk_comb(mk_const(cname,tyin),args);;

(* ------------------------------------------------------------------------- *)
(* Free variables in assumption list and conclusion of a theorem.            *)
(* ------------------------------------------------------------------------- *)

let thm_frees th =
  let asl,c = dest_thm th in
  itlist (union o frees) asl (frees c);;

(* ------------------------------------------------------------------------- *)
(* Is one term free in another?                                              *)
(* ------------------------------------------------------------------------- *)

let rec free_in tm1 tm2 =
  if aconv tm1 tm2 then true
  else if is_comb tm2 then
    let l,r = dest_comb tm2 in free_in tm1 l || free_in tm1 r
  else if is_abs tm2 then
    let bv,bod = dest_abs tm2 in
    not (vfree_in bv tm1) && free_in tm1 bod
  else false;;

(* ------------------------------------------------------------------------- *)
(* Searching for terms.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec find_term p tm =
  if p tm then tm else
  if is_abs tm then find_term p (body tm) else
  if is_comb tm then
    let l,r = dest_comb tm in
    try find_term p l with Failure _ -> find_term p r
  else failwith "find_term";;

let find_terms =
  let rec accum tl p tm =
    let tl' = if p tm then insert tm tl else tl in
    if is_abs tm then
       accum tl' p (body tm)
    else if is_comb tm then
       accum (accum tl' p (rator tm)) p (rand tm)
    else tl' in
  accum [];;

(* ------------------------------------------------------------------------- *)
(* General syntax for binders.                                               *)
(*                                                                           *)
(* NB! The "mk_binder" function expects polytype "A", which is the domain.   *)
(* ------------------------------------------------------------------------- *)

let is_binder s tm =
  match tm with
    Comb(Const(s',_),Abs(_,_)) -> s' = s
  | _ -> false;;

let dest_binder s tm =
  match tm with
    Comb(Const(s',_),Abs(x,t)) when s' = s -> (x,t)
  | _ -> failwith "dest_binder";;

let mk_binder op =
  let c = mk_const(op,[]) in
  fun (v,tm) -> mk_comb(inst [type_of v,aty] c,mk_abs(v,tm));;

(* ------------------------------------------------------------------------- *)
(* Syntax for binary operators.                                              *)
(* ------------------------------------------------------------------------- *)

let is_binop op tm =
  match tm with
    Comb(Comb(op',_),_) -> op' = op
  | _ -> false;;

let dest_binop op tm =
  match tm with
    Comb(Comb(op',l),r) when op' = op -> (l,r)
  | _ -> failwith "dest_binop";;

let mk_binop op tm1 =
  let f = mk_comb(op,tm1) in
  fun tm2 -> mk_comb(f,tm2);;

let list_mk_binop op = end_itlist (mk_binop op);;

let binops op = striplist (dest_binop op);;

(* ------------------------------------------------------------------------- *)
(* Some common special cases                                                 *)
(* ------------------------------------------------------------------------- *)

let is_conj = is_binary "/\\";;
let dest_conj = dest_binary "/\\";;
let conjuncts = striplist dest_conj;;

let is_imp = is_binary "==>";;
let dest_imp = dest_binary "==>";;

let is_forall = is_binder "!";;
let dest_forall = dest_binder "!";;
let strip_forall = splitlist dest_forall;;

let is_exists = is_binder "?";;
let dest_exists = dest_binder "?";;
let strip_exists = splitlist dest_exists;;

let is_disj = is_binary "\\/";;
let dest_disj = dest_binary "\\/";;
let disjuncts = striplist dest_disj;;

let is_neg tm =
  try fst(dest_const(rator tm)) = "~"
  with Failure _ -> false;;

let dest_neg tm =
  try let n,p = dest_comb tm in
      if fst(dest_const n) = "~" then p else fail()
  with Failure _ -> failwith "dest_neg";;

let is_uexists = is_binder "?!";;
let dest_uexists = dest_binder "?!";;

let dest_cons = dest_binary "CONS";;
let is_cons = is_binary "CONS";;
let dest_list tm =
  try let tms,nil = splitlist dest_cons tm in
      if fst(dest_const nil) = "NIL" then tms else fail()
  with Failure _ -> failwith "dest_list";;
let is_list = can dest_list;;

(* ------------------------------------------------------------------------- *)
(* Syntax for numerals.                                                      *)
(* ------------------------------------------------------------------------- *)

let dest_numeral =
  let rec dest_num tm =
    if try fst(dest_const tm) = "_0" with Failure _ -> false then num_0 else
    let l,r = dest_comb tm in
    let n = num_2 */ dest_num r in
    let cn = fst(dest_const l) in
    if cn = "BIT0" then n
    else if cn = "BIT1" then n +/ num_1
    else fail() in
  fun tm -> try let l,r = dest_comb tm in
                if fst(dest_const l) = "NUMERAL" then dest_num r else fail()
            with Failure _ -> failwith "dest_numeral";;

(* ------------------------------------------------------------------------- *)
(* Syntax for generalized abstractions.                                      *)
(*                                                                           *)
(* These are here because they are used by the preterm->term translator;     *)
(* preterms regard generalized abstractions as an atomic notion. This is     *)
(* slightly unclean --- for example we need locally some operations on       *)
(* universal quantifiers --- but probably simplest. It has to go somewhere!  *)
(* ------------------------------------------------------------------------- *)

let dest_gabs =
  let dest_geq = dest_binary "GEQ" in
  fun tm ->
    try if is_abs tm then dest_abs tm else
        let l,r = dest_comb tm in
        if not (fst(dest_const l) = "GABS") then fail() else
        let ltm,rtm = dest_geq(snd(strip_forall(body r))) in
        rand ltm,rtm
    with Failure _ -> failwith "dest_gabs: Not a generalized abstraction";;

let is_gabs = can dest_gabs;;

let mk_gabs =
  let mk_forall(v,t) =
    let cop = mk_const("!",[type_of v,aty]) in
    mk_comb(cop,mk_abs(v,t)) in
  let list_mk_forall(vars,bod) = itlist (curry mk_forall) vars bod in
  let mk_geq(t1,t2) =
    let p = mk_const("GEQ",[type_of t1,aty]) in
    mk_comb(mk_comb(p,t1),t2) in
  fun (tm1,tm2) ->
    if is_var tm1 then mk_abs(tm1,tm2) else
    let fvs = frees tm1 in
    let fty = mk_fun_ty (type_of tm1) (type_of tm2) in
    let f = variant (frees tm1 @ frees tm2) (mk_var("f",fty)) in
    let bod = mk_abs(f,list_mk_forall(fvs,mk_geq(mk_comb(f,tm1),tm2))) in
    mk_comb(mk_const("GABS",[fty,aty]),bod);;

let list_mk_gabs(vs,bod) = itlist (curry mk_gabs) vs bod;;

let strip_gabs = splitlist dest_gabs;;

(* ------------------------------------------------------------------------- *)
(* Syntax for let terms.                                                     *)
(* ------------------------------------------------------------------------- *)

let dest_let tm =
  try let l,aargs = strip_comb tm in
      if fst(dest_const l) <> "LET" then fail() else
      let vars,lebod = strip_gabs (hd aargs) in
      let eqs = zip vars (tl aargs) in
      let le,bod = dest_comb lebod in
      if fst(dest_const le) = "LET_END" then eqs,bod else fail()
  with Failure _ -> failwith "dest_let: not a let-term";;

let is_let = can dest_let;;

let mk_let(assigs,bod) =
  let lefts,rights = unzip assigs in
  let lend = mk_comb(mk_const("LET_END",[type_of bod,aty]),bod) in
  let lbod = list_mk_gabs(lefts,lend) in
  let ty1,ty2 = dest_fun_ty(type_of lbod) in
  let ltm = mk_const("LET",[ty1,aty; ty2,bty]) in
  list_mk_comb(ltm,lbod::rights);;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors for finite types.                            *)
(* ------------------------------------------------------------------------- *)

let mk_finty:num->hol_type =
  let rec finty n =
    if n =/ num_1 then mk_type("1",[]) else
    mk_type((if Num.mod_num n num_2 =/ num_0 then "tybit0" else "tybit1"),
            [finty(Num.quo_num n num_2)]) in
  fun n ->
    if not(is_integer_num n) || n </ num_1 then failwith "mk_finty" else
    finty n;;

let rec dest_finty:hol_type->num =
  function
    Tyapp("1",_) -> num_1
  | Tyapp("tybit0",[ty]) -> dest_finty ty */ num_2
  | Tyapp("tybit1",[ty]) -> succ_num (dest_finty ty */ num_2)
  | _ -> failwith "dest_finty";;

(* ------------------------------------------------------------------------- *)
(* Useful function to create stylized arguments using numbers.               *)
(* ------------------------------------------------------------------------- *)

let make_args =
  let rec margs n s avoid tys =
    if tys = [] then [] else
    let v = variant avoid (mk_var(s^(string_of_int n),hd tys)) in
    v::(margs (n + 1) s (v::avoid) (tl tys)) in
  fun s avoid tys ->
    if length tys = 1 then
      [variant avoid (mk_var(s,hd tys))]
    else
      margs 0 s avoid tys;;

(* ------------------------------------------------------------------------- *)
(* Director strings down a term.                                             *)
(* ------------------------------------------------------------------------- *)

let find_path =
  let rec find_path p tm =
    if p tm then [] else
    if is_abs tm then "b"::(find_path p (body tm)) else
    try "r"::(find_path p (rand tm))
    with Failure _ -> "l"::(find_path p (rator tm)) in
  fun p tm -> implode(find_path p tm);;

let follow_path =
  let rec follow_path s tm =
    match s with
      [] -> tm
    | "l"::t -> follow_path t (rator tm)
    | "r"::t -> follow_path t (rand tm)
    | _::t -> follow_path t (body tm) in
  fun s tm -> follow_path (explode s) tm;;

(* ------------------------------------------------------------------------- *)
(* Considering a term as a propositional formula and returning atoms.        *)
(* ------------------------------------------------------------------------- *)

let atoms =
  let rec atoms acc tm =
    match tm with
      Comb(Comb(Const("/\\",_),l),r)
    | Comb(Comb(Const("\\/",_),l),r)
    | Comb(Comb(Const("==>",_),l),r)
    | Comb(Comb(Const("=",Tyapp("fun",[Tyapp("bool",[]);_])),l),r) ->
          atoms (atoms acc l) r
    | Comb(Const("~",_),l) -> atoms acc l
    | _ -> (tm |-> ()) acc in
  fun tm -> if type_of tm <> bool_ty then failwith "atoms: not Boolean"
            else foldl (fun a x y -> x::a) [] (atoms undefined tm);;
