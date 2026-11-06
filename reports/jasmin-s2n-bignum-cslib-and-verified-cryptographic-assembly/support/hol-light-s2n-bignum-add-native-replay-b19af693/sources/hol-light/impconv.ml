(* ========================================================================= *)
(* Implicational conversions, implicational rewriting and target rewriting.  *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Analysis and Design of Dependable Systems                *)
(*                  fortiss GmbH, Munich, Germany                            *)
(*                                                                           *)
(*       Formerly:  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent.aravantinos@fortiss.org>                      *)
(*                                                                           *)
(*            Distributed under the same license as HOL Light.               *)
(* ========================================================================= *)

needs "quot.ml";;

let IMP_REWRITE_TAC,TARGET_REWRITE_TAC,HINT_EXISTS_TAC,
    SEQ_IMP_REWRITE_TAC,CASE_REWRITE_TAC =

let I = fun x -> x in

(* Same as [UNDISCH] but also returns the undischarged term *)
let UNDISCH_TERM th =
  let p = (fst o dest_imp o concl) th in
  p,UNDISCH th in

(* Same as [UNDISCH_ALL] but also returns the undischarged terms *)
let rec UNDISCH_TERMS th =
  try
    let t,th' = UNDISCH_TERM th in
    let ts,th'' = UNDISCH_TERMS th' in
    t::ts,th''
  with Failure _ -> [],th in

(* Comblies the function [f] to the conclusion of an implicational theorem. *)
let MAP_CONCLUSION f th =
  let p,th = UNDISCH_TERM th in
  DISCH p (f th) in

let strip_conj = binops `(/\)` in

(* For a list [f1;...;fk], returns the first [fi x] that succeeds. *)
let rec tryfind_fun fs x =
  match fs with
  |[] -> failwith "tryfind_fun"
  |f::fs' -> try f x with Failure _ -> tryfind_fun fs' x in

(* Same as [mapfilter] but also provides the rank of the iteration as an
 * argument to [f]. *)
let mapfilteri f =
  let rec self i = function
    |[] -> []
    |h::t ->
        let rest = self (i+1) t in
        try f i h :: rest with Failure _ -> rest
  in
  self 0 in

let list_of_option = function None -> [] | Some x -> [x] in

let try_list f x = try f x with Failure _ -> [] in

let fail_if_unchanged f x =
  try f x with Unchanged -> failwith "Unchanged" in

(* A few constants. *)
let A_ = `A:bool` and B_ = `B:bool` and C_ = `C:bool` and D_ = `D:bool` in
let T_ = `T:bool` in

(* For a term t, builds `t ==> t` *)
let IMP_REFL =
  let lem = TAUT `A ==> A` in
  fun t -> INST [t,A_] lem in

(* Conversion version of [variant]:
 * Given variables [v1;...;vk] to avoid and a term [t],
 * returns [|- t = t'] where [t'] is the same as [t] without any use of the
 * variables [v1;...;vk].
 *)
let VARIANT_CONV av t =
  let vs = variables t in
  let mapping = filter (fun (x,y) -> x <> y) (zip vs (variants av vs)) in
  DEPTH_CONV (fun u -> ALPHA_CONV (assoc (bndvar u) mapping) u) t in

(* Rule version of [VARIANT_CONV] *)
let VARIANT_RULE = CONV_RULE o VARIANT_CONV in

(* Discharges the first hypothesis of a theorem. *)
let DISCH_HD th = DISCH (hd (hyp th)) th in

(* Rule version of [REWR_CONV] *)
let REWR_RULE = CONV_RULE o REWR_CONV in

(* Given a list [A1;...;Ak] and a theorem [th],
 * returns [|- A1 /\ ... /\ Ak ==> th].
 *)
let DISCH_IMP_IMP =
  let f = function
    |[] -> I
    |t::ts -> rev_itlist (fun t -> REWR_RULE IMP_IMP o DISCH t) ts o DISCH t
  in
  f o rev in

(* Given a term [A /\ B] and a theorem [th], returns [|- A ==> B ==> th]. *)
let rec DISCH_CONJ t th =
  try
    let t1,t2 = dest_conj t in
    REWR_RULE IMP_IMP (DISCH_CONJ t1 (DISCH_CONJ t2 th))
  with Failure _ -> DISCH t th in

(* Specializes all the universally quantified variables of a theorem,
 * and returns both the theorem and the list of variables.
 *)
let rec SPEC_VARS th =
  try
    let v,th' = SPEC_VAR th in
    let vs,th'' = SPEC_VARS th' in
    v::vs,th''
  with Failure _ -> [],th in

(* Comblies the function [f] to the body of a universally quantified theorem. *)
let MAP_FORALL_BODY f th =
  let vs,th = SPEC_VARS th in
  GENL vs (f th) in

(* Given a theorem of the form [!xyz. P ==> !uvw. C] and a function [f],
 * return [!xyz. P ==> !uvw. f C].
 *)
let GEN_MAP_CONCLUSION = MAP_FORALL_BODY o MAP_CONCLUSION o MAP_FORALL_BODY in

(* Turn a theorem of the form [x ==> y /\ z] into [(x==>y) /\ (x==>z)].
 * Also deals with universal quantifications if necessary
 * (e.g., [x ==> !v. y /\ z] will be turned into
 * [(x ==> !v. y) /\ (x ==> !v. z)])
 *
 * possible improvement: apply the rewrite more locally
 *)
let IMPLY_AND =
  let IMPLY_AND_RDISTRIB = TAUT `(x ==> y /\ z) <=> (x==>y) /\(x==>z)` in
  PURE_REWRITE_RULE [GSYM AND_FORALL_THM;IMP_IMP;
    RIGHT_IMP_FORALL_THM;IMPLY_AND_RDISTRIB;GSYM CONJ_ASSOC] in

(* Returns the two operands of a binary combination.
 * Contrary to [dest_binary], does not check what is the operator.
 *)
let dest_binary_blind = function
  |Comb(Comb(_,l),r) -> l,r
  |_ -> failwith "dest_binary_blind" in

let spec_all = repeat (snd o dest_forall) in

let thm_lt (th1:thm) th2 = th1 < th2 in

(* GMATCH_MP (U1 |- !x1...xn. H1 /\ ... /\ Hk ==> C) (U2 |- P)
 * = (U1 u U2 |- !y1...ym. G1' /\ ... /\ Gl' ==> C')
 * where:
 * - P matches some Hi
 * - C' is the result of applying the matching substitution to C
 * - Gj' is the result of applying the matching substitution to Hj
 * - G1',...,Gl' is the list corresponding to H1,...,Hk but without Hi
 * - y1...ym are the variables among x1,...,xn that are not instantiated
 *
 * possible improvement: make a specific conversion,
 * define a MATCH_MP that also returns the instantiated variables *)
let GMATCH_MP =
  let swap = CONV_RULE (REWR_CONV (TAUT `(p==>q==>r) <=> (q==>p==>r)`)) in
  fun th1 ->
    let vs,th1' = SPEC_VARS th1 in
    let hs,th1'' = UNDISCH_TERMS (PURE_REWRITE_RULE [IMP_CONJ] th1') in
    fun th2 ->
      let f h hs =
        let th1''' = DISCH h th1'' in
        let th1'''' =
          try swap (DISCH_IMP_IMP hs th1''') with Failure _ -> th1'''
        in
        MATCH_MP (GENL vs th1'''') th2
      in
      let rec loop acc = function
        |[] -> []
        |h::hs ->
            (try [f h (acc @ hs)] with Failure _ -> []) @ loop (h::acc) hs
      in
      loop [] hs in

let GMATCH_MPS ths1 ths2 =
  let insert (y:thm) = function
    |[] -> [y]
    |x::_ as xs when equals_thm x y -> xs
    |x::xs when thm_lt x y -> x :: insert y xs
    |_::_ as xs -> y::xs
  in
  let inserts ys = itlist insert ys in
  match ths1 with
  |[] -> []
  |th1::ths1' ->
    let rec self acc th1 ths1 = function
      |[] -> (match ths1 with [] -> acc | th::ths1' -> self acc th ths1' ths2)
      |th2::ths2' -> self (inserts (GMATCH_MP th1 th2) acc) th1 ths1 ths2'
    in
    self [] th1 ths1' ths2 in

let MP_CLOSURE ths1 ths2 =
  let ths1 = filter (is_imp o spec_all o concl) ths1 in
  let rec self ths2 = function
    |[] -> []
    |_::_ as ths1 ->
      let ths1'' = GMATCH_MPS ths1 ths2 in
      self ths2 ths1'' @ ths1''
  in
  self ths2 ths1 in

(* Set of terms. Implemented as ordered lists. *)
let module Tset =
  struct
    type t = term list
    let cmp (x:term) y = compare x y
    let lt (x:term) y = compare x y < 0
    let lift f = List.sort cmp o f
    let of_list = lift I
    let insert ts t =
      let rec self = function
        |[] -> [t]
        |x::xs when lt x t -> x::self xs
        |x::_ as xs when x = t -> xs
        |xs -> t::xs
      in
      if t = T_ then ts else self ts
    let remove ts t =
      let rec self = function
        |[] -> []
        |x::xs when lt x t -> x::self xs
        |x::xs when x = t -> xs
        |_::_ as xs -> xs
      in
      self ts
    let strip_conj =
      let rec self acc t =
        try
          let t1,t2 = dest_conj t in
          self (self acc t1) t2
        with Failure _ -> insert acc t
      in
      self []
    let rec union l1 l2 =
      match l1 with
      |[] -> l2
      |h1::t1 ->
          match l2 with
          |[] -> l1
          |h2::t2 when lt h1 h2 -> h1::union t1 l2
          |h2::t2 when h1 = h2 -> h1::union t1 t2
          |h2::t2 -> h2::union l1 t2
    let rec mem x = function
      |x'::xs when x' = x -> true
      |x'::xs when lt x' x -> mem x xs
      |_ -> false
    let subtract l1 l2 = filter (fun x -> not (mem x l2)) l1
    let empty = []
    let flat_revmap f =
      let rec self acc = function
        |[] -> acc
        |x::xs -> self (union (f x) acc) xs
      in
      self []
    let flat_map f = flat_revmap f o rev
    let rec frees acc = function
      |Var _ as t -> insert acc t
      |Const _ -> acc
      |Abs(v,b) -> remove (frees acc b) v
      |Comb(u,v) -> frees (frees acc u) v
    let freesl ts = itlist (C frees) ts empty
    let frees = frees empty
  end in

let module Type_annoted_term =
  struct
    type t =
      |Var_ of string * hol_type
      |Const_ of string * hol_type * term
      |Comb_ of t * t * hol_type
      |Abs_ of t * t * hol_type

    let type_of = function
      |Var_(_,ty) -> ty
      |Const_(_,ty,_) -> ty
      |Comb_(_,_,ty) -> ty
      |Abs_(_,_,ty) -> ty

    let rec of_term = function
      |Var(s,ty) -> Var_(s,ty)
      |Const(s,ty) as t -> Const_(s,ty,t)
      |Comb(u,v) ->
          let u' = of_term u and v' = of_term v in
          Comb_(u',v',snd (dest_fun_ty (type_of u')))
      |Abs(x,b) ->
          let x' = of_term x and b' = of_term b in
          Abs_(x',b',mk_fun_ty (type_of x') (type_of b'))

    let rec equal t1 t2 =
      match t1,t2 with
      |Var_(s1,ty1),Var_(s2,ty2)
      |Const_(s1,ty1,_),Const_(s2,ty2,_) -> s1 = s2 && ty1 = ty2
      |Comb_(u1,v1,_),Comb_(u2,v2,_) -> equal u1 u2 && equal v1 v2
      |Abs_(v1,b1,_),Abs_(v2,b2,_) -> equal v1 v2 && equal b1 b2
      |_ -> false

    let rec to_term = function
      |Var_(s,ty) -> mk_var(s,ty)
      |Const_(_,_,t) -> t
      |Comb_(u,v,_) -> mk_comb(to_term u,to_term v)
      |Abs_(v,b,_) -> mk_abs(to_term v,to_term b)

    let dummy = Var_("",aty)

    let rec find_term p t =
      if p t then t else
        match t with
        |Abs_(_,b,_) -> find_term p b
        |Comb_(u,v,_) -> try find_term p u with Failure _ -> find_term p v
        |_ -> failwith "Annot.find_term"
  end in

let module Annot = Type_annoted_term in

(* ------------------------------------------------------------------------- *)
(* First-order matching of terms.                                            *)
(*                                                                           *)
(* Same note as in [drule.ml]:                                               *)
(* in the event of spillover patterns, this may return false results;        *)
(* but there's usually an implicit check outside that the match worked       *)
(* anyway. A test could be put in (see if any "env" variables are left in    *)
(* the term after abstracting out the pattern instances) but it'd be slower. *)
(* ------------------------------------------------------------------------- *)

let fo_term_match lcs p t =
  let fail () = failwith "fo_term_match" in
  let rec self bnds (tenv,tyenv as env) p t =
    match p,t with
    |Comb(p1,p2),Annot.Comb_(t1,t2,_) -> self bnds (self bnds env p1 t1) p2 t2
    |Abs(v,p),Annot.Abs_(v',t,_) ->
        let tyenv' = type_match (type_of v) (Annot.type_of v') tyenv in
        self ((v',v)::bnds) (tenv,tyenv') p t
    |Const(n,ty),Annot.Const_(n',ty',_) ->
        if n <> n' then fail ()
        else
          let tyenv' = type_match ty ty' tyenv in
          tenv,tyenv'
    |Var(n,ty) as v,t ->
        (* Is [v] bound? *)
        (try if Annot.equal t (rev_assoc v bnds) then env else fail ()
        (* No *)
        with Failure _ ->
          if mem v lcs
          then
            match t with
            |Annot.Var_(n',ty') when n' = n && ty' = ty -> env
            |_ -> fail ()
          else
            let tyenv' = type_match ty (Annot.type_of t) tyenv in
            let t' = try Some (rev_assoc v tenv) with Failure _ -> None in
            match t' with
            |Some t' -> if t = t' then tenv,tyenv' else fail ()
            |None -> (t,v)::tenv,tyenv')
    |_ -> fail ()
  in
  let tenv,tyenv = self [] ([],[]) p (Annot.of_term t) in
  let inst = inst tyenv in
  List.rev_map (fun t,v -> Annot.to_term t,inst v) tenv,tyenv in

let GEN_PART_MATCH_ALL =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        and v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) and n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> try
        let l1,r1 = dest_comb t1
        and l2,r2 = dest_comb t2 in
        match_bvs l1 l2 (match_bvs r1 r2 acc)
    with Failure _ -> acc
  in
  fun partfn th ->
    let sth = SPEC_ALL th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lcs = intersect (frees (concl th)) (freesl(hyp th)) in
    let fvs = subtract (subtract (frees bod) (frees pbod)) lcs in
    fun tm ->
      let bvms = match_bvs tm pbod [] in
      let abod = deep_alpha bvms bod in
      let ath = EQ_MP (ALPHA bod abod) sth in
      let insts,tyinsts = fo_term_match lcs (partfn abod) tm in
      let eth = INSTANTIATE_ALL ([],insts,tyinsts) (GENL fvs ath) in
      let fth = itlist (fun v th -> snd(SPEC_VAR th)) fvs eth in
      let tm' = partfn (concl fth) in
      if compare tm' tm = 0 then fth else
      try SUBS[ALPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure" in

let module Fo_nets =
  struct
    type term_label =
      |Vnet of int
      |Lcnet of string * int
      |Cnet of string * int
      |Lnet of int

    type 'a t = Netnode of (term_label * 'a t) list * 'a list

    let empty_net = Netnode([],[])

    let enter =
      let label_to_store lcs t =
        let op,args = strip_comb t in
        let nargs = length args in
        match op with
        |Const(n,_) -> Cnet(n,nargs),args
        |Abs(v,b) ->
          let b' = if mem v lcs then vsubst [genvar(type_of v),v] b else b in
          Lnet nargs,b'::args
        |Var(n,_) when mem op lcs -> Lcnet(n,nargs),args
        |Var(_,_) -> Vnet nargs,args
        |_ -> assert false
      in
      let rec net_update lcs elem (Netnode(edges,tips)) = function
        |[] -> Netnode(edges,elem::tips)
        |t::rts ->
            let label,nts = label_to_store lcs t in
            let child,others =
              try (snd F_F I) (remove (fun (x,y) -> x = label) edges)
              with Failure _ -> empty_net,edges in
            let new_child = net_update lcs elem child (nts@rts) in
            Netnode ((label,new_child)::others,tips)
      in
      fun lcs (t,elem) net -> net_update lcs elem net [t]

    let lookup =
      let label_for_lookup t =
        let op,args = strip_comb t in
        let nargs = length args in
        match op with
        |Const(n,_) -> Cnet(n,nargs),args
        |Abs(_,b) -> Lnet nargs,b::args
        |Var(n,_) -> Lcnet(n,nargs),args
        |Comb _ -> assert false
      in
      let rec follow (Netnode(edges,tips)) = function
        |[] -> tips
        |t::rts ->
            let label,nts = label_for_lookup t in
            let collection =
              try follow (assoc label edges) (nts@rts) with Failure _ -> []
            in
            let rec support = function
              |[] -> [0,rts]
              |t::ts ->
                  let ((k,nts')::res') as res = support ts in
                  (k+1,(t::nts'))::res
            in
            let follows =
              let f (k,nts) =
                try follow (assoc (Vnet k) edges) nts with Failure _ -> []
              in
              map f (support nts)
            in
            collection @ flat follows
      in
      fun t net -> follow net [t]

    let rec filter p (Netnode(edges,tips)) =
      Netnode(
        List.map (fun l,n -> l,filter p n) edges,
        List.filter p tips)
  end in

let module Variance =
  struct
    type t = Co | Contra
    let neg = function Co -> Contra | Contra -> Co
  end in

(*****************************************************************************)
(* IMPLICATIONAL RULES                                                       *)
(* i.e., rules to build propositions based on implications rather than       *)
(* equivalence.                                                              *)
(*****************************************************************************)

let module Impconv =
  struct

let MKIMP_common lem th1 th2 =
  let a,b = dest_imp (concl th1) and c,d = dest_imp (concl th2) in
  MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2)

(* Similar to [MK_CONJ] but theorems should be implicational instead of
 * equational, i.e., conjoin both sides of two implicational theorems.
 *
 * More precisely: given two theorems [A ==> B] and [C ==> D],
 * returns [A /\ C ==> B /\ D].
 *)
let MKIMP_CONJ = MKIMP_common MONO_AND

(* Similar to [MK_DISJ] but theorems should be implicational instead of
 * equational, i.e., disjoin both sides of two implicational theorems.
 *
 * More precisely: given two theorems [A ==> B] and [C ==> D],
 * returns [A \/ C ==> B \/ D].
 *)
let MKIMP_DISJ = MKIMP_common MONO_OR

let MKIMP_IFF =
  let lem =
    TAUT `((A ==> B) ==> (C ==> D)) /\ ((B ==> A) ==> (D ==> C)) ==> (A <=> B)
      ==> (C <=> D)`
  in
  fun th1 th2 ->
    let ab,cd = dest_imp (concl th1) in
    let a,b = dest_imp ab and c,d = dest_imp cd in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2)

(* th1 = (A ==> B) ==> C1
 * th2 = (B ==> A) ==> C2
 * output = (A <=> B) ==> (C1 /\ C2)
 *)
let MKIMP_CONTRA_IFF =
  let lem =
    TAUT `((A ==> B) ==> C) /\ ((B ==> A) ==> D) ==> (A <=> B) ==> C /\ D`
  in
  fun th1 th2 ->
    let ab,c = dest_imp (concl th1) and _,d = dest_imp (concl th2) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2)

let MKIMPL_CONTRA_IFF =
  let lem = TAUT `((A ==> B) ==> C) ==> (A <=> B) ==> C /\ (B ==> A)` in
  fun th ->
    let ab,c = dest_imp (concl th) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_] lem) th

let MKIMPR_CONTRA_IFF =
  let lem =
    TAUT `((B ==> A) ==> D) ==> (A <=> B) ==> (A ==> B) /\ D`
  in
  fun th ->
    let ba,d = dest_imp (concl th) in
    let b,a = dest_imp ba in
    MP (INST [a,A_;b,B_;d,D_] lem) th

let MKIMP_CO_IFF =
  let lem =
    TAUT `(C ==> A ==> B) /\ (D ==> B ==> A) ==> C /\ D ==> (A <=> B)`
  in
  fun th1 th2 ->
    let c,ab = dest_imp (concl th1) and d,_ = dest_imp (concl th2) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2)

let MKIMPL_CO_IFF =
  let lem =
    TAUT `(C ==> A ==> B) ==> C /\ (B ==> A) ==> (A <=> B)`
  in
  fun th ->
    let c,ab = dest_imp (concl th) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_] lem) th

let MKIMPR_CO_IFF =
  let lem = TAUT `(D ==> B ==> A) ==> (A ==> B) /\ D ==> (A <=> B)` in
  fun th ->
    let d,ba = dest_imp (concl th) in
    let b,a = dest_imp ba in
    MP (INST [a,A_;b,B_;d,D_] lem) th

(* Given two theorems [A ==> B] and [C ==> D],
 * returns [(B ==> C) ==> (A ==> D)].
 *)
let MKIMP_IMP th1 th2 =
  let b,a = dest_imp (concl th1) and c,d = dest_imp (concl th2) in
  MP (INST [a,A_;b,B_;c,C_;d,D_] MONO_IMP) (CONJ th1 th2)

let MKIMPL_common lem =
  let lem' = REWRITE_RULE[] (INST [C_,D_] lem) in
  fun th t ->
    let a,b = dest_imp (concl th) in
    MP (INST [a,A_;b,B_;t,C_] lem') th

(* Given a theorem [A ==> B] and a term [C],
 * returns [A /\ C ==> B /\ C].
 *)
let MKIMPL_CONJ = MKIMPL_common MONO_AND

(* Given a theorem [A ==> B] and a term [C],
 * returns [A \/ C ==> B \/ C].
 *)
let MKIMPL_DISJ = MKIMPL_common MONO_OR

(* Given a theorem [A ==> B] and a term [C],
 * returns [(B ==> C) ==> (A ==> C)].
 *)
let MKIMPL_IMP =
  let MONO_IMP' = REWRITE_RULE[] (INST [C_,D_] MONO_IMP) in
  fun th t ->
    let b,a = dest_imp (concl th) in
    MP (INST [a,A_;b,B_;t,C_] MONO_IMP') th

let MKIMPR_common lem =
  let lem' = REWRITE_RULE[] (INST [A_,B_] lem) in
  fun t th ->
    let c,d = dest_imp (concl th) in
    MP (INST [c,C_;d,D_;t,A_] lem') th

(* Given a term [A] and a theorem [B ==> C],
 * returns [A /\ B ==> A /\ C].
 *)
let MKIMPR_CONJ = MKIMPR_common MONO_AND

(* Given a term [A] and a theorem [B ==> C],
 * returns [A \/ B ==> A \/ C].
 *)
let MKIMPR_DISJ = MKIMPR_common MONO_OR

(* Given a term [A] and a theorem [B ==> C],
 * returns [(A ==> B) ==> (A ==> C)].
 *)
let MKIMPR_IMP = MKIMPR_common MONO_IMP

(* Given a theorem [A ==> B], returns [~B ==> ~A]. *)
let MKIMP_NOT th =
  let b,a = dest_imp (concl th) in
  MP (INST [a,A_;b,B_] MONO_NOT) th

let MKIMP_QUANT lem x th =
  let x_ty = type_of x and p,q = dest_imp (concl th) in
  let p' = mk_abs(x,p) and q' = mk_abs(x,q) in
  let P = mk_var("P",mk_fun_ty x_ty bool_ty) in
  let Q = mk_var("Q",mk_fun_ty x_ty bool_ty) in
  let lem = INST [p',P;q',Q] (INST_TYPE [x_ty,aty] lem) in
  let c = ONCE_DEPTH_CONV (ALPHA_CONV x) THENC ONCE_DEPTH_CONV BETA_CONV in
  MP (CONV_RULE c lem) (GEN x th)

(* Given a variable [x] and a theorem [A ==> B],
 * returns [(!x. A) ==> (!x. B)]. *)
let MKIMP_FORALL = MKIMP_QUANT MONO_FORALL

(* Given a variable [x] and a theorem [A ==> B],
 * returns [(?x. A) ==> (?x. B)]. *)
let MKIMP_EXISTS = MKIMP_QUANT MONO_EXISTS

(* Given two theorems [A ==> B] and [B ==> C ==> D],
 * returns [(B ==> C) ==> (A ==> D)],
 * i.e., similar to [MKIMP_IMP] but allows to remove the context [B]
 * since it is a consequence of [A].
 *)
let MKIMP_IMP_CONTRA_CTXT =
  let lem = TAUT `(B==>A) /\ (A==>B==>C==>D) ==> (A==>C) ==> (B==>D)` in
  fun th1 th2 ->
    let a,bcd = dest_imp (concl th2) in
    let b,cd = dest_imp bcd in
    let c,d = dest_imp cd in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2)

let MKIMP_IMP_CO_CTXT =
  let lem = TAUT `(A==>B) /\ (A==>B==>D==>C) ==> (B==>D) ==> (A==>C)` in
  fun th1 th2 ->
    let a,bdc = dest_imp (concl th2) in
    let b,dc = dest_imp bdc in
    let d,c = dest_imp dc in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2)

(* Given a theorem [B ==> C ==> D], returns [(B ==> C) ==> (B ==> D)],
 * i.e., similar to [MKIMP_IMP] but allows to remove the context [B]
 * since it is a consequence of [A].
 *)
let MKIMPR_IMP_CTXT =
  let lem = TAUT `(A==>C==>D) ==> (A==>C) ==> (A==>D)` in
  fun th ->
    let a,cd = dest_imp (concl th) in
    let c,d = dest_imp cd in
    MP (INST [c,C_;d,D_;a,A_] lem) th

(* Given two theorems [A ==> B] and [A ==> B ==> C ==> D],
 * returns [(A /\ C) ==> (B /\ D)],
 * i.e., similar to [MKIMP_CONJ] but allows to remove the contexts [A] and [B].
 *)
let MKIMP_CONJ_CONTRA_CTXT =
  let lem = TAUT `(C==>A==>B) /\ (A==>B==>C==>D) ==> (A/\C==>B/\D)` in
  fun th1 th2 ->
    let a,bcd = dest_imp (concl th2) in
    let b,cd = dest_imp bcd in
    let c,d = dest_imp cd in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2)

let MKIMPL_CONJ_CONTRA_CTXT =
  let lem = TAUT `(C==>A==>B) ==> (A/\C==>B/\C)` in
  fun th ->
    let c,ab = dest_imp (concl th) in
    let a,b = dest_imp ab in
    MP (INST [a,A_;b,B_;c,C_] lem) th

let MKIMPR_CONJ_CONTRA_CTXT =
  let lem = TAUT `(A==>C==>D) ==> (A/\C==>A/\D)` in
  fun th ->
    let a,cd = dest_imp (concl th) in
    let c,d = dest_imp cd in
    MP (INST [a,A_;c,C_;d,D_] lem) th

let MKIMP_CONJ_CO_CTXT =
  let lem = TAUT `(B==>A) /\ (B==>D==>C) ==> (B/\D==>A/\C)` in
  fun th1 th2 ->
    let b,a = dest_imp (concl th1) in
    let d,c = dest_imp (snd (dest_imp (concl th2))) in
    MP (INST [a,A_;b,B_;c,C_;d,D_] lem) (CONJ th1 th2)

let MKIMPL_CONJ_CO_CTXT =
  let lem = TAUT `(B==>A) ==> (B/\C==>A/\C)` in
  fun th ->
    let b,a = dest_imp (concl th) in
    fun c -> MP (INST [a,A_;b,B_;c,C_] lem) th

let MKIMPL_CONJ_CO2_CTXT =
  let lem = TAUT `(C==>B==>A) ==> (B/\C==>A/\C)` in
  fun th ->
    let c,ba = dest_imp (concl th) in
    let b,a = dest_imp ba in
    MP (INST [a,A_;b,B_;c,C_] lem) th

let MKIMPR_CONJ_CO_CTXT = MKIMPR_CONJ_CONTRA_CTXT


(*****************************************************************************)
(* IMPLICATIONAL CONVERSIONS                                                 *)
(*****************************************************************************)

open Variance

(* An implicational conversion maps a term t to a theorem of the form:
 * t' ==> t if covariant
 * t ==> t' if contravariant
 *)
type imp_conv = Variance.t -> term -> thm

(* Trivial embedding of conversions into implicational conversions. *)
let imp_conv_of_conv:conv->imp_conv =
  fun c v t ->
    let th1,th2 = EQ_IMP_RULE (c t) in
    match v with Co -> th2 | Contra -> th1

(* Retrieves the outcome of an implicational conversion, i.e., t'. *)
let imp_conv_outcome th v =
  let t1,t2 = dest_binary_blind (concl th) in
  match v with Co -> t1 | Contra -> t2

(* [ALL_IMPCONV _ t] returns `t==>t` *)
let ALL_IMPCONV:imp_conv = fun _ -> IMP_REFL

(* The implicational conversion which always fails. *)
let NO_IMPCONV:imp_conv = fun _ _ -> failwith "NO_IMPCONV"

let bind_impconv (c:imp_conv) v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> IMP_TRANS (c v t1) th
  |Contra -> IMP_TRANS th (c v t2)

let THEN_IMPCONV (c1:imp_conv) c2 v t = bind_impconv c2 v (c1 v t)


(*****************************************************************************)
(* SOME USEFUL IMPLICATIONAL CONVERSIONS                                     *)
(*****************************************************************************)

(* Given a theorem [p ==> c], returns the implicational conversion which:
  * - in the covariant case, matches the input term [t] against [c] and returns
  *   [s(p) ==> t], where [s] is the matching substitution
  * - in the contravariant case, matches the input term [t] against [p] and returns
  *   [t ==> s(c)], where [s] is the matching substitution
  *)
let MATCH_MP_IMPCONV:thm->imp_conv =
  fun th -> function
    |Co -> GEN_PART_MATCH rand th
    |Contra -> GEN_PART_MATCH lhand th


(*****************************************************************************)
(* INTERFACE                                                                 *)
(*****************************************************************************)

(* From an implicational conversion builds a rule, i.e., a function which
 * takes a theorem and returns a new theorem.
 *)
let IMPCONV_RULE:imp_conv->thm->thm =
  fun c th ->
    let t = concl th in
    MATCH_MP (c Contra t) th

(* From an implicational conversion builds a tactic. *)
let IMPCONV_TAC:imp_conv->tactic =
  fun cnv (_,c as g) ->
    (MATCH_MP_TAC (cnv Co c) THEN TRY (ACCEPT_TAC TRUTH)) g


(*****************************************************************************)
(* CONTEXT HANDLING                                                          *)
(*****************************************************************************)

(* [term list] = terms to add to the context *)
type 'a with_context =
  With_context of 'a * (Tset.t -> 'a with_context) * (term -> 'a with_context)

let apply (With_context(c,_,_)) = c

(* Maybe avoid the augment if the input list is empty? *)
let augment (With_context(_,a,_)) = a
let diminish (With_context(_,_,d)) = d
let apply_with_context c ctx v t =
  DISCH_CONJ ctx (apply (augment c (Tset.strip_conj ctx)) v t)

let imp_conv_of_ctx_imp_conv = (apply:imp_conv with_context -> imp_conv)

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Co C] returns [D ==> C],
 * then [CONJ_IMPCONV ic1 ic2 Co (A /\ C)] returns [B /\ D ==> A /\ C].
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Contra C] returns
 * [C ==> D], then [CONJ_IMPCONV ic1 ic2 Contra (A /\ B)]
 * returns [A /\ B ==> C /\ D].
 *
 * Additionally takes the context into account, i.e., if [ic2 Co C] returns
 * [A |- D ==> C],
 * then [CONJ_IMPCONV ic1 ic2 Co (A /\ B)] returns [|- C /\ D ==> A /\ B]
 * (i.e., [A] does not appear in the hypotheses).
 *)
let rec CONJ_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_conj t in
      match v with
      |Co ->
          (try
            let th1 = apply c Co t1 in
            try
              let t1' = imp_conv_outcome th1 Co in
              MKIMP_CONJ_CO_CTXT th1 (apply_with_context c t1' Co t2)
              with Failure _ -> MKIMPL_CONJ_CO_CTXT th1 t2
          with Failure _ -> MKIMPR_CONJ_CO_CTXT (apply_with_context c t1 Co t2))
      |Contra ->
          try
            (* note: we remove t1 in case it appears in t2, since otherwise,
             * t1 removes t2 and t2 removes t1
             *)
            let t2s = Tset.remove (Tset.strip_conj t2) t1 in
            let th1 = apply (augment c t2s) Contra t1 in
              try
                let t1' = imp_conv_outcome th1 Contra in
                let t1s = Tset.strip_conj t1 and t1s' = Tset.strip_conj t1' in
                let t1s'' = Tset.union t1s t1s' in
                let th2 = apply (augment c t1s'') Contra t2 in
                let th2' = DISCH_CONJ t1 (DISCH_CONJ t1' th2) in
                MKIMP_CONJ_CONTRA_CTXT (DISCH_CONJ t2 th1) th2'
              with Failure _ -> MKIMPL_CONJ_CONTRA_CTXT (DISCH_CONJ t2 th1)
            with Failure _ ->
              MKIMPR_CONJ_CONTRA_CTXT (apply_with_context c t1 Contra t2))
      :imp_conv),
    CONJ_CTXIMPCONV o augment c,
    CONJ_CTXIMPCONV o diminish c)

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Co C] returns [D ==> C],
 * then [DISJ_IMPCONV ic1 ic2 Co (A \/ C)] returns [B \/ D ==> A \/ C].
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Contra C] returns
 * [C ==> D], then [DISJ_IMPCONV ic1 ic2 Contra (A \/ B)]
 * returns [A \/ B ==> C \/ D].
 *)
let rec DISJ_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_disj t in
      try
        let th1 = apply c v t1 in
        try MKIMP_DISJ th1 (apply c v t2) with Failure _ -> MKIMPL_DISJ th1 t2
      with Failure _ -> MKIMPR_DISJ t1 (apply c v t2)):imp_conv),
    DISJ_CTXIMPCONV o augment c,
    DISJ_CTXIMPCONV o diminish c)

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Co C] returns [D ==> C],
 * then [IMP_IMPCONV ic1 ic2 Co (A ==> C)] returns [(B ==> D) ==> (A ==> C)].
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Contra C] returns
 * [C ==> D], then [IMP_IMPCONV ic1 ic2 Contra (A ==> C)]
 * returns [(A ==> C) ==> (B ==> D)].
 *
 * Additionally takes the context into account, i.e., if [ic2 Co C] returns
 * [B |- D ==> C], then [IMP_IMPCONV ic1 ic2 Co (A ==> C)] returns
 * [|- (B ==> D) ==> (A ==> C)] (i.e., [B] does not appear in the hypotheses).
 *)
let rec IMP_CTXIMPCONV (c:imp_conv with_context)  =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_imp t in
      try
        let v' = Variance.neg v in
        let th1 = apply c v' t1 in
        let t1' = imp_conv_outcome th1 v' in
        let t1s = Tset.union (Tset.strip_conj t1) (Tset.strip_conj t1') in
        let c' = augment c t1s in
        let mk =
          match v with Co -> MKIMP_IMP_CO_CTXT | Contra -> MKIMP_IMP_CONTRA_CTXT
        in
        try mk th1 (DISCH_CONJ t1 (DISCH_CONJ t1' (apply c' v t2)))
        with Failure _ -> MKIMPL_IMP th1 t2
      with Failure _ -> MKIMPR_IMP_CTXT (apply_with_context c t1 v t2)
      ):imp_conv),
    IMP_CTXIMPCONV o augment c,
    IMP_CTXIMPCONV o diminish c)

let rec IFF_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_iff t in
      let lr,l,r =
        match v with
        |Co -> MKIMP_CO_IFF,MKIMPL_CO_IFF,MKIMPR_CO_IFF
        |Contra -> MKIMP_CONTRA_IFF,MKIMPL_CONTRA_IFF,MKIMPR_CONTRA_IFF
      in
      (try
        let th1 = apply c v (mk_imp (t1,t2)) in
        try
          let th2 = apply c v (mk_imp (t2,t1)) in
          (try MKIMP_IFF th1 th2 with Failure _ -> lr th1 th2)
        with Failure _ -> l th1
      with Failure _ -> r (apply c v (mk_imp (t2,t1))))):imp_conv),
    IFF_CTXIMPCONV o augment c,
    IFF_CTXIMPCONV o diminish c)

(* Consider an implicational conversion ic.
 * Suppose [ic Contra A] returns [A ==> B]
 * then [NOT_IMPCONV ic Co ~A] returns [~B ==> ~A].
 * Suppose [ic Co A] returns [B ==> A]
 * then [NOT_IMPCONV ic Contra ~A] returns [~A ==> ~B].
 *)
let rec NOT_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t -> MKIMP_NOT (apply c (Variance.neg v) (dest_neg t))):imp_conv),
    NOT_CTXIMPCONV o augment c,
    NOT_CTXIMPCONV o diminish c)

let rec QUANT_CTXIMPCONV mkimp sel (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let x,b = sel t in
      let c' = diminish c x in
      mkimp x (apply c' v b)):imp_conv),
    QUANT_CTXIMPCONV mkimp sel o augment c,
    QUANT_CTXIMPCONV mkimp sel o diminish c)

(* Consider an implicational conversion ic.
 * Suppose [ic Co A] returns [B ==> A]
 * then [FORALL_IMPCONV ic Co (!x.A)] returns [(!x.B) ==> (!x.A)].
 * Suppose [ic Contra A] returns [A ==> B]
 * then [FORALL_IMPCONV ic Contra (!x.A)] returns [(!x.A) ==> (!x.B)].
 *)
let FORALL_CTXIMPCONV = QUANT_CTXIMPCONV MKIMP_FORALL dest_forall

(* Consider an implicational conversion ic.
 * Suppose [ic Co A] returns [B ==> A]
 * then [EXISTS_IMPCONV ic Co (?x.A)] returns [(?x.B) ==> (?x.A)].
 * Suppose [ic Contra A] returns [A ==> B]
 * then [EXISTS_IMPCONV ic Contra (?x.A)] returns [(?x.A) ==> (?x.B)].
 *)
let EXISTS_CTXIMPCONV = QUANT_CTXIMPCONV MKIMP_EXISTS dest_exists

(* Applies an implicational conversion on the subformula(s) of the input term*)
let rec SUB_CTXIMPCONV =
  let iff_ty = `:bool->bool->bool` in
  fun c ->
    With_context(
    ((fun v t ->
      let n,ty = dest_const (fst (strip_comb t)) in
      apply
        ((match n with
        |"==>" -> IMP_CTXIMPCONV
        |"/\\" -> CONJ_CTXIMPCONV
        |"\\/" -> DISJ_CTXIMPCONV
        |"=" when ty = iff_ty -> IFF_CTXIMPCONV
        |"!" -> FORALL_CTXIMPCONV
        |"?" -> EXISTS_CTXIMPCONV
        |"~" -> NOT_CTXIMPCONV
        |_ -> failwith "SUB_CTXIMPCONV") c)
        v t):imp_conv),
    SUB_CTXIMPCONV o augment c,
    SUB_CTXIMPCONV o diminish c)

(* Takes a theorem which results of an implicational conversion and applies
 * another implicational conversion on the outcome.
 *)
let bind_ctximpconv (c:imp_conv with_context) v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> IMP_TRANS (apply c v t1) th
  |Contra -> IMP_TRANS th (apply c v t2)

let rec BIND_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v th -> bind_ctximpconv c v th),
    BIND_CTXIMPCONV o augment c,
    BIND_CTXIMPCONV o diminish c))

(* Sequential combinator. *)
let rec THEN_CTXIMPCONV (c1:imp_conv with_context) (c2:imp_conv with_context) =
  With_context(
    ((fun v t -> bind_ctximpconv c2 v (apply c1 v t)):imp_conv),
    (fun x -> THEN_CTXIMPCONV (augment c1 x) (augment c2 x)),
    (fun x -> THEN_CTXIMPCONV (diminish c1 x) (diminish c2 x)))

(* Try combinator *)
let rec TRY_CTXIMPCONV (c:imp_conv with_context) =
    With_context(
      ((fun v t ->
        try apply c v t
        with Failure _ | Unchanged -> ALL_IMPCONV v t):imp_conv),
      TRY_CTXIMPCONV o augment c,
      TRY_CTXIMPCONV o diminish c)


(* Applies the first of two implicational conversions that succeeds. *)
let rec ORELSE_CTXIMPCONV
  (c1:imp_conv with_context) (c2:imp_conv with_context) =
  With_context(
    ((fun v t -> try apply c1 v t with Failure _ -> apply c2 v t):imp_conv),
    (fun x -> ORELSE_CTXIMPCONV (augment c1 x) (augment c2 x)),
    (fun x -> ORELSE_CTXIMPCONV (diminish c1 x) (diminish c2 x)))

(* Makes an implicational conversion fail if applying it leaves a term
 * unchanged.
 *)
let rec CHANGED_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let th = apply c v t in
      let l,r = dest_imp (concl th) in
      if aconv l r then failwith "CHANGED_CTXIMPCONV" else th):imp_conv),
    CHANGED_CTXIMPCONV o augment c,
    CHANGED_CTXIMPCONV o diminish c)

let rec UNCHANGED_OF_FAIL_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t -> try apply c v t with Failure _ -> raise Unchanged
      ):imp_conv),
    UNCHANGED_OF_FAIL_CTXIMPCONV o augment c,
    UNCHANGED_OF_FAIL_CTXIMPCONV o diminish c)

let rec REPEAT_UNCHANGED_CTXIMPCONV =
  let rec map_all f xs x =
    match xs with
    |[] -> []
    |y::ys -> f y x :: map_all f ys x
  in
  fun (cs:imp_conv with_context list) ->
    With_context(
      ((fun v t ->
        let rec loop changed acc = function
          |[] when changed -> loop false acc cs
          |[] -> acc
          |c::cs' ->
              try
                let acc' = bind_ctximpconv c v acc in
                loop true acc' cs'
              with Unchanged -> loop changed acc cs'
        in
        loop false (IMP_REFL t) cs):imp_conv),
      REPEAT_UNCHANGED_CTXIMPCONV o map_all augment cs,
      REPEAT_UNCHANGED_CTXIMPCONV o map_all diminish cs)


type atomic = Atomic | Non_atomic

let DEPTH_CTXIMPCONV =
  let bind c na v th =
    let t1,t2 = dest_imp (concl th) in
    match v with
    |Co -> IMP_TRANS (apply c na v t1) th
    |Contra -> IMP_TRANS th (apply c na v t2)
  in
  let rec self (c:(atomic->imp_conv) with_context) =
    With_context(
      (fun v t ->
        try
          let th1 = apply (SUB_CTXIMPCONV (self c)) v t in
          (try bind c Non_atomic v th1 with Failure _ -> th1)
        with
        | Failure "SUB_CTXIMPCONV" ->
          let th1 = apply c Atomic v t in
          (try bind_ctximpconv (self c) v th1 with Failure _ -> th1)
        | Failure _ -> apply c Non_atomic v t),
      self o augment c,
      self o diminish c)
  in
  UNCHANGED_OF_FAIL_CTXIMPCONV o self

let TOP_DEPTH_CTXIMPCONV =
  let rec self (c:imp_conv with_context) =
    With_context(
      (fun v t ->
        try
          let th = apply c v t in
          try bind_ctximpconv (self c) v th with Failure _ -> th
        with Failure _ -> apply (SUB_CTXIMPCONV (self c)) v t),
      self o augment c,
      self o diminish c)
  in
  UNCHANGED_OF_FAIL_CTXIMPCONV o self

let ONCE_DEPTH_CTXIMPCONV =
  let rec self (c:(atomic->imp_conv) with_context) =
    With_context(
      (fun v t ->
        try apply (SUB_CTXIMPCONV (self c)) v t
        with
        | Failure "SUB_CTXIMPCONV" -> apply c Atomic v t
        | Failure _ -> apply c Non_atomic v t),
      self o augment c,
      self o diminish c)
  in
  UNCHANGED_OF_FAIL_CTXIMPCONV o self


let CTXIMPCONV_RULE (c:imp_conv with_context) th =
  MATCH_MP (apply c Contra (concl th)) th

let CTXIMPCONV_TAC (cnv:imp_conv with_context) : tactic =
  fun (asms,c as g) ->
    let cnv' = augment cnv (map (concl o snd) asms) in
    (MATCH_MP_TAC (apply cnv' Co c) THEN TRY (ACCEPT_TAC TRUTH)) g

(*****************************************************************************)
(* REWRITE IMPLICATIONAL CONVERSION                                          *)
(*****************************************************************************)

(* Given a theorem [H1,...,Hn |- P ==> l = r],
 * returns the variables that occur in [P] and [r] but not in the rest.
 * Basically represents the variables that are introduced by the implicational
 * rewrite (similar status as variables occurring in the r.h.s. of a rewrite
 * but not in the l.h.s.).
 *)
let indep_vars th =
  let hs,c = dest_thm (SPEC_ALL th) in
  let p,c = dest_imp c in
  let all_vars = union (frees p) (frees (rhs c)) in
  let dep_vars = union (frees (lhs c)) (freesl hs) in
  subtract all_vars dep_vars

(* Given a list of variables to avoid [v1,...,vk], a theorem of the form
 * [hs |- !x1...xn. p ==> !y1...ym. l = r], and a term [t], matches [t] with
 * [l], yielding the substitution [s], and returns the theorem
 * [s(hs) |- !z1...zp. s(p) ==> s(l) = s(r)] where [z1], ..., [zp] are the
 * variables among [x1], ..., [xn], [y1], ..., [ym] that are not instantiated
 * by [s], and renamed so as to avoid [v1], ..., [vk].
 *)
let GEN_IMPREWR_CONV avs =
  let sel = lhs o snd o strip_forall o snd o dest_imp in
  let pmatch = GEN_PART_MATCH_ALL sel in
  fun th ->
    let pmatch' = pmatch th in
    fun t ->
      let th' = pmatch' t in
      VARIANT_RULE avs (GENL (indep_vars th') th')

(* A conversion which returns not only a theorem but also a list of terms
 * which is a sublist of the theorem hypotheses, and a list of terms which
 * are the variables newly introduced by the conversion.
 *
 * See [IMPREWR_CONV] for an example.
 *)
type annot_conv = term -> thm * term option * term list

(* Takes a list of variables to avoid [av], a theorem [th] of the form
 * [h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r], and a term [t]
 * and returns a conversion with hypotheses defined as follows:
 * for a term [t], if [t] matches [l] with substitution [s], then return
 * the theorem [h1,...,hk,s(p) |- t = s(r)] and the the list containing only
 * [s(p)].
 *
 * The purpose of the conversion with hypothesis is to be able to distinguish
 * which hypothesis comes from the input theorem and which is added by the
 * conversion itself.
 *)
let IMPREWR_CONV:Tset.t->thm->annot_conv =
  fun avs th ->
    let f t = SPEC_VARS (GEN_IMPREWR_CONV avs th t) in
    fun t ->
      let vs,uh = f t in
      let u = fst (dest_imp (concl uh)) in
      UNDISCH uh,Some u,Tset.of_list vs

let REWR_ANNOTCONV avs th t =
  let th' = PART_MATCH lhs th t in
  let _,t' = dest_binary_blind (concl th') in
  let new_vars = Tset.frees t' in
  let old_vars = Tset.union (Tset.frees t) (Tset.freesl (hyp th')) in
  th',None,Tset.subtract new_vars old_vars

let ORDER_ANNOTCONV cnv t =
  let th,_,_ as res = cnv t in
  let l,r = dest_binary_blind (concl th) in
  if term_order l r then res else failwith "ORDER_ANNOTCONV"

(* Takes a theorem, a net of conversions with hypotheses (which also take
 * variables to avoid), and adds to the net the conversion corresponding to
 * the theorem.
 *
 * Special cases:
 * - usual term rewriting is handled with [REWR_CONV] instead of introducing
 *   a fake premise. Might be useful though to introduce a fake premise since
 *   the conversion would benefit from a better handling of variables occurring
 *   in the r.h.s. but not in the l.h.s.
 * - a theorem of the form [p ==> c] where [c] is not equational is turned into
 *   [p ==> c = T]
 * - a theorem of the form [p ==> ~c] is turned into [p ==> c = F]
 *)
let pat_cnv_of_thm th : (term * (term list->annot_conv)) =
  let th = SPEC_ALL th in
  let lconsts = freesl (hyp th) and c = concl th in
  match c with
  |Comb(Comb(Const("=",_),l),r) as t ->
      let matches = C (can o term_match lconsts) in
      if free_in l r || (matches l r && matches r l)
      then t,C REWR_ANNOTCONV (MAP_FORALL_BODY EQT_INTRO th)
      else l,C REWR_ANNOTCONV th
  |Comb(Comb(Const("==>",_),p),c) as t ->
      let matches = C (can o fo_term_match lconsts) in
      let imprewr_concl f = C IMPREWR_CONV (GEN_MAP_CONCLUSION f th) in
      (match c with
      |Comb(Comb(Const("=",_),l),r) ->
          if free_in l r || (matches l r && matches r l) || is_var l
          then
            if matches p c
            then t, C REWR_ANNOTCONV (EQT_INTRO th)
            else c, imprewr_concl EQT_INTRO
          else l, C IMPREWR_CONV th
      |Comb(Const("~",_),l) -> l, imprewr_concl EQF_INTRO
      |l -> l, imprewr_concl EQT_INTRO)
  |Comb(Const("~",_),l) -> l, C REWR_ANNOTCONV (EQF_INTRO th)
  |Const("T",bool_ty) -> failwith "pat_cnv_of_thm"
  |l -> l, C REWR_ANNOTCONV (EQT_INTRO th)

let impconv_net_of_thm th =
  try
    let p,c = pat_cnv_of_thm th in
    let vs = Tset.freesl (hyp th) in
    Fo_nets.enter vs (p,(c,vs,th))
  with Failure _ -> I

let patterns_of_thm = fst o pat_cnv_of_thm

(* Apply a conversion net to the term at the top level, taking
 * avoided variables as parameter too.
 *)
let REWRITES_IMPCONV
  (net:((term list -> annot_conv) * Tset.t * thm) Fo_nets.t) avs t =
  tryfind (fun c,_,_ -> c avs t) (Fo_nets.lookup t net)

let extra_basic_rewrites =
  itlist (mk_rewrites false) [NOT_FORALL_THM;NOT_IMP] []

let IMPREWR_CTXCONV :thm list -> (atomic->annot_conv) with_context =
  let rec top_depth c avs t =
    let rec (++) c1 c2 avs t =
      match c1 avs t with
      |_,Some _,_ as c1t -> c1t
      |th1,None,vs1 as c1t ->
        (try
          let th2,ho2,vs2 = c2 (Tset.union vs1 avs) (rand (concl th1)) in
          TRANS th1 th2, ho2, Tset.union vs1 vs2
        with Failure _ -> c1t)
    and (+) c1 c2 avs t = try (c1 ++ c2) avs t with Failure _ -> c2 avs t
    and COMB_QCONV c avs l r =
      try
        match c avs l with
        |th,(Some _ as ho),vs -> AP_THM th r,ho,vs
        |th1,None,vs1 ->
          (try
            let th2,ho2,vs2 = c (Tset.union vs1 avs) r in
            MK_COMB (th1,th2), ho2, Tset.union vs1 vs2
          with Failure _ -> AP_THM th1 r,None,vs1)
      with Failure _ ->
        let th2,ho2,vs2 = c avs r in
        AP_TERM l th2,ho2,vs2
    in
    let SUB_QCONV c avs t =
      match t with
      |Comb(l,r) -> COMB_QCONV c avs l r
      |Abs(v,_) ->
          let ho = ref None and vs = ref [] in
          let c' t =
            let th,ho',vs' = c (Tset.insert avs v) t in
            ho := ho'; vs := vs'; th
          in
          let res = ABS_CONV c' t in
          res,!ho,!vs
      |_ -> failwith "SUB_QCONV"
    in
    let rec (!) c avs t = (c ++ !c) avs t in
    (!c + (SUB_QCONV (top_depth c) ++ top_depth c)) avs t
  in
  let bigger_net() =
    itlist (net_of_thm false) extra_basic_rewrites (basic_net()) in
  let basic_cnv t = REWRITES_CONV (bigger_net ()) t,None,[] in
  let rec self net ths =
    let avs = Tset.flat_revmap (Tset.freesl o hyp) ths in
    let cnv avs t =
      try REWRITES_IMPCONV net avs t with Failure _ -> basic_cnv t
    in
    With_context(
      (fun a t ->
        let f = match a with Atomic -> top_depth | Non_atomic -> I in
        f cnv (Tset.union (Tset.frees t) avs) t),
      (fun ts ->
        let ths' = map ASSUME ts in
        (*let ths'' = ths' @ GMATCH_MPS ths ths' in*)
        let ths'' = MP_CLOSURE ths' ths' @ ths' @ MP_CLOSURE ths ths' in
        self (itlist impconv_net_of_thm ths'' net) (ths'' @ ths)),
      (fun v ->
        let ths = ref [] in
        let f (_,vs,th) =
          if not (Tset.mem v vs) then (ths := th :: !ths; true) else false
        in
        let net' = Fo_nets.filter f net in
        self net' !ths))
  in
  fun ths -> self (itlist impconv_net_of_thm ths Fo_nets.empty_net) ths


(*****************************************************************************)
(* SOME USEFUL IMPLICATIONAL CONVERSIONS                                     *)
(*****************************************************************************)

(* Takes a conversion with hypotheses (with context) and makes an
 * implicational conversion out of it.
 * Basically turns a rewrite with hypotheses into an implicational rewrite
 * withouth hypotheses.
 * Adds existential quantifications for variables introduced by the rewrite.
 *)
let rec REWR_IMPCONV_OF_CONV =
  let IMP_SYM = REWR_RULE (TAUT `A==>B==>C <=> B==>A==>C`) in
  let IMP_EXIST = GSYM LEFT_IMP_EXISTS_THM in
  let TRY_GEN v th = try GEN v th with Failure _ -> th in
  fun (c:(atomic -> annot_conv) with_context) ->
    With_context(
      ((fun a v t ->
        let th,ho,new_vars = apply c a t in
        let th1,th2 = EQ_IMP_RULE th in
        let res =
          match v with
          |Co ->
              let p,th2' = UNDISCH_TERM th2 in
              let rec exists_intro = function
                |[] -> DISCH_IMP_IMP (p::list_of_option ho) th2'
                |v::vs ->
                    let th = exists_intro vs in
                    try REWR_RULE IMP_EXIST (GEN v th) with Failure _ -> th
              in
              exists_intro new_vars
          |Contra ->
              let th1' =
                match ho with None -> th1 | Some h -> IMP_SYM (DISCH h th1)
              in
              match new_vars with
              |[] -> th1'
              |_::_ -> MAP_CONCLUSION (itlist TRY_GEN new_vars) th1'
        in
        let t1,t2 = dest_imp (concl res) in
        if t1 = t2 then raise Unchanged else res):atomic->imp_conv),
      REWR_IMPCONV_OF_CONV o augment c,
      REWR_IMPCONV_OF_CONV o diminish c)

(* Applies the implicational rewrite, with context simplifications. *)
let REWRITE_CTXIMPCONV =
  DEPTH_CTXIMPCONV o REWR_IMPCONV_OF_CONV o IMPREWR_CTXCONV


(*****************************************************************************)
(* INTERFACE                                                                 *)
(*****************************************************************************)

(* Preprocessor. For now takes a theorem of the form [p ==> c1 /\ ... /\ ck]
 * and returns the list of theorems [p ==> c1], ..., [p ==> ck].
 *)
let preprocess = CONJUNCTS o IMPLY_AND

(* Tactic for implicational rewrite. *)
let IMP_REWRITE_TAC ths = fail_if_unchanged
  (CTXIMPCONV_TAC (REWRITE_CTXIMPCONV (flat (map preprocess ths))))

let SEQ_IMP_REWRITE_TAC ths =
  let cnv =
    match ths with
    |[] -> REWRITE_CTXIMPCONV [TRUTH]
    |[th] -> REWRITE_CTXIMPCONV (preprocess th)
    |_::_ ->
        let fcnv = REWRITE_CTXIMPCONV o preprocess in
        REPEAT_UNCHANGED_CTXIMPCONV (map fcnv ths)
  in
  fail_if_unchanged (CTXIMPCONV_TAC cnv)

(* Tactic for implicational rewrite with assumptions. *)
let ASM_IMP_REWRITE_TAC = ASM IMP_REWRITE_TAC

(* Cases-like conversion for implicational theorems, i.e., for a theorem of
 * the form:
 * [h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r], and a term [t],
 * return [(p ==> t') /\ (~p ==> t)], where [t'] is the result of rewriting
 * [t] by [l=r].
 *)
let rec CASE_REWR_IMPCONV_OF_CONV =
  let MP_TAUT th = MATCH_MP (TAUT th) in
  let MP_LEM1 = MP_TAUT `(~P ==> Q = R) ==> (Q <=> (~P ==> R) /\ (P ==> Q))` in
  let MP_LEM2 = MP_TAUT `(P ==> Q = R) ==> (Q <=> (P ==> R) /\ (~P ==> Q))` in
  fun (c:(atomic -> annot_conv) with_context) ->
    With_context(
      (fun a v t ->
        match apply c a t with
        |_,None,_ -> failwith "CASE_REWR_IMPCONV_OF_CONV"
        |th,Some h,_ ->
            let th' = DISCH h th in
            let th'' = try MP_LEM1 th' with Failure _ -> MP_LEM2 th' in
            imp_conv_of_conv (REWR_CONV th'') v t),
      CASE_REWR_IMPCONV_OF_CONV o augment c,
      CASE_REWR_IMPCONV_OF_CONV o diminish c)

let CASE_REWRITE_CTXIMPCONV =
  ONCE_DEPTH_CTXIMPCONV o CASE_REWR_IMPCONV_OF_CONV o IMPREWR_CTXCONV

(* Tactic version of it. *)
let CASE_REWRITE_TAC = fail_if_unchanged
  (CTXIMPCONV_TAC o CASE_REWRITE_CTXIMPCONV o preprocess)

(*****************************************************************************)
(* IMPLICATIONAL CONVERSIONS WITH MULTIPLE RESULTS                           *)
(*****************************************************************************)

(* Multiple implicational conversion. *)
type imp_mconv = Variance.t -> term -> thm list

let mapply_with_context c ctx v t =
  map (DISCH_CONJ ctx) (apply (augment c (Tset.strip_conj ctx)) v t)

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [CONJ_IMPMCONV ic1 ic2 Co (A /\ C)] returns
 * [B1 /\ C ==> A /\ C; ...; Bk /\ C ==> A /\ C; A /\ D1 ==> A /\ C; ...; Dn
 * ==> A /\ C].
 *
 * And similarly for the contravariant case.
 *)
let rec CONJ_CTXIMPMCONV (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let t1,t2 = dest_conj t in
      let left,right =
        match v with
        |Co -> MKIMPL_CONJ_CO2_CTXT,MKIMPR_CONJ_CO_CTXT
        |Contra -> MKIMPL_CONJ_CONTRA_CTXT,MKIMPR_CONJ_CONTRA_CTXT
      in
      let th1s = map left (mapply_with_context c t2 v t1) in
      let th2s = map right (mapply_with_context c t1 v t2) in
      th1s @ th2s),
    CONJ_CTXIMPMCONV o augment c,
    CONJ_CTXIMPMCONV o diminish c)

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [DISJ_IMPMCONV ic1 ic2 Co (A \/ C)] returns
 * [B1 \/ C ==> A \/ C; ...; Bk \/ C ==> A \/ C; A \/ D1 ==> A \/ C; ...; Dn
 * ==> A \/ C].
 *
 * And similarly for the contravariant case.
 *)
let rec DISJ_CTXIMPMCONV (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let t1,t2 = dest_disj t in
      let th1s = map (C MKIMPL_DISJ t2) (apply c v t1) in
      let th2s = map (MKIMPR_DISJ t1) (apply c v t2) in
      th1s @ th2s),
    DISJ_CTXIMPMCONV o augment c,
    DISJ_CTXIMPMCONV o diminish c)

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Contra A] returns a list [A ==> B1; ...; A ==> Bk],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [DISJ_IMPMCONV ic1 ic2 Co (A \/ C)] returns
 * [(B1 ==> C) ==> (A ==> C); ...; (Bk ==> C) ==> (A ==> C); (A ==> D1) ==> (A
 * ==> C); ...; (A ==> Dn) ==> (A ==> C)].
 *
 * And similarly for the contravariant case.
 *)
let rec IMP_CTXIMPMCONV (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let t1,t2 = dest_imp t in
      let th1s = map (C MKIMPL_IMP t2) (apply c (Variance.neg v) t1) in
      let th2s = map MKIMPR_IMP_CTXT (mapply_with_context c t1 v t2) in
      th1s @ th2s),
    CONJ_CTXIMPMCONV o augment c,
    CONJ_CTXIMPMCONV o diminish c)

let rec IFF_CTXIMPCONV (c:imp_mconv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_iff t in
      let left,right =
        match v with
        |Co -> MKIMPL_CO_IFF,MKIMPR_CO_IFF
        |Contra -> MKIMPL_CONTRA_IFF,MKIMPR_CONTRA_IFF
      in
      let th1s = map left (apply c v (mk_imp(t1,t2))) in
      let th2s = map right (apply c v (mk_imp(t2,t1))) in
      th1s @ th2s):imp_mconv),
    IFF_CTXIMPCONV o augment c,
    IFF_CTXIMPCONV o diminish c)

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Contra A] returns a list [A ==> B1; ...; A ==> Bk],
 * then [NOT_IMPMCONV ic Co ~A] returns [~B1 ==> ~A; ...; ~Bk ==> ~A].
 *
 * And similarly for the contravariant case.
 *)
let rec NOT_CTXIMPMCONV (c:imp_mconv with_context) : imp_mconv with_context =
  With_context(
    (fun v t ->
      map MKIMP_NOT (try_list (apply c (Variance.neg v)) (dest_neg t))),
    NOT_CTXIMPMCONV o augment c,
    NOT_CTXIMPMCONV o diminish c)

let rec QUANT_CTXIMPMCONV mkimp sel (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let x,b = sel t in
      let c' = diminish c x in
      map (mkimp x) (try_list (apply c' v) b)),
    QUANT_CTXIMPMCONV mkimp sel o augment c,
    QUANT_CTXIMPMCONV mkimp sel o diminish c)

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * then [FORALL_IMPMCONV ic Co (!x.A)] returns [(!x.B1) ==> (!x.A); ...;
 * (!x.Bk) ==> (!x.A)].
 *
 * And similarly for the contravariant case.
 *)
let FORALL_CTXIMPMCONV = QUANT_CTXIMPMCONV MKIMP_FORALL dest_forall

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * then [EXISTS_IMPMCONV ic Co (?x.A)] returns [(?x.B1) ==> (?x.A); ...;
 * (?x.Bk) ==> (?x.A)].
 *
 * And similarly for the contravariant case.
 *)
let EXISTS_CTXIMPMCONV = QUANT_CTXIMPMCONV MKIMP_EXISTS dest_exists

(* Applies a multiple implicational conversion on the subformula(s) of the
 * input term
 *)
let rec SUB_CTXIMPMCONV =
  let iff_ty = `:bool->bool->bool` in
  fun c ->
  With_context(
    ((fun v t ->
      let n,ty = dest_const (fst (strip_comb t)) in
      apply
        ((match n with
        |"==>" -> IMP_CTXIMPMCONV
        |"/\\" -> CONJ_CTXIMPMCONV
        |"\\/" -> DISJ_CTXIMPMCONV
        |"!" -> FORALL_CTXIMPMCONV
        |"?" -> EXISTS_CTXIMPMCONV
        |"~" -> NOT_CTXIMPMCONV
        |"=" when ty = iff_ty -> IFF_CTXIMPCONV
        |_ -> failwith "SUB_CTXIMPMCONV") c) v t):imp_mconv),
    SUB_CTXIMPMCONV o augment c,
    SUB_CTXIMPMCONV o diminish c)


(* Applies a multiple implicational conversion once to the first suitable sub-term(s)
 * encountered in bottom-up order.
 *)
let rec DEPTH_CTXIMPMCONV (c : (atomic->imp_mconv) with_context) =
  With_context(
    (fun v t ->
      try
        let ths = apply (SUB_CTXIMPMCONV (DEPTH_CTXIMPMCONV c)) v t in
        apply c Non_atomic v t @ ths
      with Failure "SUB_CTXIMPMCONV" ->
        (apply c Atomic v t)),
      DEPTH_CTXIMPMCONV o augment c,
      DEPTH_CTXIMPMCONV o diminish c)


(*****************************************************************************)
(* REWRITE IMPLICATIONAL CONVERSIONS                                         *)
(*****************************************************************************)

(* Multiple implicational conversion with hypotheses. *)
type annot_mconv = term -> (thm * term option * term list) list

(* Takes a theorem, a net of conversions with hypotheses (which also take
 * variables to avoid), and adds to the net the conversion corresponding to
 * the theorem.
 *
 * Special cases:
 * - usual term rewriting is handled with [REWR_CONV] instead of introducing
 *   a fake premise. Might be useful though to introduce a fake premise since
 *   the conversion would benefit from a better handling of variables occurring
 *   in the r.h.s. but not in the l.h.s.
 * - a theorem of the form [p ==> c] where [c] is not equational is turned into
 *   [p ==> c = T]
 * - a theorem of the form [p ==> ~c] is turned into [p ==> c = F]
 *)
let target_pat_cnv_of_thm th : (term * (term list->annot_conv)) =
  let th = SPEC_ALL th in
  match concl th with
  |Comb(Comb(Const("=",_),l),_) -> l,C REWR_ANNOTCONV th
  |Comb(Comb(Const("==>",_),_),c) ->
      let pat,th' =
        match c with
        |Comb(Comb(Const("=",_),l),_) -> l, th
        |Comb(Const("~",_),l) -> l, GEN_MAP_CONCLUSION EQF_INTRO th
        |l -> c, GEN_MAP_CONCLUSION EQT_INTRO th
      in
      pat, C IMPREWR_CONV th'
  |Comb(Const("~",_),l) -> l, C REWR_ANNOTCONV (EQF_INTRO th)
  |Const("T",bool_ty) -> failwith "target_pat_cnv_of_thm"
  |l -> l, C REWR_ANNOTCONV (EQT_INTRO th)

let target_impconv_net_of_thm th =
  try
    let p,c = target_pat_cnv_of_thm th in
    let vs = Tset.freesl (hyp th) in
    Fo_nets.enter vs (p,(c,vs,th))
  with Failure _ -> I

let target_patterns_of_thm = fst o target_pat_cnv_of_thm

(* Multiple conversion which returns all the possible rewrites (on one subterm
 * only) by one theorem.
 *)

let DEEP_IMP_REWR_MCONV:thm list->(atomic->annot_mconv) with_context =
  let map_fst f (x,y,z) = f x,y,z in
  let COMB_MCONV c l r =
    map (map_fst (C AP_THM r)) (c l) @ map (map_fst (AP_TERM l)) (c r)
  and ABS_MCONV c v b =
    let ths = c b in
    try map (map_fst (ABS v)) ths
    with Failure _ ->
      let gv = genvar(type_of v) in
      let f (gth,ho,vs) =
        let gtm = concl gth in
        let l,r = dest_eq gtm in
        let v' = variant (frees gtm) v in
        let l' = alpha v' l and r' = alpha v' r in
        EQ_MP (ALPHA gtm (mk_eq(l',r'))) gth,ho,vs
      in
      let b' = vsubst[gv,v] b in
      map f (map (map_fst (ABS gv)) (c b'))
  in
  let SUB_MCONV c = function
    |Comb(l,r) -> COMB_MCONV c l r
    |Abs(v,b) -> ABS_MCONV c v b
    |Const _ | Var _ -> []
  in
  let rec top_depth c t = SUB_MCONV (top_depth c) t @ c t in
  let REWRITES_IMPCONV (net:((term list -> annot_conv) * Tset.t * thm) Fo_nets.t) avs t =
    mapfilter (fun c,_,_ -> c avs t) (Fo_nets.lookup t net)
  in
  let rec self net ths =
    let avs = Tset.flat_revmap (Tset.freesl o hyp) ths in
    With_context(
      (fun a t ->
        let avs' = Tset.union (Tset.frees t) avs in
        let cnv t = REWRITES_IMPCONV net avs' t in
        let f =
          match a with
          |Atomic -> top_depth
          |Non_atomic -> (fun cnv avs -> cnv avs)
        in
        f cnv t),
      (fun _ -> self net ths),
      (fun v ->
        let ths = ref [] in
        let f (_,vs,th) =
          if not (Tset.mem v vs) then (ths := th :: !ths; true) else false
        in
        let net' = Fo_nets.filter f net in
        self net' !ths))
  in
  fun ths ->
    self (itlist target_impconv_net_of_thm ths Fo_nets.empty_net) ths

(* Takes a multiple conversion with hypotheses (which also takes a context as
 * parameter) and makes a multiple implicational conversion out of it.
 *
 * Basically extends [GENERAL_REWRITE_IMPCONV] to the multiple conversion
 * case.
 *)
let rec REWR_IMPMCONV_OF_MCONV =
  let IMP_SYM = REWR_RULE (TAUT `A==>B==>C <=> B==>A==>C`) in
  let IMP_EXIST = GSYM LEFT_IMP_EXISTS_THM in
  let TRY_GEN v th = try GEN v th with Failure _ -> th in
  fun (c:(atomic -> annot_mconv) with_context) ->
    With_context(
      ((fun a v t ->
        let f (th,ho,new_vars) =
          let th1,th2 = EQ_IMP_RULE th in
          match v with
          |Co ->
              let p,th2' = UNDISCH_TERM th2 in
              let rec exists_intro = function
                |[] -> DISCH_IMP_IMP (p::list_of_option ho) th2'
                |v::vs ->
                    let th = exists_intro vs in
                    try REWR_RULE IMP_EXIST (GEN v th) with Failure _ -> th
              in
              exists_intro new_vars
          |Contra ->
              let th1' =
                match ho with None -> th1 | Some h -> IMP_SYM (DISCH h th1)
              in
              match new_vars with
              |[] -> th1'
              |_::_ -> MAP_CONCLUSION (itlist TRY_GEN new_vars) th1'
        in
        map f (apply c a t)):atomic->imp_mconv),
      REWR_IMPMCONV_OF_MCONV o augment c,
      REWR_IMPMCONV_OF_MCONV o diminish c)


(*****************************************************************************)
(* TARGET REWRITING                                                          *)
(*****************************************************************************)

let EXISTS_CTXIMPCONV:imp_conv with_context =
  let EXISTSs i p =
    let codom,dom = unzip i in
    let f i ps = vsubst [i] (snd (dest_exists (hd ps))) :: ps in
    let h::ps = rev_itlist f i [list_mk_exists(dom,p)] in
    rev_itlist EXISTS (zip ps (rev codom)) (ASSUME h)
  in
  let LEFT_FORALL_IMP = REWR_RULE LEFT_FORALL_IMP_THM in
  let rec self ts =
    With_context
    ((fun v t ->
      match v,t with
      |Co,Comb(Const("?",_),_) ->
          let vs,b = strip_exists t in
          let bs = strip_conj b in
          let hmatch (n,b) =
            match partition (C mem vs) (variables b) with
            |[],_ -> failwith "EXISTS_CTXIMPCONV"
            |_::_ as lvs,lcs ->
                fun h ->
                  match term_match lcs b h with
                  |_,i,j when filter (uncurry (<>)) j = [] ->
                      (if i = [] then zip lvs lvs else i),n
                  |_ -> failwith "EXISTS_CTXIMPCONV"
          in
          let s,n = tryfind_fun (mapfilteri (curry (tryfind o hmatch)) bs) ts in
          let th = EXISTSs (map (fun v -> rev_assocd v s v,v) vs) b in
          let th' = DISCH_HD th in
          let h = fst (dest_imp (concl th')) in
          (match strip_conj h with
          |[] -> assert false
          |[h] -> DISCH T_ th
          |_::_ as hs ->
            let hs1,h'::hs2 = chop_list n hs in
            let hs_th = CONJ_ACI_RULE (mk_eq(h,list_mk_conj (h'::(hs1@hs2)))) in
            let th1 = CONV_RULE (LAND_CONV (REWR_CONV hs_th)) th' in
            let th2 = UNDISCH (CONV_RULE (REWR_CONV IMP_CONJ) th1) in
            let vs' = subtract vs (map snd s) in
            let f v th = try LEFT_FORALL_IMP (GEN v th) with Failure _ -> th in
            itlist f vs' th2)
      |_ -> failwith "EXISTS_CTXIMPCONV"),
      (fun ts' -> self (Tset.union ts' ts)),
      (fun _ -> self ts))
  in
  self []

(* Takes a theorem which results of an implicational conversion and applies a
 * multiple implicational conversion on the outcome.
 *)
let bind_impmconv (c:imp_mconv) v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> map (C IMP_TRANS th) (c v t1)
  |Contra -> map (IMP_TRANS th) (c v t2)


(* Target rewrite implicational conversion:
 * [TARGET_REWRITE_IMPCONV sths ts] is an implicational conversion which
 * applies all the possible implicational rewrites on the input term until
 * one of the resulting terms matches one of the terms in [ts].
 *
 * Note that we allow several target terms and not just one. See
 * TARGET_REWRITE_TAC for a justification.
 *)
let TARGET_REWRITE_IMPCONV : thm list -> term list -> imp_conv =
  let PRE = apply (TRY_CTXIMPCONV (REWRITE_CTXIMPCONV [])) in
  let POST = TRY_CTXIMPCONV (TOP_DEPTH_CTXIMPCONV EXISTS_CTXIMPCONV) in
  fun sths ->
    let one_step_sths v uh =
      let pre v th = try bind_impconv PRE v th with Unchanged -> th in
      let post v = bind_ctximpconv POST v in
      let f =
        DEPTH_CTXIMPMCONV o REWR_IMPMCONV_OF_MCONV o DEEP_IMP_REWR_MCONV
      in
      map (post v) (bind_impmconv (apply (f sths)) v (pre v uh))
    in
    let flat l = uniq (itlist (merge thm_lt) l []) in
    fun ts v t ->
      let rec self ths =
        let pool = flat (map (mergesort thm_lt o one_step_sths v) ths) in
        let sel th = imp_conv_outcome th v in
        let is_one_sol g = (can o find_term o can o fo_term_match []) g o sel in
        let is_sol th = tryfind is_one_sol ts th in
        try bind_ctximpconv POST v (find is_sol pool)
        with _ ->
          match pool with
          |[] -> failwith "TARGET_REWRITE_IMPCONV: no path found"
          |_::_ -> self (map (bind_ctximpconv POST v) pool)
      in
      self [IMP_REFL t]

(* Tactic version of it.
 *
 * Since the target theorem is preprocessed, it can yield several theorems.
 * Therefore, there is not just one possible target pattern but several.
 *)
let TARGET_REWRITE_TAC sths th =
  let sths' = flat (map preprocess sths) in
  let ths = preprocess th and (+) = THEN_IMPCONV in
  fail_if_unchanged (IMPCONV_TAC
    (TARGET_REWRITE_IMPCONV sths' (map patterns_of_thm ths)
      + imp_conv_of_ctx_imp_conv (REWRITE_CTXIMPCONV ths)))

let HINT_EXISTS_TAC = fail_if_unchanged
  (CTXIMPCONV_TAC (TOP_DEPTH_CTXIMPCONV EXISTS_CTXIMPCONV))

end in

Impconv.IMP_REWRITE_TAC,
Impconv.TARGET_REWRITE_TAC,
Impconv.HINT_EXISTS_TAC,
Impconv.SEQ_IMP_REWRITE_TAC,
Impconv.CASE_REWRITE_TAC;;
