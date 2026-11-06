(* ========================================================================= *)
(* Version of the MESON procedure a la PTTP. Various search options.         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "canon.ml";;

(* ------------------------------------------------------------------------- *)
(* Some parameters controlling MESON behaviour.                              *)
(* ------------------------------------------------------------------------- *)

let meson_depth = ref false;;   (* Use depth not inference bound.            *)

let meson_prefine = ref true;;  (* Use Plaisted's positive refinement.       *)

let meson_dcutin = ref 1;;      (* Min size for d-and-c optimization cut-in. *)

let meson_skew = ref 3;;        (* Skew proof bias (one side is <= n / skew) *)

let meson_brand = ref false;;   (* Use Brand transformation                  *)

let meson_split_limit = ref 8;; (* Limit of case splits before MESON proper  *)

let meson_chatty = ref false;;  (* Old-style verbose MESON output            *)

(* ------------------------------------------------------------------------- *)
(* Prolog exception.                                                         *)
(* ------------------------------------------------------------------------- *)

exception Cut;;

(* ------------------------------------------------------------------------- *)
(* Shadow syntax for FOL terms in NNF. Functions and predicates have         *)
(* numeric codes, and negation is done by negating the predicate code.       *)
(* ------------------------------------------------------------------------- *)

type fol_term = Fvar of int
              | Fnapp of int * fol_term list;;

type fol_atom = int * fol_term list;;

type fol_form = Atom of fol_atom
               | Conj of fol_form * fol_form
               | Disj of fol_form * fol_form
               | Forallq of int * fol_form;;

(* ------------------------------------------------------------------------- *)
(* Type for recording a MESON proof tree.                                    *)
(* ------------------------------------------------------------------------- *)

type fol_goal =
  Subgoal of fol_atom * fol_goal list * (int * thm) *
             int * (fol_term * int)list;;

(* ------------------------------------------------------------------------- *)
(* General MESON procedure, using assumptions and with settable limits.      *)
(* ------------------------------------------------------------------------- *)

module Meson = struct

  let offinc = 10000
  and inferences = ref 0

  (* ----------------------------------------------------------------------- *)
  (* Negate a clause.                                                        *)
  (* ----------------------------------------------------------------------- *)

    let mk_negated (p,a) = -p,a

  (* ----------------------------------------------------------------------- *)
  (* Like partition, but with short-circuiting for special situation.        *)
  (* ----------------------------------------------------------------------- *)

  let qpartition p m =
    let rec qpartition l =
      if l == m then raise Unchanged else
      match l with
        [] -> raise Unchanged
      | (h::t) -> if p h then
                    try let yes,no = qpartition t in h::yes,no
                    with Unchanged -> [h],t
                  else
                    let yes,no = qpartition t in yes,h::no in
    function l -> try qpartition l
                  with Unchanged -> [],l

  (* ----------------------------------------------------------------------- *)
  (* Translate a term (in NNF) into the shadow syntax.                       *)
  (* ----------------------------------------------------------------------- *)

  let reset_vars,fol_of_var,hol_of_var =
    let vstore = ref []
    and gstore = ref []
    and vcounter = ref 0 in
    let inc_vcounter() =
      let n = !vcounter in
      let m = n + 1 in
      if m >= offinc then failwith "inc_vcounter: too many variables" else
      (vcounter := m; n) in
    let reset_vars() = vstore := []; gstore := []; vcounter := 0 in
    let fol_of_var v =
      let currentvars = !vstore in
      try assoc v currentvars with Failure _ ->
      let n = inc_vcounter() in
      vstore := (v,n)::currentvars; n in
    let hol_of_var v =
      try rev_assoc v (!vstore)
      with Failure _ -> rev_assoc v (!gstore) in
    let hol_of_bumped_var v =
      try hol_of_var v with Failure _ ->
      let v' = v mod offinc in
      let hv' = hol_of_var v' in
      let gv = genvar(type_of hv') in
      gstore := (gv,v)::(!gstore); gv in
    reset_vars,fol_of_var,hol_of_bumped_var

  let reset_consts,fol_of_const,hol_of_const =
    let false_tm = `F` in
    let cstore = ref ([]:(term * int)list)
    and ccounter = ref 2 in
    let reset_consts() = cstore := [false_tm,1]; ccounter := 2 in
    let fol_of_const c =
      let currentconsts = !cstore in
      try assoc c currentconsts with Failure _ ->
      let n = !ccounter in
      ccounter := n + 1; cstore := (c,n)::currentconsts; n in
    let hol_of_const c = rev_assoc c (!cstore) in
    reset_consts,fol_of_const,hol_of_const

  let rec fol_of_term env consts tm =
    if is_var tm && not (mem tm consts) then
      Fvar(fol_of_var tm)
    else
      let f,args = strip_comb tm in
      if mem f env then failwith "fol_of_term: higher order" else
      let ff = fol_of_const f in
      Fnapp(ff,map (fol_of_term env consts) args)

  let fol_of_atom env consts tm =
    let f,args = strip_comb tm in
    if mem f env then failwith "fol_of_atom: higher order" else
    let ff = fol_of_const f in
    ff,map (fol_of_term env consts) args

  let fol_of_literal env consts tm =
    try let tm' = dest_neg tm in
        let p,a = fol_of_atom env consts tm' in
        -p,a
    with Failure _ -> fol_of_atom env consts tm

  let rec fol_of_form env consts tm =
    try let v,bod = dest_forall tm in
        let fv = fol_of_var v in
        let fbod = fol_of_form (v::env) (subtract consts [v]) bod in
        Forallq(fv,fbod)
    with Failure _ -> try
        let l,r = dest_conj tm in
        let fl = fol_of_form env consts l
        and fr = fol_of_form env consts r in
        Conj(fl,fr)
    with Failure _ -> try
        let l,r = dest_disj tm in
        let fl = fol_of_form env consts l
        and fr = fol_of_form env consts r in
        Disj(fl,fr)
    with Failure _ ->
        Atom(fol_of_literal env consts tm)

  (* ----------------------------------------------------------------------- *)
  (* Further translation functions for HOL formulas.                         *)
  (* ----------------------------------------------------------------------- *)

  let rec hol_of_term tm =
    match tm with
      Fvar v -> hol_of_var v
    | Fnapp(f,args) -> list_mk_comb(hol_of_const f,map hol_of_term args)

  let hol_of_atom (p,args) =
    list_mk_comb(hol_of_const p,map hol_of_term args)

  let hol_of_literal (p,args) =
    if p < 0 then mk_neg(hol_of_atom(-p,args))
    else hol_of_atom (p,args)

  (* ----------------------------------------------------------------------- *)
  (* Versions of shadow syntax operations with variable bumping.             *)
  (* ----------------------------------------------------------------------- *)

  let rec fol_free_in v tm =
    match tm with
      Fvar x -> x = v
    | Fnapp(_,lis) -> exists (fol_free_in v) lis

  let rec fol_subst theta tm =
    match tm with
      Fvar v -> rev_assocd v theta tm
    | Fnapp(f,args) ->
          let args' = qmap (fol_subst theta) args in
          if args' == args then tm else Fnapp(f,args')

  let fol_inst theta ((p,args) as at:fol_atom) =
    let args' = qmap (fol_subst theta) args in
    if args' == args then at else p,args'

  let rec fol_subst_bump offset theta tm =
    match tm with
      Fvar v -> if v < offinc then
                 let v' = v + offset in
                 rev_assocd v' theta (Fvar(v'))
               else
                 rev_assocd v theta tm
    | Fnapp(f,args) ->
          let args' = qmap (fol_subst_bump offset theta) args in
          if args' == args then tm else Fnapp(f,args')

  let fol_inst_bump offset theta ((p,args) as at:fol_atom) =
    let args' = qmap (fol_subst_bump offset theta) args in
    if args' == args then at else p,args'

  (* ----------------------------------------------------------------------- *)
  (* Main unification function, maintaining a "graph" instantiation.         *)
  (* We implicitly apply an offset to variables in the second term, so this  *)
  (* is not symmetric between the arguments.                                 *)
  (* ----------------------------------------------------------------------- *)

  let rec istriv env x t =
    match t with
      Fvar y -> y = x ||
                (try let t' = rev_assoc y env in istriv env x t'
                 with Failure "find" -> false)
    | Fnapp(f,args) -> exists (istriv env x) args && failwith "cyclic"

  let rec fol_unify offset tm1 tm2 sofar =
    match tm1,tm2 with
      Fnapp(f,fargs),Fnapp(g,gargs) ->
          if f <> g then failwith "" else
          itlist2 (fol_unify offset) fargs gargs sofar
    | _,Fvar(x) ->
         (let x' = x + offset in
          try let tm2' = rev_assoc x' sofar in
              fol_unify 0 tm1 tm2' sofar
          with Failure "find" ->
              if istriv sofar x' tm1 then sofar
              else (tm1,x')::sofar)
    | Fvar(x),_ ->
         (try let tm1' = rev_assoc x sofar in
              fol_unify offset tm1' tm2 sofar
          with Failure "find" ->
              let tm2' = fol_subst_bump offset [] tm2 in
              if istriv sofar x tm2' then sofar
              else (tm2',x)::sofar)

  (* ----------------------------------------------------------------------- *)
  (* Test for equality under the pending instantiations.                     *)
  (* ----------------------------------------------------------------------- *)

  let rec fol_eq insts tm1 tm2 =
    tm1 == tm2 ||
    match tm1,tm2 with
      Fnapp(f,fargs),Fnapp(g,gargs) ->
          f = g && forall2 (fol_eq insts) fargs gargs
    | _,Fvar(x) ->
         (try let tm2' = rev_assoc x insts in
              fol_eq insts tm1 tm2'
          with Failure "find" ->
          try istriv insts x tm1 with Failure _ -> false)
    | Fvar(x),_ ->
         (try let tm1' = rev_assoc x insts in
              fol_eq insts tm1' tm2
          with Failure "find" ->
          try istriv insts x tm2 with Failure _ -> false)

  let fol_atom_eq insts (p1,args1) (p2,args2) =
    p1 = p2 && forall2 (fol_eq insts) args1 args2

  (* ----------------------------------------------------------------------- *)
  (* Cacheing continuations. Very crude, but it works remarkably well.       *)
  (* ----------------------------------------------------------------------- *)

  let cacheconts f =
    let memory = ref [] in
    fun (gg,(insts,offset,size) as input) ->
      if exists (fun (_,(insts',_,size')) ->
                     insts = insts' && (size <= size' || !meson_depth))
          (!memory)
      then failwith "cachecont"
      else memory := input::(!memory); f input

  (* ----------------------------------------------------------------------- *)
  (* Check ancestor list for repetition.                                     *)
  (* ----------------------------------------------------------------------- *)

  let checkan insts (p,a) ancestors =
    let p' = -p in
    let t' = (p',a) in
    try let ours = assoc p' ancestors in
        if exists (fun u -> fol_atom_eq insts t' (snd(fst u))) ours
        then failwith "checkan"
        else ancestors
    with Failure "find" -> ancestors

  (* ----------------------------------------------------------------------- *)
  (* Insert new goal's negation in ancestor clause, given refinement.        *)
  (* ----------------------------------------------------------------------- *)

  let insertan insts (p,a) ancestors =
    let p' = -p in
    let t' = (p',a) in
    let ourancp,otheranc =
      try remove (fun (pr,_) -> pr = p') ancestors
      with Failure _ -> (p',[]),ancestors in
    let ouranc = snd ourancp in
    if exists (fun u -> fol_atom_eq insts t' (snd(fst u))) ouranc
    then failwith "insertan: loop"
    else (p',(([],t'),(0,TRUTH))::ouranc)::otheranc

  (* ----------------------------------------------------------------------- *)
  (* Apply a multi-level "graph" instantiation.                              *)
  (* ----------------------------------------------------------------------- *)

  let rec fol_subst_partial insts tm =
    match tm with
      Fvar(v) -> (try let t = rev_assoc v insts in
                      fol_subst_partial insts t
                  with Failure "find" -> tm)
    | Fnapp(f,args) -> Fnapp(f,map (fol_subst_partial insts) args)

  (* ----------------------------------------------------------------------- *)
  (* Tease apart local and global instantiations.                            *)
  (* At the moment we also force a full evaluation; should eliminate this.   *)
  (* ----------------------------------------------------------------------- *)

  let separate_insts offset oldinsts newinsts =
    let locins,globins =
      qpartition (fun (_,v) -> offset <= v) oldinsts newinsts in
    if globins = oldinsts then
      map (fun (t,x) -> fol_subst_partial newinsts t,x) locins,oldinsts
    else
      map (fun (t,x) -> fol_subst_partial newinsts t,x) locins,
      map (fun (t,x) -> fol_subst_partial newinsts t,x) globins

  (* ----------------------------------------------------------------------- *)
  (* Perform basic MESON expansion.                                          *)
  (* ----------------------------------------------------------------------- *)

  let meson_single_expand loffset rule ((g,ancestors),(insts,offset,size)) =
    let (hyps,conc),tag = rule in
    let allins = rev_itlist2 (fol_unify loffset) (snd g) (snd conc) insts in
    let locin,globin = separate_insts offset insts allins in
    let mk_ihyp h =
      let h' = fol_inst_bump offset locin h in
      h',checkan insts h' ancestors in
    let newhyps =  map mk_ihyp hyps in
    inferences := !inferences + 1;
    newhyps,(globin,offset+offinc,size-length hyps)

  (* ----------------------------------------------------------------------- *)
  (* Perform first basic expansion which allows continuation call.           *)
  (* ----------------------------------------------------------------------- *)

  let meson_expand_cont loffset rules state cont =
    tryfind
     (fun r -> cont (snd r) (meson_single_expand loffset r state)) rules

  (* ----------------------------------------------------------------------- *)
  (* Try expansion and continuation call with ancestor or initial rule.      *)
  (* ----------------------------------------------------------------------- *)

  let meson_expand rules ((g,ancestors),((insts,offset,size) as tup)) cont =
    let pr = fst g in
    let newancestors = insertan insts g ancestors in
    let newstate = (g,newancestors),tup in
    try if !meson_prefine && pr > 0 then failwith "meson_expand" else
        let arules = assoc pr ancestors in
        meson_expand_cont 0 arules newstate cont
    with Cut -> failwith "meson_expand" | Failure _ ->
        try let crules =
              filter (fun ((h,_),_) -> length h <= size) (assoc pr rules) in
            meson_expand_cont offset crules newstate cont
        with Cut -> failwith "meson_expand"
           | Failure _ -> failwith "meson_expand"

  (* ----------------------------------------------------------------------- *)
  (* Simple Prolog engine organizing search and backtracking.                *)
  (* ----------------------------------------------------------------------- *)

  let expand_goal rules =
    let rec expand_goal depth ((g,_),(insts,offset,size) as state) cont =
      if depth < 0 then failwith "expand_goal: too deep" else
      meson_expand rules state
        (fun apprule (_,(pinsts,_,_) as newstate) ->
            expand_goals (depth-1) newstate
              (cacheconts(fun (gs,(newinsts,newoffset,newsize)) ->
                 let locin,globin = separate_insts offset pinsts newinsts in
                 let g' = Subgoal(g,gs,apprule,offset,locin) in
                 if globin = insts && gs = [] then
                   try cont(g',(globin,newoffset,size))
                   with Failure _ -> raise Cut
                 else
                   try cont(g',(globin,newoffset,newsize))
                   with Cut -> failwith "expand_goal"
                      | Failure _ -> failwith "expand_goal")))

    and expand_goals depth (gl,(insts,offset,size as tup)) cont =
      match gl with
        [] -> cont ([],tup)

      | [g] -> expand_goal depth (g,tup) (fun (g',stup) -> cont([g'],stup))

      | gl -> if size >= !meson_dcutin then
                let lsize = size / (!meson_skew) in
                let rsize = size - lsize in
                let lgoals,rgoals = chop_list (length gl / 2) gl in
                try expand_goals depth (lgoals,(insts,offset,lsize))
                     (cacheconts(fun (lg',(i,off,n)) ->
                         expand_goals depth (rgoals,(i,off,n + rsize))
                           (cacheconts(fun (rg',ztup) -> cont (lg'@rg',ztup)))))
                with Failure _ ->
                    expand_goals depth (rgoals,(insts,offset,lsize))
                      (cacheconts(fun (rg',(i,off,n)) ->
                         expand_goals depth (lgoals,(i,off,n + rsize))
                           (cacheconts (fun (lg',((_,_,fsize) as ztup)) ->
                              if n + rsize <= lsize + fsize
                              then failwith "repetition of demigoal pair"
                              else cont (lg'@rg',ztup)))))
              else
                let g::gs = gl in
                expand_goal depth (g,tup)
                  (cacheconts(fun (g',stup) ->
                      expand_goals depth (gs,stup)
                        (cacheconts(fun (gs',ftup) -> cont(g'::gs',ftup))))) in

    fun g maxdep maxinf cont ->
      expand_goal maxdep (g,([],2 * offinc,maxinf)) cont

  (* ----------------------------------------------------------------------- *)
  (* With iterative deepening of inferences or depth.                        *)
  (* ----------------------------------------------------------------------- *)

  let solve_goal rules incdepth min max incsize =
    let rec solve n g =
      if n > max then failwith "solve_goal: Too deep" else
      (if !meson_chatty && !verbose then
        (Format.print_string
          ((string_of_int (!inferences))^" inferences so far. "^
              "Searching with maximum size "^(string_of_int n)^".");
         Format.print_newline())
       else if !verbose then
        (Format.print_string(string_of_int (!inferences)^"..");
         Format.print_flush())
       else ());
      try let gi =
            if incdepth then expand_goal rules g n 100000 (fun x -> x)
            else expand_goal rules g 100000 n (fun x -> x) in
          (if !meson_chatty && !verbose then
            (Format.print_string
              ("Goal solved with "^(string_of_int (!inferences))^
               " inferences.");
             Format.print_newline())
           else if !verbose then
            (Format.print_string("solved at "^string_of_int (!inferences));
             Format.print_newline())
           else ());
          gi
      with Failure _ -> solve (n + incsize) g in
    fun g -> solve min (g,[])

  (* ----------------------------------------------------------------------- *)
  (* Creation of tagged contrapositives from a HOL clause.                   *)
  (* This includes any possible support clauses (1 = falsity).               *)
  (* The rules are partitioned into association lists.                       *)
  (* ----------------------------------------------------------------------- *)

  let fol_of_hol_clauses =
    let eqt (a1,(b1,c1)) (a2, (b2,c2)) =
     ((a1 = a2) && (b1 = b2) && (equals_thm c1 c2)) in
    let rec mk_contraposes n th used unused sofar =
      match unused with
        [] -> sofar
      | h::t -> let nw = (map mk_negated (used @ t),h),(n,th) in
                mk_contraposes (n + 1) th (used@[h]) t (nw::sofar) in
    let fol_of_hol_clause th =
      let lconsts = freesl (hyp th) in
      let tm = concl th in
      let hlits = disjuncts tm in
      let flits = map (fol_of_literal [] lconsts) hlits in
      let basics = mk_contraposes 0 th [] flits [] in
      if forall (fun (p,_) -> p < 0) flits then
        ((map mk_negated flits,(1,[])),(-1,th))::basics
      else basics in
    fun thms ->
      let rawrules = itlist (union' eqt o fol_of_hol_clause) thms [] in
      let prs = setify (map (fst o snd o fst) rawrules) in
      let prules =
        map (fun t -> t,filter ((=) t o fst o snd o fst) rawrules) prs in
      let srules = sort (fun (p,_) (q,_) -> abs(p) <= abs(q)) prules in
      srules

  (* ----------------------------------------------------------------------- *)
  (* Optimize set of clauses; changing literal order complicates HOL stuff.  *)
  (* ----------------------------------------------------------------------- *)

  let optimize_rules =
    let optimize_clause_order cls =
      sort (fun ((l1,_),_) ((l2,_),_) -> length l1 <= length l2) cls in
    map (fun (a,b) -> a,optimize_clause_order b)

  (* ----------------------------------------------------------------------- *)
  (* Create a HOL contrapositive on demand, with a cache.                    *)
  (* ----------------------------------------------------------------------- *)

  let clear_contrapos_cache,make_hol_contrapos =
    let DISJ_AC = AC DISJ_ACI
    and imp_CONV = REWR_CONV(TAUT `a \/ b <=> ~b ==> a`)
    and push_CONV =
      GEN_REWRITE_CONV TOP_SWEEP_CONV
       [TAUT `~(a \/ b) <=> ~a /\ ~b`; TAUT `~(~a) <=> a`]
    and pull_CONV = GEN_REWRITE_CONV DEPTH_CONV
       [TAUT `~a \/ ~b <=> ~(a /\ b)`]
    and imf_CONV = REWR_CONV(TAUT `~p <=> p ==> F`) in
    let memory = ref [] in
    let clear_contrapos_cache() = memory := [] in
    let make_hol_contrapos (n,th) =
      let tm = concl th in
      let key = (n,tm) in
      try assoc key (!memory) with Failure _ ->
      if n < 0 then
        CONV_RULE (pull_CONV THENC imf_CONV) th
      else
        let djs = disjuncts tm in
        let acth =
          if n = 0 then th else
          let ldjs,rdjs = chop_list n djs in
          let ndjs = (hd rdjs)::(ldjs@(tl rdjs)) in
          EQ_MP (DISJ_AC(mk_eq(tm,list_mk_disj ndjs))) th in
        let fth =
          if length djs = 1 then acth
          else CONV_RULE (imp_CONV THENC push_CONV) acth in
        (memory := (key,fth)::(!memory); fth) in
    clear_contrapos_cache,make_hol_contrapos

  (* ---------------------------------------------------------------------- *)
  (* Handle trivial start/finish stuff.                                     *)
  (* ---------------------------------------------------------------------- *)

  let finish_RULE =
      GEN_REWRITE_RULE I
       [TAUT `(~p ==> p) <=> p`; TAUT `(p ==> ~p) <=> ~p`]

  (* ----------------------------------------------------------------------- *)
  (* Translate back the saved proof into HOL.                                *)
  (* ----------------------------------------------------------------------- *)

  let meson_to_hol =
    let hol_negate tm =
      try dest_neg tm with Failure _ -> mk_neg tm in
    let merge_inst (t,x) current =
      (fol_subst current t,x)::current in
    let rec meson_to_hol insts (Subgoal(g,gs,(n,th),offset,locin)) =
      let newins = itlist merge_inst locin insts in
      let g' = fol_inst newins g in
      let hol_g = hol_of_literal g' in
      let ths = map (meson_to_hol newins) gs in
      let hth =
        if equals_thm th TRUTH then ASSUME hol_g else
        let cth = make_hol_contrapos(n,th) in
        if ths = [] then cth else MATCH_MP cth (end_itlist CONJ ths) in
      let ith = PART_MATCH I hth hol_g in
      finish_RULE (DISCH (hol_negate(concl ith)) ith) in
    meson_to_hol

  (* ----------------------------------------------------------------------- *)
  (* Create equality axioms for all the function and predicate symbols in    *)
  (* a HOL term. Not very efficient (but then neither is throwing them into  *)
  (* automated proof search!)                                                *)
  (* ----------------------------------------------------------------------- *)

  let create_equality_axioms =
    let eq_thms = (CONJUNCTS o prove)
     (`(x:A = x) /\
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

  (* ----------------------------------------------------------------------- *)
  (* Brand's transformation.                                                 *)
  (* ----------------------------------------------------------------------- *)

  let perform_brand_modification =
    let rec subterms_irrefl lconsts tm acc =
      if is_var tm || is_const tm then acc else
      let fn,args = strip_comb tm in
      itlist (subterms_refl lconsts) args acc
    and subterms_refl lconsts tm acc =
      if is_var tm then if mem tm lconsts then insert tm acc else acc
      else if is_const tm then insert tm acc else
      let fn,args = strip_comb tm in
      itlist (subterms_refl lconsts) args (insert tm acc) in
    let CLAUSIFY = CONV_RULE(REWR_CONV(TAUT `a ==> b <=> ~a \/ b`)) in
    let rec BRAND tms th =
      if tms = [] then th else
      let tm = hd tms in
      let gv = genvar (type_of tm) in
      let eq = mk_eq(gv,tm) in
      let th' = CLAUSIFY (DISCH eq (SUBS [SYM (ASSUME eq)] th))
      and tms' = map (subst [gv,tm]) (tl tms) in
      BRAND  tms' th' in
    let BRAND_CONGS th =
      let lconsts = freesl (hyp th) in
      let lits = disjuncts (concl th) in
      let atoms = map (fun t -> try dest_neg t with Failure _ -> t) lits in
      let eqs,noneqs = partition
        (fun t -> try fst(dest_const(fst(strip_comb t))) = "="
                  with Failure _ -> false) atoms in
      let acc = itlist (subterms_irrefl lconsts) noneqs [] in
      let uts = itlist
        (itlist (subterms_irrefl lconsts) o snd o strip_comb) eqs acc in
      let sts = sort (fun s t -> not(free_in s t)) uts in
      BRAND sts th in
    let BRANDE th =
      let tm = concl th in
      let l,r = dest_eq tm in
      let gv = genvar(type_of l) in
      let eq = mk_eq(r,gv) in
      CLAUSIFY(DISCH eq (EQ_MP (AP_TERM (rator tm) (ASSUME eq)) th)) in
    let LDISJ_CASES th lth rth =
      DISJ_CASES th (DISJ1 lth (concl rth)) (DISJ2 (concl lth) rth) in
    let ASSOCIATE = CONV_RULE(REWR_CONV(GSYM DISJ_ASSOC)) in
    let rec BRAND_TRANS th =
      let tm = concl th in
      try let l,r = dest_disj tm in
          if is_eq l then
            let lth = ASSUME l in
            let lth1 = BRANDE lth
            and lth2 = BRANDE (SYM lth)
            and rth = BRAND_TRANS (ASSUME r) in
            map (ASSOCIATE o LDISJ_CASES th lth1) rth @
            map (ASSOCIATE o LDISJ_CASES th lth2) rth
          else
            let rth = BRAND_TRANS (ASSUME r) in
            map (LDISJ_CASES th (ASSUME l)) rth
      with Failure _ ->
          if is_eq tm then [BRANDE th; BRANDE (SYM th)]
          else [th] in
    let find_eqs =
      find_terms (fun t -> try fst(dest_const t) = "="
                           with Failure _ -> false) in
    let REFLEXATE ths =
      let eqs = itlist (union o find_eqs o concl) ths [] in
      let tys = map (hd o snd o dest_type o snd o dest_const) eqs in
      let gvs = map genvar tys in
      itlist (fun v acc -> (REFL v)::acc) gvs ths in
    fun ths ->
      if exists (can (find_term is_eq o concl)) ths then
        let ths' = map BRAND_CONGS ths in
        let ths'' = itlist (union' equals_thm o BRAND_TRANS) ths' [] in
        REFLEXATE ths''
      else ths

  (* ----------------------------------------------------------------------- *)
  (* Push duplicated copies of poly theorems to match existing assumptions.  *)
  (* ----------------------------------------------------------------------- *)

  let POLY_ASSUME_TAC =
    let rec uniq' eq =
      fun l ->
        match l with
          x::(y::_ as t) -> let t' = uniq' eq t in
                              if eq x y then t' else
                              if t'==t then l else x::t'
        | _ -> l in
    let setify' le eq s = uniq' eq (sort le s) in
    let rec grab_constants tm acc =
      if is_forall tm || is_exists tm then grab_constants (body(rand tm)) acc
      else if is_iff tm || is_imp tm || is_conj tm || is_disj tm then
        grab_constants (rand tm) (grab_constants (lhand tm) acc)
      else if is_neg tm then grab_constants (rand tm) acc
      else union (find_terms is_const tm) acc in
    let match_consts (tm1,tm2) =
      let s1,ty1 = dest_const tm1
      and s2,ty2 = dest_const tm2 in
      if s1 = s2 then type_match ty1 ty2 []
      else failwith "match_consts" in
    let polymorph mconsts th =
      let tvs = subtract (type_vars_in_term (concl th))
                         (unions (map type_vars_in_term (hyp th))) in
      if tvs = [] then [th] else
      let pconsts = grab_constants (concl th) [] in
      let tyins = mapfilter match_consts
        (allpairs (fun x y -> x,y) pconsts mconsts) in
      let ths' =
        setify' (fun th th' -> dest_thm th <= dest_thm th')
                equals_thm (mapfilter (C INST_TYPE th) tyins) in
      if ths' = [] then
        (warn true "No useful-looking instantiations of lemma"; [th])
      else ths' in
    let rec polymorph_all mconsts ths acc =
      if ths = [] then acc else
      let ths' = polymorph mconsts (hd ths) in
      let mconsts' = itlist grab_constants (map concl ths') mconsts in
      polymorph_all mconsts' (tl ths) (union' equals_thm ths' acc) in
    fun ths (asl,w as gl) ->
      let mconsts = itlist (grab_constants o concl o snd) asl [] in
      let ths' = polymorph_all mconsts ths [] in
      MAP_EVERY ASSUME_TAC ths' gl

  (* ----------------------------------------------------------------------- *)
  (* Basic HOL MESON procedure.                                              *)
  (* ----------------------------------------------------------------------- *)

  let SIMPLE_MESON_REFUTE min max inc ths =
    clear_contrapos_cache();
    inferences := 0;
    let old_dcutin = !meson_dcutin in
    if !meson_depth then meson_dcutin := 100001 else ();
    let ths' = if !meson_brand then perform_brand_modification ths
               else ths @ create_equality_axioms (map concl ths) in
    let rules = optimize_rules(fol_of_hol_clauses ths') in
    let proof,(insts,_,_) =
      solve_goal rules (!meson_depth) min max inc (1,[]) in
    meson_dcutin := old_dcutin;
    meson_to_hol insts proof

  let CONJUNCTS_THEN' ttac cth =
    ttac(CONJUNCT1 cth) THEN ttac(CONJUNCT2 cth)

  let PURE_MESON_TAC min max inc gl =
    reset_vars(); reset_consts();
    (FIRST_ASSUM CONTR_TAC ORELSE
     W(ACCEPT_TAC o SIMPLE_MESON_REFUTE min max inc o map snd o fst)) gl

  let QUANT_BOOL_CONV =
    PURE_REWRITE_CONV[FORALL_BOOL_THM; EXISTS_BOOL_THM; COND_CLAUSES;
                      NOT_CLAUSES; IMP_CLAUSES; AND_CLAUSES; OR_CLAUSES;
                      EQ_CLAUSES; FORALL_SIMP; EXISTS_SIMP]

  let rec SPLIT_TAC n g =
    ((FIRST_X_ASSUM(CONJUNCTS_THEN' ASSUME_TAC) THEN SPLIT_TAC n) ORELSE
     (if n > 0 then FIRST_X_ASSUM DISJ_CASES_TAC THEN SPLIT_TAC (n - 1)
      else NO_TAC) ORELSE
     ALL_TAC) g

end;;

(* ------------------------------------------------------------------------- *)
(* Basic MESON tactic with settable parameters.                              *)
(* ------------------------------------------------------------------------- *)

let GEN_MESON_TAC min max step ths =
  REFUTE_THEN ASSUME_TAC THEN
  Meson.POLY_ASSUME_TAC (map GEN_ALL ths) THEN
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
  ASM_FOL_TAC THEN
  Meson.SPLIT_TAC (!meson_split_limit) THEN
  RULE_ASSUM_TAC(CONV_RULE(PRENEX_CONV THENC WEAK_CNF_CONV)) THEN
  RULE_ASSUM_TAC(repeat
   (fun th -> SPEC(genvar(type_of(fst(dest_forall(concl th))))) th)) THEN
  REPEAT (FIRST_X_ASSUM (Meson.CONJUNCTS_THEN' ASSUME_TAC)) THEN
  RULE_ASSUM_TAC(CONV_RULE(ASSOC_CONV DISJ_ASSOC)) THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  Meson.PURE_MESON_TAC min max step;;

(* ------------------------------------------------------------------------- *)
(* Common cases.                                                             *)
(* ------------------------------------------------------------------------- *)

let ASM_MESON_TAC = GEN_MESON_TAC 0 50 1;;

let MESON_TAC ths = POP_ASSUM_LIST(K ALL_TAC) THEN ASM_MESON_TAC ths;;

(* ------------------------------------------------------------------------- *)
(* Also introduce a rule.                                                    *)
(* ------------------------------------------------------------------------- *)

let MESON ths tm =
  let th = TAC_PROOF(([],tm),MESON_TAC ths) in
  let asl,tm' = dest_thm th in
  if asl <> [] && not(subset asl (unions (map hyp ths)))
  then failwith "MESON: too many assumptions in result"
  else if tm' = tm then th else
  try EQ_MP (ALPHA tm' tm) th
  with Failure _ -> failwith "MESON: the wrong result";;
