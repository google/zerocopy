(* ========================================================================= *)
(* Binary decision diagrams with complement edges, as a HOL derived rule.    *)
(*                                                                           *)
(* The style of implementation follows Brace, Rudell and Bryant's paper      *)
(* "Efficient implementation of a BDD package" (DAC 1990). It's based on the *)
(* hol90 implementation in "Binary Decision Diagrams as a HOL Derived Rule", *)
(* but greatly simplified since HOL Light handles pointer-eq subterms more   *)
(* efficiently and so we can avoid introducing any additional variables.     *)
(* ========================================================================= *)

let tfst (a,b,c) = a;;
let tsnd (a,b,c) = b;;

(* ------------------------------------------------------------------------- *)
(* Handling of variable tables.                                              *)
(* ------------------------------------------------------------------------- *)

let var_of_num varray n = Array.get varray n;;

let num_of_var (varray,vnext,vhash) v =
  try Hashtbl.find vhash v
  with Not_Found ->
      let n = !vnext in
      (vnext := n + 1; Array.set varray n v; Hashtbl.add vhash v n; n);;

let mk_vtable n =
  (Array.make (n+1) `T`,
   ref 1,
   (Hashtbl.create (n+1) :(term,int)Hashtbl.t));;

(* ------------------------------------------------------------------------- *)
(* Handling of unique table.                                                 *)
(* ------------------------------------------------------------------------- *)

let BDD_1 = max_int;;
let BDD_0 = -BDD_1;;

let btm_of_int =
  let true_tm = `T` in
  let rec btm_of_int uarray n =
     if n < 0 then mk_neg(btm_of_int uarray (-n)) else
     if n = BDD_1 then true_tm else
     rand(rator(concl(snd(apply (!uarray) n)))) in
  btm_of_int;;

let lookup_triple varray (uarray,unext,uhash) ((v,y,n) as tr) =
  try apply (!uhash) tr with Not_Found ->
  let ytm = btm_of_int uarray y
  and ntm = btm_of_int uarray n
  and vtm = Array.get varray v
  and m = !unext in
  let ltm = mk_cond(vtm,ytm,ntm) in
  let dth = REFL ltm in
  (unext := m + 1;
   uarray := (m |-> (tr,dth)) (!uarray);
   uhash := (tr |-> m) (!uhash);
   m);;

let bdd_expand uarray b =
  if b < 0 then
    let (v,l,r) = fst(apply (!uarray) (-b)) in
    (v,-l,-r)
  else fst(apply (!uarray) b);;

let BDD_EXPAND =
  let pth1 = TAUT
    `~(if v then b1 else b2) <=> (if v then ~b1 else ~b2)`
  and pth2 = TAUT
    `~(if v then b1 else ~b2) <=> (if v then ~b1 else b2)`
  and pth3 = TAUT
    `~(if v then ~b1 else b2) <=> (if v then b1 else ~b2)`
  and pth4 = TAUT
    `~(if v then ~b1 else ~b2) <=> (if v then b1 else b2)`
  and neg_tm = `~`
  and v_tm = `v:bool`
  and b1_tm = `b1:bool`
  and b2_tm = `b2:bool` in
  let rec BDD_EXPAND uarray b =
    if b < 0 then
      let def = snd(apply (!uarray) (-b)) in
      let (v,(y,n)) = dest_cond(rand(concl def)) in
      let pth =
        if is_neg y then
          if is_neg n then INST [v,v_tm; rand y,b1_tm; rand n,b2_tm] pth4
          else INST [v,v_tm; rand y,b1_tm; n,b2_tm] pth3
        else
          if is_neg n then INST [v,v_tm; y,b1_tm; rand n,b2_tm] pth2
          else INST [v,v_tm; y,b1_tm; n,b2_tm] pth1 in
      TRANS (AP_TERM neg_tm def) pth
    else snd(apply (!uarray) b) in
  BDD_EXPAND;;

let BDD_LOOKUP =
  let pth1 = TAUT `b <=> (if v then b else b)`
  and pth2 = TAUT
    `(b <=> (if v then l else r))
     ==> (~b <=> (if v then ~l else ~r))`
  and pth3 = TAUT
    `(b <=> (if v then l else ~r))
     ==> (~b <=> (if v then ~l else r))`
  and b_tm = `b:bool`
  and v_tm = `v:bool`
  and l_tm = `l:bool`
  and r_tm = `r:bool` in
  let rec BDD_LOOKUP varray utable (v,l,r) =
    if l = r then
      (INST [var_of_num varray v,v_tm;btm_of_int (tfst utable) l,b_tm] pth1,
       l,0)
    else if l < 0 then
      let i = lookup_triple varray utable (v,-l,-r) in
      let dth = snd(apply(!(tfst utable)) i) in
      let (ctm,(vtm,(ltm,rtm))) = (I F_F dest_cond) (dest_eq(concl dth)) in
      if r < 0 then
        (MP (INST [ctm,b_tm;vtm,v_tm;ltm,l_tm;rtm,r_tm] pth2) dth,-i,i)
      else
        (MP (INST [ctm,b_tm;vtm,v_tm;ltm,l_tm;rand rtm,r_tm] pth3) dth,-i,i)
    else let i = lookup_triple varray utable (v,l,r) in
         let dth = snd(apply (!(tfst utable)) i) in
         (dth,i,i) in
  BDD_LOOKUP;;

let mk_utable() =
  (ref(0 |=> ((0,0,0),TRUTH)),
   ref 1,
   ref undefined);;

(* ------------------------------------------------------------------------- *)
(* Handling of computed table.                                               *)
(* ------------------------------------------------------------------------- *)

let bdd_and =
  let pth1 = TAUT `~T /\ r1 <=> ~T`
  and pth2 = TAUT `l1 /\ T <=> l1`
  and pth3 = TAUT `l1 /\ l1 <=> l1`
  and pth4 = TAUT `~r1 /\ r1 <=> ~T`
  and pth5 = TAUT
    `(b1 <=> (if v then l1 else r1))
     ==> (b2 <=> (if v then l2 else r2))
         ==> (b3 <=> (if v then l3 else r3))
             ==> (l1 /\ l2 <=> l3) ==> (r1 /\ r2 <=> r3) ==> (b1 /\ b2 <=> b3)`
  and pth6 = TAUT
   `(b1 <=> (if v then l1 else r1))
    ==> (b3 <=> (if v then l3 else r3))
        ==> (l1 /\ b2 <=> l3) ==> (r1 /\ b2 <=> r3) ==> (b1 /\ b2 <=> b3)`
  and pth7 = TAUT
    `(b2 <=> (if v then l2 else r2))
     ==> (b3 <=> (if v then l3 else r3))
         ==> (b1 /\ l2 <=> l3) ==> (b1 /\ r2 <=> r3) ==> (b1 /\ b2 <=> b3)`
  and pth8 = TAUT `l1 /\ r1 <=> r1 /\ l1`
  and b1_tm = `b1:bool`
  and b2_tm = `b2:bool`
  and b3_tm = `b3:bool`
  and l1_tm = `l1:bool`
  and l2_tm = `l2:bool`
  and l3_tm = `l3:bool`
  and r1_tm = `r1:bool`
  and r2_tm = `r2:bool`
  and r3_tm = `r3:bool`
  and v_tm = `v:bool`
  and lookup_pair (carray,cnext,chash) (l,r) =
     try let i = apply (!chash) (l,r) in (fst(apply (!carray) i),i)
     with Not_Found -> failwith "lookup_pair" in
  let rec bdd_and (varray,utable,((carray,cnext,chash) as ctable)) (l,r) =
    try lookup_pair ctable (l,r) with Failure _ ->
    let (ans,thm,uargs,cargs) =
      if l = BDD_0 then
       (BDD_0,INST [btm_of_int (tfst utable) r,r1_tm] pth1,[],[])
      else if r = BDD_1 then
       (l,INST [btm_of_int (tfst utable) l,l1_tm] pth2,[],[])
      else if l = r then
       (l,INST [btm_of_int (tfst utable) l,l1_tm] pth3,[],[])
      else if l = -r then
       (BDD_0,INST [btm_of_int (tfst utable) r,r1_tm] pth4,[],[])
      else
        let (lv,ly,ln) = bdd_expand (tfst utable) l
        and (rv,ry,rn) = bdd_expand (tfst utable) r in
        if lv = rv then
          let (thy,cy,jy) = bdd_ands (varray,utable,ctable) (ly,ry) in
          let (thn,cn,jn) = bdd_ands (varray,utable,ctable) (ln,rn) in
          let thl = BDD_EXPAND (tfst utable) l in
          let thr = BDD_EXPAND (tfst utable) r in
          let (thc,c,jc) = BDD_LOOKUP varray utable (lv,cy,cn) in
          let (b1,(v1,(l1,r1))) = (I F_F dest_cond) (dest_eq(concl thl)) in
          let (b2,(v2,(l2,r2))) = (I F_F dest_cond) (dest_eq(concl thr)) in
          let (b3,(v3,(l3,r3))) = (I F_F dest_cond) (dest_eq(concl thc)) in
          let ith = INST [(b1,b1_tm);(b2,b2_tm);(b3,b3_tm);
                          (l1,l1_tm);(l2,l2_tm);(l3,l3_tm);
                          (r1,r1_tm);(r2,r2_tm);(r3,r3_tm);(v3,v_tm)] pth5 in
          let lis = [thl; thr; thc; thy; thn] in
          let xth = rev_itlist (C MP) lis ith in
          (c,xth,[abs(l);abs(r);jc],[jy;jn])
        else if lv > rv then
          let (thy,cy,jy) = bdd_ands (varray,utable,ctable) (ly,r) in
          let (thn,cn,jn) = bdd_ands (varray,utable,ctable) (ln,r) in
          let thl = BDD_EXPAND (tfst utable) l in
          let (thc,c,jc) = BDD_LOOKUP varray utable (lv,cy,cn) in
          let (b1,(v1,(l1,r1))) = (I F_F dest_cond) (dest_eq(concl thl)) in
          let (b3,(v3,(l3,r3))) = (I F_F dest_cond) (dest_eq(concl thc)) in
          let b2 = rand(rand(rator(concl thy))) in
          let ith = INST [(b1,b1_tm);(b2,b2_tm);(b3,b3_tm);
                          (l1,l1_tm);(l3,l3_tm);
                          (r1,r1_tm);(r3,r3_tm);(v3,v_tm)] pth6 in
          let lis = [thl; thc; thy; thn] in
          let xth = rev_itlist (C MP) lis ith in
          (c,xth,[abs(l);jc],[jy;jn])
        else
          let (thy,cy,jy) = bdd_ands (varray,utable,ctable) (l,ry) in
          let (thn,cn,jn) = bdd_ands (varray,utable,ctable) (l,rn) in
          let thr = BDD_EXPAND (tfst utable) r in
          let (thc,c,jc) = BDD_LOOKUP varray utable (rv,cy,cn) in
          let (b2,(v2,(l2,r2))) = (I F_F dest_cond) (dest_eq(concl thr)) in
          let (b3,(v3,(l3,r3))) = (I F_F dest_cond) (dest_eq(concl thc)) in
          let b1 = rand(rator(rand(rator(concl thy)))) in
          let ith = INST [(b1,b1_tm);(b2,b2_tm);(b3,b3_tm);
                          (l2,l2_tm);(l3,l3_tm);
                          (r2,r2_tm);(r3,r3_tm);(v3,v_tm)] pth7 in
          let lis = [thr; thc; thy; thn] in
          let xth = rev_itlist (C MP) lis ith in
          (c,xth,[abs(r);jc],[jy;jn]) in
    let m = !cnext in
    (cnext := m + 1;
     carray := (m |-> (ans,(thm,uargs,cargs))) (!carray);
     chash := ((l,r) |-> m) (!chash);
     (ans,m))

  and bdd_ands (varray,utable,ctable) (l,r) =
    if (l:int) <= r then
      let (ans,i) = bdd_and (varray,utable,ctable) (l,r) in
      let th = tfst(snd(apply (!(tfst ctable)) i)) in
      (th,ans,i)
    else
      let (ans,i) = bdd_and (varray,utable,ctable) (r,l) in
      let th = tfst(snd(apply (!(tfst ctable)) i)) in
      let ((ltm,rtm),ctm) = (dest_conj F_F I) (dest_eq(concl th)) in
      let eth = INST [rtm,l1_tm; ltm,r1_tm] pth8 in
      (TRANS eth th,ans,i) in
  bdd_and;;

let mk_ctable() =
  (ref undefined,
   ref 0,
   ref undefined);;

(* ------------------------------------------------------------------------- *)
(* Basic BDD-constructing operations for the logical connectives.            *)
(* ------------------------------------------------------------------------- *)

let BDD_TRUE = (BDD_1,REFL `T`);;

let BDD_FALSE = (BDD_0,TAUT `F <=> ~T`);;

let BDD_VAR =
  let pth = TAUT `(x <=> (if v then T else ~T)) ==> v = x`
  and x_tm = `x:bool`
  and v_tm = `v:bool` in
  fun (vtable,utable,ctable) tm ->
    let v = num_of_var vtable tm in
    let u = lookup_triple (tfst vtable) utable (v,BDD_1,BDD_0) in
    let ltm = btm_of_int (tfst utable) u in
    let sth = INST [ltm,x_tm; tm,v_tm] pth in
    let th = snd(apply (!(tfst utable)) u) in
    (u,MP sth th);;

let BDD_NEG =
  let neg_tm = `~`
  and x_tm = `x:bool`
  and pth = TAUT `~ ~ x <=> x` in
  fun (vtable,utable,ctable) (i,fth) ->
    if i < 0 then
      let utm = btm_of_int (tfst utable) (-i) in
      let th = INST [utm,x_tm] pth in
      (-i,TRANS (AP_TERM neg_tm fth) th)
    else
      (-i,AP_TERM neg_tm fth);;

let BDD_AND =
  let and_tm = `/\`
  and t1_tm = `t1:bool`
  and t2_tm = `t2:bool` in
  let pth = SPECL [t1_tm; t2_tm] CONJ_SYM in
  fun (vtable,utable,ctable) ((i1,th1),(i2,th2)) ->
    if i2 < i1 then
      let (i3,j) = bdd_and (tfst vtable,utable,ctable) (i2,i1) in
      let sth = INST [btm_of_int (tfst utable) i1,t1_tm;
                      btm_of_int (tfst utable) i2,t2_tm] pth
      and th = tfst(snd(apply (!(tfst ctable)) j)) in
      (i3,TRANS (MK_COMB(AP_TERM and_tm th1,th2))
                (TRANS sth th))
    else
      let (i3,j) = bdd_and (tfst vtable,utable,ctable) (i1,i2) in
      let th = tfst(snd(apply (!(tfst ctable)) j)) in
      (i3,TRANS (MK_COMB(AP_TERM and_tm th1,th2)) th);;

let BDD_OR =
  let pth = TAUT `~(~a /\ ~b) <=> a \/ b` in
  let rew = REWR_CONV pth in
  let rewl = LAND_CONV rew in
  let rule = CONV_RULE rewl in
  fun tt (b1,b2) ->
    let (i,fth) = BDD_NEG tt (BDD_AND tt (BDD_NEG tt b1,BDD_NEG tt b2)) in
    (i,rule fth);;

let BDD_IMP =
  let pth = TAUT `~(a /\ ~b) <=> a ==> b` in
  let rew = REWR_CONV pth in
  let rewl = LAND_CONV rew in
  let rule = CONV_RULE rewl in
  fun tt (b1,b2) ->
    let (i,fth) = BDD_NEG tt (BDD_AND tt (b1,BDD_NEG tt b2)) in
    (i,rule fth);;

let BDD_IFF =
  let pth = TAUT `~(a /\ ~b) /\ ~(~a /\ b) <=> (a <=> b)` in
  let rew = REWR_CONV pth in
  let rewl = LAND_CONV rew in
  let rule = CONV_RULE rewl in
  fun tt (b1,b2) ->
    let (i,fth) = BDD_AND tt (BDD_NEG tt (BDD_AND tt (b1,BDD_NEG tt b2)),
                            BDD_NEG tt (BDD_AND tt (BDD_NEG tt b1,b2))) in
    (i,rule fth);;

let rec BDD_OF_TERM defs tt tm =
  match tm with
    Const("T",_) -> BDD_TRUE
  | Const("F",_) -> BDD_FALSE
  | Comb(Comb(Const("/\\",_),l),r) ->
        BDD_AND tt (BDD_OF_TERM defs tt l,BDD_OF_TERM defs tt r)
  | Comb(Comb(Const("\\/",_),l),r) ->
        BDD_OR tt (BDD_OF_TERM defs tt l,BDD_OF_TERM defs tt r)
  | Comb(Comb(Const("==>",_),l),r) ->
        BDD_IMP tt (BDD_OF_TERM defs tt l,BDD_OF_TERM defs tt r)
  | Comb(Comb(Const("=",Tyapp("fun",[Tyapp("bool",[]);_])),l),r) ->
        BDD_IFF tt (BDD_OF_TERM defs tt l,BDD_OF_TERM defs tt r)
  | Comb(Const("~",_),l) ->
        BDD_NEG tt (BDD_OF_TERM defs tt (rand tm))
  | _ -> (try apply defs tm with Failure _ -> BDD_VAR tt tm);;

(* ------------------------------------------------------------------------- *)
(* Existential quantification of BDDs.                                       *)
(* ------------------------------------------------------------------------- *)

let BDD_EXISTS =
  let [rule_e;rule_d;rule_t;rule_f] =
    map (fun t -> GEN_REWRITE_RULE RAND_CONV [MESON[] t])
      [`(?p. if p then q else r) <=> q \/ r`;
       `(?p. if x then q p else r p) <=> (if x then (?p. q p) else (?p. r p))`;
       `(?p:bool. T) <=> T`;
       `(?p:bool. ~T) <=> ~T`] in
  fun (vtable,utable,ctable) x ->
    let etable = ref undefined in
    let xn = num_of_var vtable x in
    let rec BDD_EXISTS (n,th) =
      try apply (!etable) n with Failure _ ->
      let res =
        if n = BDD_0 then
          (BDD_0,rule_f (MK_EXISTS x th))
        else if n = BDD_1 then
          (BDD_1,rule_t (MK_EXISTS x th))
        else
          let v,nt,nf = bdd_expand (tfst utable) n
          and eth = TRANS th (BDD_EXPAND (tfst utable) n) in
          let _,(ntm,nfm) = dest_cond(rand(concl eth)) in
          if v = xn then
            let onum,oth = BDD_OR (vtable,utable,ctable)
                                  ((nt,REFL ntm),(nf,REFL nfm)) in
            onum,TRANS (rule_e (MK_EXISTS x eth)) oth
          else
            let lnum,lth = BDD_EXISTS (nt,REFL ntm)
            and rnum,rth = BDD_EXISTS (nf,REFL nfm) in
            let wth =
              TRANS (rule_d (MK_EXISTS x eth))
                 (MK_COMB(AP_TERM (rator(rator(rand(concl eth)))) lth,rth)) in
            let fth,wn,_ =  BDD_LOOKUP (tfst vtable) utable (v,lnum,rnum) in
            wn,TRANS wth (SYM fth) in
      etable := (n |-> res) (!etable); res in
      BDD_EXISTS;;

(* ------------------------------------------------------------------------- *)
(* Provide some information on output when verbose = 1                       *)
(* ------------------------------------------------------------------------- *)

let bdd_stats nd (vt,ct,ut) =
  let d = if nd = 0 then "" else string_of_int nd^" definitions, " in
  remark
   ("BDD with "^d^
    string_of_int(!(tsnd vt)) ^ " variables, " ^
    string_of_int(!(tsnd ut)) ^ " nodes and " ^
    string_of_int(!(tsnd ct)) ^ " cached results");;

(* ------------------------------------------------------------------------- *)
(* Basic tautology prover                                                    *)
(* ------------------------------------------------------------------------- *)

let BDD_TAUT tm =
  let vt = mk_vtable(length(atoms tm))
  and ut = mk_utable() and ct = mk_ctable() in
  let b = BDD_OF_TERM undefined (vt,ut,ct) tm in
  let _ = bdd_stats 0 (vt,ct,ut) in
  EQT_ELIM (snd b);;

(* ------------------------------------------------------------------------- *)
(* A version that treats an input p ==> q specially, considering p           *)
(* as a list of "definitions" (required to be left-to-right acyclic)         *)
(* ------------------------------------------------------------------------- *)

let BDD_DEFTAUT =
  let bdd_def th =
    let rule = TRANS th in
    fun (i,fth) -> (i,rule fth) in
  let rec bdd_of_defs defs tt ths =
    match ths with
      [] -> defs
    | th::oths ->
          let lv,rt = dest_eq(concl th) in
          let br = BDD_OF_TERM defs tt rt in
          let bl = bdd_def th br in
          bdd_of_defs ((lv |-> bl) defs) tt oths in
  let is_atomic tm =
    not(is_neg tm || is_conj tm || is_disj tm || is_imp tm || is_iff tm) in
  let is_literal tm =
    (is_neg tm && is_atomic(rand tm)) || is_atomic tm in
  let valid_definition tm =
    (is_iff tm && is_literal(lhand tm)) || is_literal tm in
  let ADJUST_DEF th =
    let tm = concl th in
    if is_neg tm then EQF_INTRO th
    else if is_iff tm then th
    else EQT_INTRO th in
  let rec acyclic oks tms =
    match tms with
      [] -> true
    | tm::otms -> not (exists (free_in (lhs tm)) (rand tm::oks)) &&
                  acyclic (tm::oks) otms in
  let valid_definitions tm =
    let tms = map (concl o ADJUST_DEF o ASSUME) (conjuncts tm) in
    forall valid_definition tms && acyclic [] tms in
  fun ivars tm ->
    let vars = ivars @ subtract (atoms tm) ivars in
    let vt = mk_vtable (length vars)
    and ut = mk_utable() and ct = mk_ctable() in
    let _ = do_list (ignore o BDD_VAR (vt,ut,ct)) ivars in
    if is_imp tm && valid_definitions (lhand tm) then
      let ths = map ADJUST_DEF (CONJUNCTS(ASSUME(lhand tm))) in
      let defs = bdd_of_defs undefined (vt,ut,ct) ths in
      let b = BDD_OF_TERM defs (vt,ut,ct) (rand tm) in
      let _ = bdd_stats (length(dom defs)) (vt,ct,ut) in
      DISCH (lhand tm) (EQT_ELIM(snd b))
    else
      let b = BDD_OF_TERM undefined (vt,ut,ct) tm in
      let _ = bdd_stats 0 (vt,ct,ut) in
      EQT_ELIM(snd b);;
