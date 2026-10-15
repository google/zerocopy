(* ========================================================================= *)
(* Basic equality reasoning including conversionals.                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "printer.ml";;

(* ------------------------------------------------------------------------- *)
(* Type abbreviation for conversions.                                        *)
(* ------------------------------------------------------------------------- *)

type conv = term->thm;;

(* ------------------------------------------------------------------------- *)
(* A bit more syntax.                                                        *)
(* ------------------------------------------------------------------------- *)

let lhand = rand o rator;;

let lhs = fst o dest_eq;;

let rhs = snd o dest_eq;;

(* ------------------------------------------------------------------------- *)
(* Similar to variant, but even avoids constants, and ignores types.         *)
(* ------------------------------------------------------------------------- *)

let mk_primed_var =
  let rec svariant avoid s =
    if mem s avoid || (can get_const_type s && not(is_hidden s)) then
      svariant avoid (s^"'")
    else s in
  fun avoid v ->
    let s,ty = dest_var v in
    let s' = svariant (mapfilter (fst o dest_var) avoid) s in
    mk_var(s',ty);;

(* ------------------------------------------------------------------------- *)
(* General case of beta-conversion.                                          *)
(* ------------------------------------------------------------------------- *)

let BETA_CONV tm =
  try BETA tm with Failure _ ->
  try let f,arg = dest_comb tm in
      let v = bndvar f in
      INST [arg,v] (BETA (mk_comb(f,v)))
  with Failure _ -> failwith "BETA_CONV: Not a beta-redex";;

(* ------------------------------------------------------------------------- *)
(* A few very basic derived equality rules.                                  *)
(* ------------------------------------------------------------------------- *)

let AP_TERM tm =
  let rth = REFL tm in
  fun th -> try MK_COMB(rth,th)
            with Failure _ -> failwith "AP_TERM";;

let AP_THM th tm =
  try MK_COMB(th,REFL tm)
  with Failure _ -> failwith "AP_THM";;

let SYM th =
  let tm = concl th in
  let l,r = dest_eq tm in
  let lth = REFL l in
  EQ_MP (MK_COMB(AP_TERM (rator (rator tm)) th,lth)) lth;;

let ALPHA tm1 tm2 =
  try TRANS (REFL tm1) (REFL tm2)
  with Failure _ -> failwith "ALPHA";;

let ALPHA_CONV v tm =
  let res = alpha v tm in
  ALPHA tm res;;

let GEN_ALPHA_CONV v tm =
  if is_abs tm then ALPHA_CONV v tm else
  let b,abs = dest_comb tm in
  AP_TERM b (ALPHA_CONV v abs);;

let MK_BINOP op =
  let afn = AP_TERM op in
  fun (lth,rth) -> MK_COMB(afn lth,rth);;

(* ------------------------------------------------------------------------- *)
(* Terminal conversion combinators.                                          *)
(* ------------------------------------------------------------------------- *)

let (NO_CONV:conv) = fun tm -> failwith "NO_CONV";;

let (ALL_CONV:conv) = REFL;;

(* ------------------------------------------------------------------------- *)
(* Combinators for sequencing, trying, repeating etc. conversions.           *)
(* ------------------------------------------------------------------------- *)

let ((THENC):conv -> conv -> conv) =
  fun conv1 conv2 t ->
    let th1 = conv1 t in
    let th2 = conv2 (rand(concl th1)) in
    TRANS th1 th2;;

let ((ORELSEC):conv -> conv -> conv) =
  fun conv1 conv2 t ->
    try conv1 t with Failure _ -> conv2 t;;

let (FIRST_CONV:conv list -> conv) = end_itlist (fun c1 c2 -> c1 ORELSEC c2);;

let (EVERY_CONV:conv list -> conv) =
  fun l -> itlist (fun c1 c2 -> c1 THENC c2) l ALL_CONV;;

let REPEATC =
  let rec REPEATC conv t =
    ((conv THENC (REPEATC conv)) ORELSEC ALL_CONV) t in
  (REPEATC:conv->conv);;

let (CHANGED_CONV:conv->conv) =
  fun conv tm ->
    let th = conv tm in
    let l,r = dest_eq (concl th) in
    if aconv l r then failwith "CHANGED_CONV" else th;;

let TRY_CONV conv = conv ORELSEC ALL_CONV;;

(* ------------------------------------------------------------------------- *)
(* Subterm conversions.                                                      *)
(* ------------------------------------------------------------------------- *)

let (RATOR_CONV:conv->conv) =
  fun conv tm ->
    match tm with
      Comb(l,r) -> AP_THM (conv l) r
    | _ -> failwith "RATOR_CONV: Not a combination";;

let (RAND_CONV:conv->conv) =
  fun conv tm ->
   match tm with
     Comb(l,r) -> MK_COMB(REFL l,conv r)
   |  _ -> failwith "RAND_CONV: Not a combination";;

let LAND_CONV = RATOR_CONV o RAND_CONV;;

let (COMB2_CONV: conv->conv->conv) =
  fun lconv rconv tm ->
   match tm with
     Comb(l,r) -> MK_COMB(lconv l,rconv r)
  | _ -> failwith "COMB2_CONV: Not a combination";;

let COMB_CONV = W COMB2_CONV;;

let (ABS_CONV:conv->conv) =
  fun conv tm ->
    let v,bod = dest_abs tm in
    let th = conv bod in
    try ABS v th with Failure _ ->
    let gv = genvar(type_of v) in
    let gbod = vsubst[gv,v] bod in
    let gth = ABS gv (conv gbod) in
    let gtm = concl gth in
    let l,r = dest_eq gtm in
    let v' = variant (frees gtm) v in
    let l' = alpha v' l and r' = alpha v' r in
    EQ_MP (ALPHA gtm (mk_eq(l',r'))) gth;;

let BINDER_CONV conv tm =
  if is_abs tm then ABS_CONV conv tm
  else RAND_CONV(ABS_CONV conv) tm;;

let SUB_CONV conv tm =
  match tm with
    Comb(_,_) -> COMB_CONV conv tm
  | Abs(_,_) -> ABS_CONV conv tm
  | _ -> REFL tm;;

let (BINOP_CONV:conv->conv) =
  fun conv tm ->
    let lop,r = dest_comb tm in
    let op,l = dest_comb lop in
    MK_COMB(AP_TERM op (conv l),conv r);;

let (BINOP2_CONV:conv->conv->conv) =
  fun conv1 conv2 tm ->
    let lop,r = dest_comb tm in
    let op,l = dest_comb lop in
    MK_COMB(AP_TERM op (conv1 l),conv2 r);;

(* ------------------------------------------------------------------------- *)
(* Depth conversions; internal use of a failure-propagating `Boultonized'    *)
(* version to avoid a great deal of reuilding of terms.                      *)
(* ------------------------------------------------------------------------- *)

let (ONCE_DEPTH_CONV: conv->conv),
    (DEPTH_CONV: conv->conv),
    (REDEPTH_CONV: conv->conv),
    (TOP_DEPTH_CONV: conv->conv),
    (TOP_SWEEP_CONV: conv->conv) =
  let THENQC conv1 conv2 tm =
    try let th1 = conv1 tm in
        try let th2 = conv2(rand(concl th1)) in TRANS th1 th2
        with Failure _ -> th1
    with Failure _ -> conv2 tm
  and THENCQC conv1 conv2 tm =
    let th1 = conv1 tm in
    try let th2 = conv2(rand(concl th1)) in TRANS th1 th2
    with Failure _ -> th1
  and COMB_QCONV conv tm =
    match tm with
      Comb(l,r) ->
        (try let th1 = conv l in
             try let th2 = conv r in MK_COMB(th1,th2)
             with Failure _ -> AP_THM th1 r
         with Failure _ -> AP_TERM l (conv r))
    | _ -> failwith "COMB_QCONV: Not a combination" in
  let rec REPEATQC conv tm = THENCQC conv (REPEATQC conv) tm in
  let SUB_QCONV conv tm =
    match tm with
      Abs(_,_) -> ABS_CONV conv tm
    | _ -> COMB_QCONV conv tm in
  let rec ONCE_DEPTH_QCONV conv tm =
      (conv ORELSEC (SUB_QCONV (ONCE_DEPTH_QCONV conv))) tm
  and DEPTH_QCONV conv tm =
    THENQC (SUB_QCONV (DEPTH_QCONV conv))
           (REPEATQC conv) tm
  and REDEPTH_QCONV conv tm =
    THENQC (SUB_QCONV (REDEPTH_QCONV conv))
           (THENCQC conv (REDEPTH_QCONV conv)) tm
  and TOP_DEPTH_QCONV conv tm =
    THENQC (REPEATQC conv)
           (THENCQC (SUB_QCONV (TOP_DEPTH_QCONV conv))
                    (THENCQC conv (TOP_DEPTH_QCONV conv))) tm
  and TOP_SWEEP_QCONV conv tm =
    THENQC (REPEATQC conv)
           (SUB_QCONV (TOP_SWEEP_QCONV conv)) tm in
  (fun c -> TRY_CONV (ONCE_DEPTH_QCONV c)),
  (fun c -> TRY_CONV (DEPTH_QCONV c)),
  (fun c -> TRY_CONV (REDEPTH_QCONV c)),
  (fun c -> TRY_CONV (TOP_DEPTH_QCONV c)),
  (fun c -> TRY_CONV (TOP_SWEEP_QCONV c));;

(* ------------------------------------------------------------------------- *)
(* Apply at leaves of op-tree; NB any failures at leaves cause failure.      *)
(* ------------------------------------------------------------------------- *)

let rec DEPTH_BINOP_CONV op conv tm =
  match tm with
    Comb(Comb(op',l),r) when compare op' op = 0 ->
      let l,r = dest_binop op tm in
      let lth = DEPTH_BINOP_CONV op conv l
      and rth = DEPTH_BINOP_CONV op conv r in
      MK_COMB(AP_TERM op' lth,rth)
  | _ -> conv tm;;

(* ------------------------------------------------------------------------- *)
(* Follow a path.                                                            *)
(* ------------------------------------------------------------------------- *)

let PATH_CONV =
  let rec path_conv s cnv =
    match s with
      [] -> cnv
    | "l"::t -> RATOR_CONV (path_conv t cnv)
    | "r"::t -> RAND_CONV (path_conv t cnv)
    | _::t -> ABS_CONV (path_conv t cnv) in
  fun s cnv -> path_conv (explode s) cnv;;

(* ------------------------------------------------------------------------- *)
(* Follow a pattern                                                          *)
(* ------------------------------------------------------------------------- *)

let PAT_CONV =
  let rec PCONV xs pat conv =
    if mem pat xs then conv
    else if not(exists (fun x -> free_in x pat) xs) then ALL_CONV
    else if is_comb pat then
      COMB2_CONV (PCONV xs (rator pat) conv) (PCONV xs (rand pat) conv)
    else
      ABS_CONV (PCONV xs (body pat) conv) in
  fun pat -> let xs,pbod = strip_abs pat in PCONV xs pbod;;

(* ------------------------------------------------------------------------- *)
(* Symmetry conversion.                                                      *)
(* ------------------------------------------------------------------------- *)

let SYM_CONV tm =
  try let th1 = SYM(ASSUME tm) in
      let tm' = concl th1 in
      let th2 = SYM(ASSUME tm') in
      DEDUCT_ANTISYM_RULE th2 th1
  with Failure _ -> failwith "SYM_CONV";;

(* ------------------------------------------------------------------------- *)
(* Conversion to a rule.                                                     *)
(* ------------------------------------------------------------------------- *)

let CONV_RULE (conv:conv) th =
  EQ_MP (conv(concl th)) th;;

(* ------------------------------------------------------------------------- *)
(* Substitution conversion.                                                  *)
(* ------------------------------------------------------------------------- *)

let SUBS_CONV ths tm =
  try if ths = [] then REFL tm else
      let lefts = map (lhand o concl) ths in
      let gvs = map (genvar o type_of) lefts in
      let pat = subst (zip gvs lefts) tm in
      let abs = list_mk_abs(gvs,pat) in
      let th = rev_itlist
        (fun y x -> CONV_RULE (RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV)
                              (MK_COMB(x,y))) ths (REFL abs) in
      if rand(concl th) = tm then REFL tm else th
  with Failure _ -> failwith "SUBS_CONV";;

(* ------------------------------------------------------------------------- *)
(* Get a few rules.                                                          *)
(* ------------------------------------------------------------------------- *)

let BETA_RULE = CONV_RULE(REDEPTH_CONV BETA_CONV);;

let GSYM = CONV_RULE(ONCE_DEPTH_CONV SYM_CONV);;

let SUBS ths = CONV_RULE (SUBS_CONV ths);;

(* ------------------------------------------------------------------------- *)
(* A cacher for conversions.                                                 *)
(* ------------------------------------------------------------------------- *)

let CACHE_CONV =
  let ALPHA_HACK th =
    let tm' = lhand(concl th) in
    fun tm -> if tm' = tm then th else TRANS (ALPHA tm tm') th in
  fun conv ->
    let net = ref empty_net in
    fun tm -> try tryfind (fun f -> f tm) (lookup tm (!net))
              with Failure _ ->
                  let th = conv tm in
                  (net := enter [] (tm,ALPHA_HACK th) (!net); th);;

(* ------------------------------------------------------------------------- *)
(* A printer.                                                                *)
(* ------------------------------------------------------------------------- *)

let PRINT_TERM_CONV t = Format.printf "%a\n" pp_print_qterm t; ALL_CONV t;;
