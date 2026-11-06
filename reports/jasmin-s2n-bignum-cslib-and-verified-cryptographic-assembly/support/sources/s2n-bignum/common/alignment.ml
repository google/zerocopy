(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ------------------------------------------------------------------------- *)
(* Additional proof support for "aligned w" subgoals (w = 16, 32 etc.).      *)
(* ------------------------------------------------------------------------- *)

(* Legacy ARM/x86 normalization. Remove a concrete addend or subtrahend only
   when it is a multiple of the requested alignment. Keep this conversion
   deliberately narrow because existing tactics depend on its exact output. *)
let NORMALIZE_ALIGNED_WORD_CONV =
  let pth = prove
   (`(!n (x:A word).
      w divides n ==> (aligned w (word_add x (word n)) <=> aligned w x)) /\
     (!n (x:A word).
      w divides n ==> (aligned w (word_add (word n) x) <=> aligned w x)) /\
     (!n (x:A word).
      w divides n ==> (aligned w (word_sub x (word n)) <=> aligned w x)) /\
     (!n (x:A word).
      w divides n ==> (aligned w (word_sub (word n) x) <=> aligned w x))`,
    MESON_TAC[ALIGNED_WORD_ADD_EQ; ALIGNED_WORD_SUB_EQ; ALIGNED_WORD;
             aligned]) in
  let funs = map (PART_MATCH (lhs o rand)) (CONJUNCTS pth) in
  let conv tm =
    try let th = tryfind (fun f -> f tm) funs in
        MP th (EQT_ELIM(DIVIDES_CONV(lhand(concl th))))
    with Failure _ -> failwith "" in
  fun tm ->
    match tm with
      Comb(Comb(Const("aligned",_),w),x) when is_numeral w -> REPEATC conv tm
     | _ -> failwith "NORMALIZE_ALIGNED_WORD_CONV";;

(* Opt-in normalization for generic backends. Rewrite symbolic `word (pc + n)`
   terms as word additions, distribute alignment through a conditional address,
   normalize each branch, and collapse equal results. For example,

     aligned 4
       (if b then word(pc + 4):int32 else word(pc + 8))

   is reduced to `aligned 4 (word pc:int32)`: both offsets preserve four-byte
   alignment, independently of the branch and of 32-bit wraparound. *)
let NORMALIZE_ALIGNED_WORD_EXTENDED_CONV =
  let rec normalize tm =
    (RAND_CONV
       (GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_ADD]) THENC
     NORMALIZE_ALIGNED_WORD_CONV THENC
     TRY_CONV
      (REWR_CONV COND_RAND THENC
       RATOR_CONV (RAND_CONV normalize) THENC
       RAND_CONV normalize THENC
       REWRITE_CONV[COND_ID])) tm in
  fun tm ->
    match tm with
      Comb(Comb(Const("aligned",_),w),_) when is_numeral w -> normalize tm
     | _ -> failwith "NORMALIZE_ALIGNED_WORD_EXTENDED_CONV";;

(* An `n`-aligned address is also `m`-aligned whenever `m` divides `n`.
   The extended tactics use this to consume a stronger alignment assumption;
   the legacy ARM/x86 tactics below do not add this inference. *)
let ALIGNED_WORD_WEAKEN = prove
 (`!m n (x:N word).
      m divides n ==> aligned n x ==> aligned m x`,
  REWRITE_TAC[aligned] THEN MESON_TAC[DIVIDES_TRANS]);;

let ALIGNED_WORD_WEAKEN_CONV ths =
  let conv tm =
    let f,args = strip_comb tm in
    if not (is_const f && name_of f = "aligned" &&
            List.length args = 2) then
      failwith "ALIGNED_WORD_WEAKEN_CONV"
    else
      let m,x = hd args,last args in
      tryfind
       (fun th ->
          let f',args' = strip_comb (concl th) in
          if not (is_const f' && name_of f' = "aligned" &&
                  List.length args' = 2 && aconv x (last args')) then
            failwith "ALIGNED_WORD_WEAKEN_CONV"
          else
            let n = hd args' in
            let dth =
              EQT_ELIM
               (DIVIDES_CONV (mk_binary "num_divides" (m,n))) in
            EQT_INTRO
             (MATCH_MP
               (MATCH_MP
                 (ISPECL [m;n;x] ALIGNED_WORD_WEAKEN) dth) th))
       ths in
  conv;;

let rec SUB_ALIGNED_WORD_CONV conv tm =
  match tm with
  | Comb(Comb(Const("aligned",_),w),_) when is_numeral w -> RAND_CONV conv tm
  | Comb(l,r) -> COMB_CONV (SUB_ALIGNED_WORD_CONV conv) tm
  | Abs(x,bod) -> ABS_CONV (SUB_ALIGNED_WORD_CONV conv) tm
  | _ -> REFL tm;;

(* Legacy tactic and conversion retained with their previous behavior. *)
let (ALIGNED_WORD_TAC:tactic) =
  let basetac =
    CONV_TAC
     (SUB_ALIGNED_WORD_CONV(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV)) THEN
    ASM (GEN_REWRITE_TAC
      (LAND_CONV o SUB_ALIGNED_WORD_CONV o TOP_DEPTH_CONV)) [] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV) THEN
    ASSUM_LIST(fun thl ->
      REWRITE_TAC(mapfilter (CONV_RULE NORMALIZE_ALIGNED_WORD_CONV) thl))
  and trigger = can (find_term (fun tm ->
    let f,args = strip_comb tm in
    is_const f && name_of f = "aligned" && List.length args = 2)) in
  fun (asl,w) -> if trigger w then basetac (asl,w) else ALL_TAC (asl,w);;

let ALIGNED_WORD_CONV ths =
  let baseconv =
    SUB_ALIGNED_WORD_CONV(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THENC
    GEN_REWRITE_CONV (SUB_ALIGNED_WORD_CONV o TOP_DEPTH_CONV) ths THENC
    ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_CONV THENC
    REWRITE_CONV(mapfilter (CONV_RULE NORMALIZE_ALIGNED_WORD_CONV) ths)
  and trigger = can (find_term (fun tm ->
    let f,args = strip_comb tm in
    is_const f && name_of f = "aligned" && List.length args = 2)) in
  fun tm -> if trigger tm then baseconv tm else REFL tm;;

(* Opt-in variants for goals that contain conditional or symbolic addresses,
   or need a weaker alignment than the one available in the assumptions. The
   tactic:
   - simplifies component reads through state writes inside aligned addresses;
   - rewrites addresses using the assumptions;
   - normalizes concrete offsets and conditional branches; and
   - derives `aligned m x` from `aligned n x` when `m divides n`.

   Thus, from `aligned 16 (word pc:int32)`, it can close

     aligned 4
       (if b then word(pc + 4):int32 else word(pc + 8))

   Use ALIGNED_WORD_EXTENDED_TAC when proving a goal from the current
   assumptions. ALIGNED_WORD_EXTENDED_CONV provides the same normalization
   to a conversion caller that supplies the relevant theorems explicitly. *)
let (ALIGNED_WORD_EXTENDED_TAC:tactic) =
  let basetac =
    CONV_TAC
     (SUB_ALIGNED_WORD_CONV(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV)) THEN
    ASM (GEN_REWRITE_TAC
      (LAND_CONV o SUB_ALIGNED_WORD_CONV o TOP_DEPTH_CONV)) [] THEN
    CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_EXTENDED_CONV) THEN
    ASSUM_LIST(fun thl ->
      let nthl =
        mapfilter
          (CONV_RULE NORMALIZE_ALIGNED_WORD_EXTENDED_CONV) thl in
      REWRITE_TAC nthl THEN
      CONV_TAC(TOP_DEPTH_CONV (ALIGNED_WORD_WEAKEN_CONV nthl)))
  and trigger = can (find_term (fun tm ->
    let f,args = strip_comb tm in
    is_const f && name_of f = "aligned" && List.length args = 2)) in
  fun (asl,w) -> if trigger w then basetac (asl,w) else ALL_TAC (asl,w);;

let ALIGNED_WORD_EXTENDED_CONV ths =
  let nths =
    mapfilter
      (CONV_RULE NORMALIZE_ALIGNED_WORD_EXTENDED_CONV) ths in
  let baseconv =
    SUB_ALIGNED_WORD_CONV(TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV) THENC
    GEN_REWRITE_CONV (SUB_ALIGNED_WORD_CONV o TOP_DEPTH_CONV) ths THENC
    ONCE_DEPTH_CONV NORMALIZE_ALIGNED_WORD_EXTENDED_CONV THENC
    REWRITE_CONV nths THENC
    TOP_DEPTH_CONV (ALIGNED_WORD_WEAKEN_CONV nths)
  and trigger = can (find_term (fun tm ->
    let f,args = strip_comb tm in
    is_const f && name_of f = "aligned" && List.length args = 2)) in
  fun tm -> if trigger tm then baseconv tm else REFL tm;;
