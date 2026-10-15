(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*       Common forward symbolic-execution and state-update machinery.       *)
(* ========================================================================= *)

needs "common/interval.ml";;

(* Returns true if t is `read <component_name> <state>`. *)
let is_read_named_component component_name t =
  match t with
  | Comb (Comb (Const ("read", _), Const (name, _)), _) ->
      name = component_name
  | _ -> false;;

(* Construct the length theorem and offset-indexed decode theorem array for
   a byte-list machine-code definition. Backends supply any representation-
   specific length rewrites and their decoder traversal. *)
let GEN_MK_EXEC_RULE length_rewrites decodes_thm th0 =
  let th1 = AP_TERM `LENGTH:byte list->num` th0 in
  let th2 =
    (REWRITE_CONV length_rewrites THENC NUM_REDUCE_CONV)
      (rhs (concl th1)) in
  let execth1 = TRANS th1 th2 in
  let execth2_raw:(thm*term) list = decodes_thm th0 in
  let decode_arr:thm option array = Array.make
    (dest_small_numeral (snd (dest_eq (concl execth1)))) None in
  let _ = List.iter (fun decode_th,pcofs ->
    decode_arr.(dest_small_numeral pcofs) <- Some decode_th)
    execth2_raw in
  (execth1,decode_arr);;

(* The shared stepping interface has two levels.

   GEN_BASIC_STEP_TAC performs the semantic step only. It selects a decode
   theorem, asks step_conv for `step s s'`, unfolds eventually/eventually_n,
   introduces the successor state named by sname, and runs the backend's
   immediate post-step cleanup. It does not propagate the resulting state
   update through the surrounding proof context.

   GEN_STEP_TAC below is the proof-oriented wrapper normally exposed by a
   backend. It calls the basic tactic, normalizes the update, re-establishes
   loaded-code facts, pushes the update through assumptions and MAYCHANGE,
   and derives simplified component reads for the new state. *)
let GEN_BASIC_STEP_TAC backend_name step_tm state_ty step_conv post_step_tac =
  let one = `1:num` in
  fun (decode_ths:thm option array) sname
      (store_inst_term_to:term ref option) (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,state_ty) in
    let atm = mk_comb(mk_comb(step_tm,sv),sv') in
    let eth = step_conv decode_ths (map snd asl) atm in

    (match store_inst_term_to with
     | Some r -> r := rhs (concl eth)
     | None -> ());

    let progress_tac =
      let c,_ = strip_comb w in
      if name_of c = "eventually" then
        GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC
      else if name_of c = "eventually_n" then
        let stepn = dest_numeral(rand(rator(rator w))) in
        let stepn_decr = stepn -/ num 1 in
        let stepn_thm = GSYM (NUM_ADD_CONV
          (mk_binary "+" (one,mk_numeral(stepn_decr)))) in
        GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV)
          [stepn_thm] THEN
        GEN_REWRITE_TAC I [EVENTUALLY_N_STEP]
      else
        failwith
          (backend_name ^
           "_BASIC_STEP_TAC: neither eventually nor eventually_n") in

    (progress_tac THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINDER_CONV [eth] THEN
      (CONV_TAC EXISTS_NONTRIVIAL_CONV ORELSE
       (PRINT_GOAL_TAC THEN
        FAIL_TAC
          (backend_name ^
           "_BASIC_STEP_TAC: Equality between two states is ill-formed. " ^
           "Did you forget to assume an extra condition like pointer " ^
           "alignment?")));
      X_GEN_TAC sv' THEN
      GEN_REWRITE_TAC LAND_CONV [eth] THEN
      post_step_tac]) (asl,w);;

(* For example, schematically,

     ARM_BASIC_STEP_TAC decode_ths "s1" ...

   decodes one instruction and introduces s1. If the context also contains
   `aligned_bytes_loaded s pc code` and `read X1 s = x`, then

     ARM_STEP_TAC (mc_length_th,decode_ths) [] "s1" ...

   additionally preserves the loaded-code fact at s1 and, when X1 is
   unchanged, derives `read X1 s1 = x`. The length theorem is needed only by
   this full layer to establish loaded-code preservation.

   The normalization hook runs after decoding and before the common
   state-update machinery. subths describe subsidiary loaded-code blocks
   whose preservation should be propagated along with the main block. *)
let GEN_STEP_TAC basic_step_tac normalize_tac loaded_update log_update
    (mc_length_th,decode_ths) (subths:thm list) sname
    (store_inst_term_to:term ref option)
    (strip_component_tac:thm_tactic) =
  basic_step_tac decode_ths sname store_inst_term_to THEN
  normalize_tac THEN
  NONSELFMODIFYING_STATE_UPDATE_TAC
    (MATCH_MP loaded_update mc_length_th) THEN
  MAP_EVERY (TRY o NONSELFMODIFYING_STATE_UPDATE_TAC o
    MATCH_MP loaded_update o CONJUNCT1) subths THEN
  ASSUMPTION_STATE_UPDATE_TAC THEN
  MAYCHANGE_STATE_UPDATE_TAC THEN
  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    log_update th thl;
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    ASSEMBLER_SIMPLIFY_TAC THEN
    strip_component_tac th);;

let GEN_VERBOSE_STEP_TAC step_tac (exth1,exth2) sname g =
  Format.print_string("Stepping to state "^sname);
  Format.print_newline();
  step_tac (exth1,exth2) [] sname None (K STRIP_TAC) g;;

let GEN_VERBOSE_SUBSTEP_TAC step_tac (exth1,exth2) subths sname g =
  Format.print_string("Stepping to state "^sname);
  Format.print_newline();
  step_tac (exth1,exth2) subths sname None (K STRIP_TAC) g;;

let GEN_DISCARD_STATE_TAC state_ty s =
  DISCARD_ASSUMPTIONS_TAC (vfree_in (mk_var(s,state_ty)) o concl);;

let GEN_DISCARD_OLDSTATE_TAC state_ty print_log s =
  let v = mk_var(s,state_ty) in
  let rec unbound_statevars_of_read bound_svars tm =
    match tm with
    | Comb(Comb(Const("read",_),_),s) ->
        if mem s bound_svars then [] else [s]
    | Comb(a,b) ->
        union (unbound_statevars_of_read bound_svars a)
              (unbound_statevars_of_read bound_svars b)
    | Abs(v,t) -> unbound_statevars_of_read (v::bound_svars) t
    | _ -> [] in
  DISCARD_ASSUMPTIONS_TAC
   (fun thm ->
      let us = unbound_statevars_of_read [] (concl thm) in
      if us = [] || us = [v] then false
      else if not(mem v us) then true
      else if !print_log then
        (Printf.printf
          "Info: assumption `%s` is erased, but it might have contained \
useful information\n"
          (string_of_term (concl thm));
         true)
      else true);;

(* Simulate through a core ensures theorem while preserving the surrounding
   eventual-execution goal. Backends supply their code-loading update theorem
   and old-state cleanup tactic. *)
let GEN_BIGSTEP_TAC backend_name loaded_update discard_oldstate_tac =
  let lemma = prove
   (`P s /\ (!s':S. Q s' /\ C s s' ==> eventually step R s')
     ==> ensures step P Q C ==> eventually step R s`,
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [ensures] THEN
    DISCH_THEN(MP_TAC o SPEC `s:S`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `(!s:S. eventually step P s ==> eventually step Q s)
      ==> eventually step P s ==> eventually step Q s`) THEN
    GEN_REWRITE_TAC I [EVENTUALLY_IMP_EVENTUALLY] THEN
    ASM_REWRITE_TAC[]) in
  fun (execth1,_) sname (asl,w) ->
    if not (is_imp w) ||
       let the_lhs,the_rhs = dest_imp w in
       not (is_comb the_lhs &&
            name_of (fst (strip_comb the_lhs)) = "ensures" &&
            is_comb the_rhs &&
            name_of (fst (strip_comb the_rhs)) = "eventually")
    then
      Printf.printf
        "%s_BIGSTEP_TAC: `ensures ... ==> eventually ...` expected, \
but got `%s`.\n"
        backend_name (string_of_term w);
    let sv = mk_var(sname,type_of(rand(rand w))) in
    (GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
      (!simulation_precanon_thms) THEN
     MATCH_MP_TAC lemma THEN CONJ_TAC THENL
      [BETA_TAC THEN ASM_REWRITE_TAC[];
       BETA_TAC THEN X_GEN_TAC sv THEN
       REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
       REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
       NONSELFMODIFYING_STATE_UPDATE_TAC
        (MATCH_MP loaded_update execth1) THEN
       ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(K ALL_TAC) THEN
       discard_oldstate_tac sname])
    (asl,w);;

(* ABI promotion starts from a goal whose precondition names caller-provided
   values by equations such as `read X30 s = returnaddress`. The promotion
   tactics then traverse and reorder the outer universal quantifiers. If the
   right-hand variable of one of these equations is not an explicit outer
   quantifier, the tactic can specialize that input instead of proving the
   result for every caller value.

   For each backend-supplied left-hand pattern, check the first matching
   equality in the goal. A variable on its right must occur among the outer
   `forall` binders. Missing equalities and non-variable right-hand sides are
   accepted because a theorem may omit or already instantiate that input. *)
let GEN_CHECK_FORALLVARS_TAC lhs_pats =
  let find_and_check lhs_pat t quants =
    let read_eq =
      try Some (find_term
        (fun t -> is_eq t && can (term_match [] lhs_pat) (lhs t)) t)
      with Failure _ -> None in
    match read_eq with
    | Some read_eq ->
        let the_var = rhs read_eq in
        if is_var the_var && not (mem the_var quants) then
          failwith
            ("variable " ^ string_of_term the_var ^
             " (which is RHS of " ^ string_of_term lhs_pat ^
             ") does not appear at forall")
        else
          ALL_TAC
    | None -> ALL_TAC in
  W(fun (_,w) ->
    let quants = fst (strip_forall w) in
    MAP_EVERY
      (fun lhs_pat -> find_and_check lhs_pat w quants)
      lhs_pats);;

(* These lemmas contain no ABI facts. They only reorder explicit quantifiers,
   split an event trace into a stack-spill prefix and the core trace, or carry
   an implication across a change of inner quantified variables. Backend
   files retain their old theorem names as exact-statement corollaries. *)
let SUBROUTINE_SWAP_FORALL3 = MESON[]
 `(forall (x:A) (y:B) (z:C). P x y z) <=>
  (forall y x z. P x y z)`;;

let SUBROUTINE_APPEND_FORALL = MESON[APPEND_EXISTS]
 `(forall (e:(A)list). P e) <=>
  (forall e_stack_spill e. P (APPEND e_stack_spill e))`;;

let SUBROUTINE_MONO_FORALL2 = MESON[]
 `(!(x:A). (!(y:B). P x y) ==> (!(z:C). Q x z))
  ==> (!x y. P x y) ==> (!x z. Q x z)`;;

let SUBROUTINE_MONO_FORALL3 = MESON[]
 `(!(x:A). (!(y:B) (y':C). P x y y') ==> (!(z:D) (z':E). Q x z z'))
  ==> (!x y y'. P x y y') ==> (!x z z'. Q x z z')`;;

let SUBROUTINE_APPEND_PREFIX_NIL = prove
 (`!e:(A)list. !e2.
    e = APPEND e2 e <=> APPEND [] e = APPEND e2 e`,
  MESON_TAC[APPEND]);;

(* The full step tactic leaves facts about earlier states in the context.
   SINGLE_STEP is the usual linear-execution interface: after constructing
   the successor state, it removes facts which mention only obsolete states
   and simplifies the remaining context. Use the verbose step directly when
   a proof still needs to relate the successor to an earlier state. *)
let GEN_SINGLE_STEP_TAC verbose_step_tac discard_oldstate_tac th s =
  time (verbose_step_tac th s) THEN
  discard_oldstate_tac s THEN
  CLARIFY_TAC;;

(* Arithmetic accumulation collects useful equations after selected steps,
   usually carry or borrow equations from multi-instruction arithmetic. For
   example,

     ARM_VACCSTEPS_TAC th [2;4] [1;2;3;4]

   executes states s1 through s4 and runs accumulation after s2 and s4. If no
   suitable arithmetic pattern is found, the step still succeeds.

   VACCSTEP keeps facts about earlier states. XACCSTEP discards obsolete-state
   facts and omits the listed components from accumulation. ACCSTEP also
   discards obsolete-state facts, but runs a caller-supplied preprocessing
   tactic before accumulation. *)
let GEN_VACCSTEP_TAC verbose_step_tac th aflag s =
  verbose_step_tac th s THEN
  (if aflag then TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
   else ALL_TAC);;

let GEN_XACCSTEP_TAC single_step_tac th excs aflag s =
  single_step_tac th s THEN
  (if aflag then TRY(ACCUMULATEX_ARITH_TAC excs s THEN CLARIFY_TAC)
   else ALL_TAC);;

let GEN_ACCSTEP_TAC single_step_tac acc_preproc th aflag s =
  single_step_tac th s THEN
  (if aflag then
     acc_preproc THEN TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
   else ALL_TAC);;

(* The plural forms apply their corresponding one-step tactic to state names
   s<n>. For accumulating variants, [anums] identifies the state numbers at
   which arithmetic accumulation should run; [snums] is the complete sequence
   of steps to execute. *)
let GEN_VSTEPS_TAC verbose_step_tac th snums =
  MAP_EVERY (verbose_step_tac th) (statenames "s" snums);;

let GEN_STEPS_TAC single_step_tac th snums =
  MAP_EVERY (single_step_tac th) (statenames "s" snums);;

let GEN_VACCSTEPS_TAC vaccstep_tac th anums snums =
  MAP_EVERY
    (fun n -> vaccstep_tac th (mem n anums) ("s"^string_of_int n))
    snums;;

let GEN_XACCSTEPS_TAC xaccstep_tac th excs anums snums =
  MAP_EVERY
    (fun n -> xaccstep_tac th excs (mem n anums) ("s"^string_of_int n))
    snums;;

let GEN_ACCSTEPS_TAC accstep_tac acc_preproc th anums snums =
  MAP_EVERY
    (fun n ->
      let state_name = "s"^string_of_int n in
      accstep_tac (acc_preproc state_name) th (mem n anums) state_name)
    snums;;
