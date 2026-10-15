(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Definitions for the constant-time property and memory-safety property.    *)
(* ========================================================================= *)

needs "common/overlap.ml";;

(*** We define that an instruction raises an observable microarchitectural
 *** event if its cycles/power consumption/anything that can be observed by
 *** a side-channel attacker can vary depending on the inputs of
 *** the instruction. For example, instructions taking a constant number of
 *** cycles like ADD do not raise an observable event, whereas cond branch does.
 *** Its kinds (EventLoad/Store/...) describe the events distinguishable from
 *** each other by the attacker, and their parameters describe the values
 *** that are inputs and/or outputs of the instructions that will affect the
 *** observed cycles/etc.
 *** An opcode of instruction is not a parameter of the event, even if the
 *** number of taken cycles may depend on opcode. This relies on an assumption
 *** that a program is public information.
 *** One instruction can raise multiple events (e.g., one that reads PC from
 *** the memory and jumps to the address, even though this case will not exist
 *** in Arm).
 *** The formal semantics of instruction must emit a fixed list of events.
 *** It is not allowed for an instruction to raise one event when its input
 *** data is X and and two events when its input data is Y.
 *** Note: for x86, even if PUSH and POP instructions do memory access at RSP
 *** which is public information (stack address is public), these instructions
 *** must still explicitly raise EventLoad and EventStore because otherwise
 *** memory safety check will miss out-of-bounds stack access.
 ***)
let address_uarch_event_INDUCT, address_uarch_event_RECURSION = define_type
  "address_uarch_event =
    // (address, byte length)
    EventLoad (A word#num)
    // (address, byte length)
    | EventStore (A word#num)
    // (src pc, destination pc)
    | EventJump (A word#A word)

    // Instructions in X86 that are not in the DOIT list
    // (Data Operand Independent Timing Instructions)

    // PEXT (src1, src2, bitwidth)
    | EventX86PEXT (int64#int64#num)
    // POPCNT (src, bitwidth)
    | EventX86POPCNT (int64#num)
  ";;

(* Before this type was parameterized, every event constructor produced a
   uarch_event with 64-bit addresses. Preserve that source behavior for
   unconstrained quotations. An address-typed operand or explicit result type
   still selects the generic constructor at another width.

   For example, the annotation on
     `[EventLoad(word 0,4)]:((32)address_uarch_event)list`
   selects the 32-bit constructor. The unannotated quotation
     `[EventLoad(word 0,4)]`
   retains the historical 64-bit constructor.

   TODO: Remove this 64-bit preference once existing proof code gives quoted
   event lists an explicit address type. *)
make_overloadable "EventLoad"
 `:A word#num->(A)address_uarch_event`;;
overload_interface
 ("EventLoad",`EventLoad:A word#num->(A)address_uarch_event`);;
overload_interface
 ("EventLoad",`EventLoad:int64#num->(64)address_uarch_event`);;

make_overloadable "EventStore"
 `:A word#num->(A)address_uarch_event`;;
overload_interface
 ("EventStore",`EventStore:A word#num->(A)address_uarch_event`);;
overload_interface
 ("EventStore",`EventStore:int64#num->(64)address_uarch_event`);;

make_overloadable "EventJump"
 `:A word#A word->(A)address_uarch_event`;;
overload_interface
 ("EventJump",`EventJump:A word#A word->(A)address_uarch_event`);;
overload_interface
 ("EventJump",`EventJump:int64#int64->(64)address_uarch_event`);;

make_overloadable "EventX86PEXT"
 `:int64#int64#num->(A)address_uarch_event`;;
overload_interface
 ("EventX86PEXT",`EventX86PEXT:int64#int64#num->(A)address_uarch_event`);;
overload_interface
 ("EventX86PEXT",`EventX86PEXT:int64#int64#num->(64)address_uarch_event`);;

make_overloadable "EventX86POPCNT"
 `:int64#num->(A)address_uarch_event`;;
overload_interface
 ("EventX86POPCNT",`EventX86POPCNT:int64#num->(A)address_uarch_event`);;
overload_interface
 ("EventX86POPCNT",`EventX86POPCNT:int64#num->(64)address_uarch_event`);;

let uarch_event_INDUCT =
  address_uarch_event_INDUCT
and uarch_event_RECURSION =
  address_uarch_event_RECURSION;;

(* Preserve the existing public event type for AArch64 and x86-64 while
   allowing another backend to instantiate events at its native address
   width.

   TODO: Give the 64-bit compatibility type a width-suffixed public name,
   such as uarch_event64, and migrate the existing 64-bit backends. Keep the
   unsuffixed name for now only to avoid source churn in ARM and x86 proofs. *)
new_type_abbrev("uarch_event",`:(64)address_uarch_event`);;

(* Keep this layer independent of common/misc.ml; a backend may load safety
   before the wider tactic library. *)
let SAFETY_EX_SUBSET_LIST = prove
 (`!l:A list P l2.
      EX P l /\ ALL (\x. MEM x l2) l ==> EX P l2`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[EX;ALL] THEN ASM_MESON_TAC[EX_MEM]);;

let SAFETY_EX_CONTAINED_WORD_RANGES = prove
 (`!base sz (l:(A word#num)list) l2.
      EX (\r. contained_modulo (2 EXP dimindex(:A))
              (base,sz) (val (FST r),SND r)) l /\
      ALL (\r. EX (\r'. contained r r') l2) l
      ==> EX (\r. contained_modulo (2 EXP dimindex(:A))
              (base,sz) (val (FST r),SND r)) l2`,
  REWRITE_TAC
   [GSYM EX_MEM;GSYM ALL_MEM;EXISTS_PAIR_THM;FORALL_PAIR_THM;contained] THEN
  MESON_TAC[CONTAINED_MODULO_TRANS]);;

let SAFETY_APPEND_EXISTS = prove
 (`!x:A list. ?x1 x2. x = APPEND x1 x2`,
  GEN_TAC THEN EXISTS_TAC `[]:A list` THEN MESON_TAC[APPEND]);;

(* ------------------------------------------------------------------------- *)
(* In-bound-ness of memory access                                            *)
(* ------------------------------------------------------------------------- *)

let memaccess_inbounds_def = new_definition `
  memaccess_inbounds (e2:((A)address_uarch_event)list)
                  (readable_ranges:(A word#num)list)
                  (writable_ranges:(A word#num)list) <=>
    ALL (\(e:(A)address_uarch_event). match e with
      | EventLoad (adr,sz) ->
        EX (\range. contained_modulo
            (2 EXP dimindex(:A))
            (val adr, sz) (val (FST range), SND range))
           readable_ranges
      | EventStore (adr,sz) ->
        EX (\range. contained_modulo
            (2 EXP dimindex(:A))
            (val adr, sz) (val (FST range), SND range))
           writable_ranges
      | _ -> true) e2`;;

(* Preserve the literal 64-bit modulus produced by the historical unfolding.
   Existing ARM and x86 arithmetic tactics depend on this syntactic form.
   The second conjunct remains the generic rewrite for native-width users. *)
let MEMACCESS_INBOUNDS_64 = prove
 (`memaccess_inbounds (e2:uarch_event list)
                     (readable_ranges:(int64#num)list)
                     (writable_ranges:(int64#num)list) <=>
    ALL (\(e:uarch_event). match e with
      | EventLoad (adr,sz) ->
        EX (\range. contained_modulo
            (2 EXP 64)
            (val adr, sz) (val (FST range), SND range))
           readable_ranges
      | EventStore (adr,sz) ->
        EX (\range. contained_modulo
            (2 EXP 64)
            (val adr, sz) (val (FST range), SND range))
           writable_ranges
      | _ -> true) e2`,
  REWRITE_TAC[memaccess_inbounds_def; DIMINDEX_64]);;

let memaccess_inbounds =
  MEMACCESS_INBOUNDS_64;;

let MEMACCESS_INBOUNDS_APPEND = prove(
  `forall e1 e2 rr wr. memaccess_inbounds (APPEND e1 e2) rr wr
    <=> memaccess_inbounds e1 rr wr /\ memaccess_inbounds e2 rr wr`,
  REWRITE_TAC[memaccess_inbounds_def;ALL_APPEND]);;

let MEMACCESS_INBOUNDS_CONS = prove(
  `forall h t rr wr. memaccess_inbounds (CONS h t) rr wr
    <=> memaccess_inbounds [h] rr wr /\ memaccess_inbounds t rr wr`,
  REWRITE_TAC[memaccess_inbounds_def;ALL]);;

let MEMACCESS_INBOUNDS_ALL = prove(
  `forall e rr wr.
    memaccess_inbounds e rr wr <=>
    ALL (\h. memaccess_inbounds [h] rr wr) e`,
  REWRITE_TAC[memaccess_inbounds_def;ALL]);;

let MEMACCESS_INBOUNDS_EVENT_MEM = prove(
  `forall rr rr' wr wr' (e:(A)address_uarch_event).
    ALL (\r. MEM r rr') rr /\ ALL (\w. MEM w wr') wr
    ==> memaccess_inbounds [e] rr wr
    ==> memaccess_inbounds [e] rr' wr'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SPEC_TAC
   (`(e:(A)address_uarch_event)`,`(e:(A)address_uarch_event)`) THEN
  MATCH_MP_TAC address_uarch_event_INDUCT THEN
  REWRITE_TAC[memaccess_inbounds_def;ALL] THEN CONJ_TAC THENL [
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC SAFETY_EX_SUBSET_LIST THEN
    EXISTS_TAC `rr:(A word#num)list` THEN ASM_REWRITE_TAC[];

    REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC SAFETY_EX_SUBSET_LIST THEN
    EXISTS_TAC `wr:(A word#num)list` THEN ASM_REWRITE_TAC[];
  ]);;

let MEMACCESS_INBOUNDS_MEM = prove(
  `forall (e:((A)address_uarch_event)list)
          (rr:(A word#num)list) rr' wr wr'.
    ALL (\r. MEM r rr') rr /\ ALL (\w. MEM w wr') wr
    ==> memaccess_inbounds e rr wr
    ==> memaccess_inbounds e rr' wr'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(snd(EQ_IMP_RULE(ISPECL
    [`e:((A)address_uarch_event)list`;
     `rr':(A word#num)list`; `wr':(A word#num)list`]
    MEMACCESS_INBOUNDS_ALL))) THEN
  MATCH_MP_TAC(ISPECL
    [`\(h:(A)address_uarch_event). memaccess_inbounds [h] rr wr`;
     `\(h:(A)address_uarch_event). memaccess_inbounds [h] rr' wr'`;
     `e:((A)address_uarch_event)list`]
    ALL_IMP) THEN
  BETA_TAC THEN CONJ_TAC THENL [
    X_GEN_TAC `h:(A)address_uarch_event` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
      [`rr:(A word#num)list`; `rr':(A word#num)list`;
       `wr:(A word#num)list`; `wr':(A word#num)list`;
       `h:(A)address_uarch_event`]
      MEMACCESS_INBOUNDS_EVENT_MEM) THEN
    ASM_REWRITE_TAC[];

    MATCH_MP_TAC(fst(EQ_IMP_RULE(ISPECL
      [`e:((A)address_uarch_event)list`;
       `rr:(A word#num)list`; `wr:(A word#num)list`]
      MEMACCESS_INBOUNDS_ALL))) THEN
    ASM_REWRITE_TAC[];
  ]);;

let MEMACCESS_INBOUNDS_EVENT_CONTAINED = prove(
  `forall rr rr' wr wr' (e:(A)address_uarch_event).
    ALL (\r. EX (\r'. contained r r') rr') rr /\
    ALL (\w. EX (\w'. contained w w') wr') wr
    ==> memaccess_inbounds [e] rr wr
    ==> memaccess_inbounds [e] rr' wr'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SPEC_TAC
   (`(e:(A)address_uarch_event)`,`(e:(A)address_uarch_event)`) THEN
  MATCH_MP_TAC address_uarch_event_INDUCT THEN
  REWRITE_TAC[memaccess_inbounds_def;ALL] THEN CONJ_TAC THENL [
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC SAFETY_EX_CONTAINED_WORD_RANGES THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th))) THEN
    ASM_REWRITE_TAC[];

    REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC SAFETY_EX_CONTAINED_WORD_RANGES THEN
    FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th))) THEN
    ASM_REWRITE_TAC[];
  ]);;

let MEMACCESS_INBOUNDS_CONTAINED = prove(
  `forall (e:((A)address_uarch_event)list)
          (rr:(A word#num)list) rr' wr wr'.
    ALL (\r. EX (\r'. contained r r') rr') rr /\
    ALL (\w. EX (\w'. contained w w') wr') wr
    ==> memaccess_inbounds e rr wr
    ==> memaccess_inbounds e rr' wr'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(snd(EQ_IMP_RULE(ISPECL
    [`e:((A)address_uarch_event)list`;
     `rr':(A word#num)list`; `wr':(A word#num)list`]
    MEMACCESS_INBOUNDS_ALL))) THEN
  MATCH_MP_TAC(ISPECL
    [`\(h:(A)address_uarch_event). memaccess_inbounds [h] rr wr`;
     `\(h:(A)address_uarch_event). memaccess_inbounds [h] rr' wr'`;
     `e:((A)address_uarch_event)list`]
    ALL_IMP) THEN
  BETA_TAC THEN CONJ_TAC THENL [
    X_GEN_TAC `h:(A)address_uarch_event` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
      [`rr:(A word#num)list`; `rr':(A word#num)list`;
       `wr:(A word#num)list`; `wr':(A word#num)list`;
       `h:(A)address_uarch_event`]
      MEMACCESS_INBOUNDS_EVENT_CONTAINED) THEN
    ASM_REWRITE_TAC[];

    MATCH_MP_TAC(fst(EQ_IMP_RULE(ISPECL
      [`e:((A)address_uarch_event)list`;
       `rr:(A word#num)list`; `wr:(A word#num)list`]
      MEMACCESS_INBOUNDS_ALL))) THEN
    ASM_REWRITE_TAC[];
  ]);;

(* ------------------------------------------------------------------------- *)
(* Helper tactics for subroutines                                            *)
(* ------------------------------------------------------------------------- *)

let safety_print_log = ref false;;

(* Do ASSUME_TAC for safety proof which is `exists f_events. ...` after
  stripping the exists f_events part. *)
let ASSUME_CALLEE_SAFETY_TAC =
  let fresh_f_events_var_counter = ref 0 in
  fun (callee_safety_proof:thm) (asmname:string) ->
    let f_events_var_type = type_of (fst (dest_exists (concl callee_safety_proof))) in
    let f_events_callee =
      let _ = fresh_f_events_var_counter := 1 + !fresh_f_events_var_counter in
      mk_var("f_events_callee" ^ (string_of_int !fresh_f_events_var_counter),
              f_events_var_type) in
    (X_CHOOSE_THEN f_events_callee (LABEL_TAC asmname)) callee_safety_proof;;

(* Extension of ASSUME_CALLEE_SAFETY_TAC: given safety_th which is
  |- exists f_events. forall e x y ... . P e,
  split e into e_tail and e, and push e_tail into the innermost place.
  |- exists f_events. forall e x y ... e_tail. P (APPEND e_tail e)
*)
let ASSUME_CALLEE_SAFETY_TAILED_TAC =
  let append_lemma = MESON[SAFETY_APPEND_EXISTS]
    `(forall (e:((A)address_uarch_event)list). P e) <=>
      (forall e_tail e. P (APPEND e_tail e))` in
  fun (safety_th:thm) (name:string) ->
    let safety_th' = ONCE_REWRITE_RULE[append_lemma] safety_th in
    (* push e_tail to the innermost location *)
    let exarg,body = dest_exists (concl safety_th') in
    let args,body = strip_forall body in
    let args_rotated = (tl args) @ [hd args] in
    let eqth = MESON[](mk_eq(
        concl safety_th',
        mk_exists(exarg,list_mk_forall(args_rotated,body))))
      in
    let safety_th'' = ONCE_REWRITE_RULE[eqth] safety_th' in
    ASSUME_CALLEE_SAFETY_TAC safety_th'' name;;
