(* ========================================================================= *)
(* General theory of state components (lenses).                              *)
(*                                                                           *)
(* This gives a hierarchical way of describing state using ":>" to compose,  *)
(* analogous to record components. The components are essentially just pairs *)
(* of reader and writer function, wrapped in a special type only for brevity *)
(* when stating component types explicitly. This idea is often called a      *)
(* "lens", (e.g. https://medium.com/javascript-scene/lenses-b85976cb0534).   *)
(*                                                                           *)
(* Ported from s2n-bignum (common/components.ml).                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Storing useful per-case theorems not true of a general component.         *)
(* ------------------------------------------------------------------------- *)

let component_read_write_thms = ref ([]:thm list);;

let add_component_read_write_thms l =
  component_read_write_thms := union l (!component_read_write_thms);;

let component_alias_thms = ref ([]:thm list);;

let valid_component_thms = ref ([]:thm list);;

let add_valid_component_thms l =
  valid_component_thms := union l (!valid_component_thms);;

let strongly_valid_component_thms = ref ([]:thm list);;

let add_strongly_valid_component_thms l =
  strongly_valid_component_thms :=
  union l (!strongly_valid_component_thms);;

let weakly_valid_component_thms = ref ([]:thm list);;

let add_weakly_valid_component_thms l =
  weakly_valid_component_thms :=
  union l (!weakly_valid_component_thms);;

let extensionally_valid_component_thms = ref ([]:thm list);;

let add_extensionally_valid_component_thms l =
  extensionally_valid_component_thms :=
  union l (!extensionally_valid_component_thms);;

let component_orthogonality_thms = ref ([]:thm list);;

let add_component_orthogonality_thms l =
  component_orthogonality_thms := union l (!component_orthogonality_thms);;

(* ------------------------------------------------------------------------- *)
(* Set up a type ":(S,V)component" for a component of type ":V" in a        *)
(* larger state space ":S", which is really just a reader function S->V      *)
(* and a writer function V->S->S updating the corresponding field.           *)
(* ------------------------------------------------------------------------- *)

let component_tybij =
  let th = prove(`?rw:(S->V)#(V->S->S). T`,REWRITE_TAC[]) in
  REWRITE_RULE[]
   (new_type_definition "component" ("component","dest_component") th);;

let COMPONENT_INJ = prove
 (`!rw rw'. component rw = component rw' <=> rw = rw'`,
  MESON_TAC[component_tybij]);;

let FORALL_COMPONENT = prove
 (`(!c:(S,V)component. P c) <=> !r w. P(component(r,w))`,
  MESON_TAC[component_tybij; PAIR]);;

let EXISTS_COMPONENT = prove
 (`(?c:(S,V)component. P c) <=> ?r w. P(component(r,w))`,
  MESON_TAC[component_tybij; PAIR]);;

let read_def = new_definition
 `read (c:(S,V)component) = FST(dest_component c)`;;

let write_def = new_definition
 `write (c:(S,V)component) = SND(dest_component c)`;;

let read = prove
 (`!(r:S->V) w. read(component(r,w)) = r`,
  REWRITE_TAC[read_def; component_tybij]);;

let write = prove
 (`!(r:S->V) w. write(component(r,w)) = w`,
  REWRITE_TAC[write_def; component_tybij]);;

let COMPONENT_EQ = prove
 (`!c1 c2. c1 = c2 <=> read c1 = read c2 /\ write c1 = write c2`,
  REWRITE_TAC[COMPONENT_INJ; FORALL_COMPONENT; read; write; PAIR_EQ]);;

(* ------------------------------------------------------------------------- *)
(* A sort of identity for state components, corresponding to the full state. *)
(* ------------------------------------------------------------------------- *)

let entirety = new_definition
 `entirety = component((\s:S. s),(\x:S s:S. x))`;;

let READ_ENTIRETY = prove
 (`read entirety = I /\ (!s. read entirety s = s)`,
  REWRITE_TAC[read; entirety; I_THM; FUN_EQ_THM]);;

let WRITE_ENTIRETY = prove
 (`(!y. write entirety y = \s. y) /\ (!s y. write entirety y s = y)`,
  REWRITE_TAC[write; entirety; I_THM; FUN_EQ_THM]);;

let READ_WRITE_ENTIRETY = prove
 (`!y s. read entirety (write entirety y s) = y`,
  REWRITE_TAC[WRITE_ENTIRETY; READ_ENTIRETY; I_DEF]);;

add_component_read_write_thms [READ_WRITE_ENTIRETY];;

(* ------------------------------------------------------------------------- *)
(* Composition operation on state components.                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix(":>",(28,"right"));;

let component_compose = new_definition
  `(c1:(S,T)component) :> (c2:(T,U)component) =
        component((read c2 o read c1),
                  (\v s. write c1 (write c2 v (read c1 s)) s))`;;

let COMPONENT_COMPOSE_ASSOC = prove
 (`!sc1 sc2 sc3. sc1 :> (sc2 :> sc3) = (sc1 :> sc2) :> sc3`,
  REWRITE_TAC[FORALL_COMPONENT; component_compose; read; write; o_DEF]);;

let READ_COMPONENT_COMPOSE = prove
 (`!sc1 sc2 s. read (sc1 :> sc2) s = read sc2 (read sc1 s)`,
  REWRITE_TAC[FORALL_COMPONENT; read; component_compose; read; write; o_DEF]);;

let WRITE_COMPONENT_COMPOSE = prove
 (`!sc1 sc2 s x. write (sc1 :> sc2) x s =
                 write sc1 (write sc2 x (read sc1 s)) s`,
  REWRITE_TAC[FORALL_COMPONENT; read; write; component_compose]);;

let COMPOSE_ENTIRETY = prove
 (`(!c. c :> entirety = c) /\ (!c. entirety :> c = c)`,
  REWRITE_TAC[FORALL_COMPONENT; component_compose; entirety; FUN_EQ_THM;
              read; write; COMPONENT_EQ; o_DEF]);;

let READ_WRITE_COMPONENT_COMPOSE = prove
 (`!sc1 sc2.
        (!y s. read sc1 (write sc1 y s) = y) /\
        (!y s. read sc2 (write sc2 y s) = y)
        ==> !y s. read (sc1 :> sc2) (write (sc1 :> sc2) y s) = y`,
  SIMP_TAC[READ_COMPONENT_COMPOSE; WRITE_COMPONENT_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Individual read-versus-write properties                                   *)
(* ------------------------------------------------------------------------- *)

let read_over_write = new_definition
 `read_over_write (c:(S,A)component) <=>
        !y s. read c (write c y s) = y`;;

let write_over_write = new_definition
 `write_over_write (c:(S,A)component) <=>
        !y z s. write c z (write c y s) = write c z s`;;

let write_over_read = new_definition
 `write_over_read (c:(S,A)component) <=>
     !s. write c (read c s) s = s`;;

let weak_read_over_write = new_definition
 `weak_read_over_write (c:(S,A)component) <=>
        ?f. !y s. read c (write c y s) = f y`;;

(* ------------------------------------------------------------------------- *)
(* Valid state components.                                                   *)
(* ------------------------------------------------------------------------- *)

let valid_component = define
 `valid_component c <=>
        (!y s. read c (write c y s) = y) /\
        (!y z s. write c z (write c y s) = write c z s)`;;

let VALID_COMPONENT_COMPOSE = prove
 (`!c1 c2. valid_component c1 /\ valid_component c2
           ==> valid_component(c1 :> c2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[valid_component] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[WRITE_COMPONENT_COMPOSE; READ_COMPONENT_COMPOSE]);;

let VALID_COMPONENT_ENTIRETY = prove
 (`valid_component entirety`,
  REWRITE_TAC[valid_component; WRITE_ENTIRETY; READ_ENTIRETY; I_DEF]);;

add_valid_component_thms [VALID_COMPONENT_ENTIRETY];;

(* ------------------------------------------------------------------------- *)
(* A slightly weaker version where writes may be modified (e.g. truncated).  *)
(* ------------------------------------------------------------------------- *)

let weakly_valid_component = define
 `weakly_valid_component c <=>
        (?f. !y s. read c (write c y s) = f y) /\
        (!y z s. write c z (write c y s) = write c z s)`;;

let VALID_IMP_WEAKLY_VALID_COMPONENT = prove
 (`!c:(S,V)component. valid_component c ==> weakly_valid_component c`,
  REWRITE_TAC[valid_component; weakly_valid_component] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\x:V. x` THEN ASM_REWRITE_TAC[]);;

let WEAKLY_VALID_COMPONENT_ENTIRETY = prove
 (`weakly_valid_component entirety`,
  SIMP_TAC[VALID_IMP_WEAKLY_VALID_COMPONENT; VALID_COMPONENT_ENTIRETY]);;

add_weakly_valid_component_thms [WEAKLY_VALID_COMPONENT_ENTIRETY];;

(* ------------------------------------------------------------------------- *)
(* A stronger notion more in line with our expectations.                     *)
(* ------------------------------------------------------------------------- *)

let strongly_valid_component = define
 `strongly_valid_component c <=>
        (!y s. read c (write c y s) = y) /\
        (!s. write c (read c s) s = s) /\
        (!y z s. write c z (write c y s) = write c z s)`;;

let STRONGLY_VALID_IMP_VALID_COMPONENT = prove
 (`!c:(S,V)component. strongly_valid_component c ==> valid_component c`,
  SIMP_TAC[valid_component; strongly_valid_component]);;

let STRONGLY_VALID_COMPONENT_COMPOSE = prove
 (`!c1 c2. strongly_valid_component c1 /\ strongly_valid_component c2
           ==> strongly_valid_component(c1 :> c2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[strongly_valid_component] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[WRITE_COMPONENT_COMPOSE; READ_COMPONENT_COMPOSE]);;

let STRONGLY_VALID_COMPONENT_ENTIRETY = prove
 (`strongly_valid_component entirety`,
  REWRITE_TAC[strongly_valid_component; READ_ENTIRETY; WRITE_ENTIRETY]);;

add_strongly_valid_component_thms [STRONGLY_VALID_COMPONENT_ENTIRETY];;

(* ------------------------------------------------------------------------- *)
(* And likewise a version of that allowing write truncation.                 *)
(* ------------------------------------------------------------------------- *)

let extensionally_valid_component = define
 `extensionally_valid_component (c:(S,A)component) <=>
        (?f. !y s. read c (write c y s) = f y) /\
        (!s. write c (read c s) s = s) /\
        (!y z s. write c z (write c y s) = write c z s)`;;

let STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT = prove
 (`!c:(S,V)component.
        strongly_valid_component c ==> extensionally_valid_component c`,
  REWRITE_TAC[extensionally_valid_component; strongly_valid_component] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\x:V. x` THEN ASM_REWRITE_TAC[]);;

let EXTENSIONALLY_VALID_COMPONENT_ENTIRETY = prove
 (`extensionally_valid_component entirety`,
  SIMP_TAC[STRONGLY_VALID_COMPONENT_ENTIRETY;
           STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT]);;

add_extensionally_valid_component_thms
  [EXTENSIONALLY_VALID_COMPONENT_ENTIRETY];;

(* ------------------------------------------------------------------------- *)
(* General independence/orthogonality of state components.                   *)
(* ------------------------------------------------------------------------- *)

let orthogonal_components = define
 `orthogonal_components sc1 sc2 <=>
        (!y z s. write sc1 y (write sc2 z s) =
                 write sc2 z (write sc1 y s)) /\
        (!y s. read sc2 (write sc1 y s) = read sc2 s) /\
        (!z s. read sc1 (write sc2 z s) = read sc1 s)`;;

let ORTHOGONAL_COMPONENTS_SYM = prove
 (`!sc1 sc2. orthogonal_components sc1 sc2 <=> orthogonal_components sc2 sc1`,
  REWRITE_TAC[orthogonal_components] THEN MESON_TAC[]);;
