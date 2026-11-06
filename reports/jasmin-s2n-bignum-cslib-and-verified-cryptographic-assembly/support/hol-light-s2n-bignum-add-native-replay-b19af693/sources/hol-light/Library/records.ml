(* ========================================================================= *)
(* Definition of record types, defining standard components for the fields.  *)
(*                                                                           *)
(* Ported from s2n-bignum (common/records.ml).                               *)
(* ========================================================================= *)

needs "Library/components.ml";;

let parse_record_specification =
  let ptype src =
    let pty,rst = parse_pretype src in
    type_of_pretype pty,rst in
  let recordelement src =
    match src with
      (Ident t)::(Resword ":")::rst ->
        let ty,ors = ptype rst in
        (t,ty),ors
    | _ -> raise Noparse in
 let recordelements =
   listof recordelement (a(Resword ";")) "';' or '}'" in
 let recspec =
   a (Resword "{") ++ recordelements ++ a (Resword "}")
        >> (fun ((_,s),_) -> s) in
 fun s -> match lex(explode s) with
            ((Ident tyname)::(Ident "=")::rst) ->
               let rs,er = recspec rst in
               if er <> [] then failwith "Stuff after record spec"
               else tyname,rs
          | _ -> raise Noparse;;

let define_record_type =
  let tweak = (MATCH_MP o prove)
   (`(?r. P r) /\ (?w. Q w) ==> ?c. P(read c) /\ Q(write c)`,
    REWRITE_TAC[EXISTS_COMPONENT; read; write] THEN MESON_TAC[]) in
  fun s ->
    let tyname,fields = parse_record_specification s in
    let tyname_rec = tyname^"_RECORD" in
    let ith,rth =
     define_type_raw [mk_vartype tyname,[tyname_rec,map snd fields]] in
    let f,ebod = dest_forall(concl rth) in
    let fn,abod = dest_exists ebod in
    let avs,eqn = strip_forall abod in
    let left = rand(lhand eqn) in
    let leftys = mk_fun_ty (type_of left) (type_of left) in
    let fnms = map fst fields in
    let defs = map2
      (fun fnm v -> let vn,vty = dest_var v in
                    let v' = mk_var(vn^"'",vty) in
                    let right = subst [v',v] left in
                    let wfn = mk_var("writer",mk_fun_ty (type_of v) leftys) in
                    let wdef = mk_eq(mk_comb(mk_comb(wfn,v'),left),right) in
                    let wcdef = list_mk_forall(v'::avs,wdef) in
                    let wethm = prove_recursive_functions_exist rth wcdef in
                    let rfn = mk_var("reader",
                                     mk_fun_ty (type_of left) (type_of v)) in
                    let rdef = mk_eq(mk_comb(rfn,left),v) in
                    let rcdef = list_mk_forall(avs,rdef) in
                    let rethm = prove_recursive_functions_exist rth rcdef in
                    new_specification [fnm] (tweak (CONJ rethm wethm)))
      fnms avs in
    ith,rth,end_itlist CONJ defs;;

(* ------------------------------------------------------------------------- *)
(* Get the components out of a record definition                             *)
(* ------------------------------------------------------------------------- *)

let rec get_record_components cth =
  let cjs = conjuncts(concl cth) in
  let n = length cjs / 2 in
  let rcjs = map (fun i -> el (2 * i) cjs) (0--(n-1)) in
  map (lhand o lhand o snd o strip_forall) rcjs;;

(* ------------------------------------------------------------------------- *)
(* Construct "read and write same component" theorems for all fields.        *)
(* ------------------------------------------------------------------------- *)

let record_read_write_thms (ith,cth) =
  let pat = `!(y:B) (s:A). read c (write c y s) = y`
  and ctm = `c:(A,B)component` in
  let rule tm =
    prove(instantiate(term_match [] ctm tm) pat,
          REPEAT(MATCH_MP_TAC ith ORELSE GEN_TAC) THEN
          REWRITE_TAC[cth] THEN NO_TAC) in
  map rule (get_record_components cth);;

(* ------------------------------------------------------------------------- *)
(* Construct "valid component" for all fields.                               *)
(* ------------------------------------------------------------------------- *)

let record_strongly_valid_component_thms (ith,cth) =
  let rule tm =
    prove(list_mk_icomb "strongly_valid_component" [tm],
          GEN_REWRITE_TAC I [strongly_valid_component] THEN
          REPEAT CONJ_TAC THEN
          REPEAT(MATCH_MP_TAC ith ORELSE GEN_TAC) THEN
          REWRITE_TAC[cth] THEN NO_TAC) in
  map rule (get_record_components cth);;

let record_valid_component_thms (ith,cth) =
  map (MATCH_MP STRONGLY_VALID_IMP_VALID_COMPONENT)
      (record_strongly_valid_component_thms (ith,cth));;

let record_extensionally_valid_component_thms (ith,cth) =
  map (MATCH_MP STRONGLY_VALID_IMP_EXTENSIONALLY_VALID_COMPONENT)
      (record_strongly_valid_component_thms (ith,cth));;

let record_weakly_valid_component_thms (ith,cth) =
  map (MATCH_MP VALID_IMP_WEAKLY_VALID_COMPONENT)
      (record_valid_component_thms (ith,cth));;

(* ------------------------------------------------------------------------- *)
(* Create orthogonality theorems for all distinct pairs.                     *)
(* ------------------------------------------------------------------------- *)

let record_orthogonality_thms (ith,cth) =
  let cmps = get_record_components cth in
  let dps = filter (fun (a,b) -> a <> b)
                   (allpairs (fun a b -> a,b) cmps cmps) in
  let cjs = map
   (fun (a,b) -> list_mk_icomb "orthogonal_components" [a;b]) dps in
  let tac =
    REWRITE_TAC[orthogonal_components] THEN
    REPEAT(CONJ_TAC ORELSE MATCH_MP_TAC ith ORELSE GEN_TAC) THEN
    REWRITE_TAC[cth] in
  map (fun tm -> prove(tm,tac)) cjs;;

(* ------------------------------------------------------------------------- *)
(* Combined function that does the definition and adds all the theorems.     *)
(* ------------------------------------------------------------------------- *)

let define_auto_record_type def =
  let ith,rth,cth = define_record_type def in
  (add_component_read_write_thms (record_read_write_thms (ith,cth));
   add_strongly_valid_component_thms
    (record_strongly_valid_component_thms (ith,cth));
   add_valid_component_thms (record_valid_component_thms (ith,cth));
   add_extensionally_valid_component_thms
    (record_extensionally_valid_component_thms (ith,cth));
   add_weakly_valid_component_thms
    (record_weakly_valid_component_thms (ith,cth));
   add_component_orthogonality_thms (record_orthogonality_thms (ith,cth));
   ith,rth,cth);;
