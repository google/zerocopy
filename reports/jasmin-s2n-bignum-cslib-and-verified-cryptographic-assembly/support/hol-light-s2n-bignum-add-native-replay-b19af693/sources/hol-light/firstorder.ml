(* ========================================================================= *)
(* General facilities for manipulating first-order shadow terms.             *)
(*                                                                           *)
(*   (c) Copyright, Michael Faerber and Cezary Kaliszyk, 2014-2018.          *)
(* ========================================================================= *)

needs "meson.ml";;

(* ------------------------------------------------------------------------- *)
(* Controls verbosity of these and the main CoP functions.                   *)
(* ------------------------------------------------------------------------- *)

let copverb = ref false;;           (* Controls output verbosity of the CoPs *)

(* ------------------------------------------------------------------------- *)
(* Misc utility functions.                                                   *)
(* ------------------------------------------------------------------------- *)

module Utils = struct

let ( %> ) f g x = g (f x)

let ( % ) f g x = f (g x)

let const x _ = x

let ( >>= ) x f = match x with None -> None | Some y -> f y


module Pair =
struct

let mapn f (x, y) = (f x, f y)

end


module List =
struct

include List

let cons x l = x :: l

let list_rest l =
  let rec go acc = function
    x :: xs -> (x, (acc, xs)) :: go (x :: acc) xs
  | [] -> [] in
  go [] l

(* "nth_rest i l" returns the i-th element of l as well as
   the elements before and after (in order)
*)
let nth_rest n =
  let rec go acc i = function
    x :: xs when i > 0 -> go (x :: acc) (i-1) xs
  | x :: xs when i = 0 -> x, (List.rev acc, xs)
  | _ -> failwith "nth_rest"
  in go [] n

let insert_at i elem l =
  let rec go acc = function
    (0, xs) -> List.rev_append acc (elem::xs)
  | (n, []) -> failwith "insert_at"
  | (n, x :: xs) -> go (x::acc) (n-1, xs)
  in go [] (i, l)

let take_drop n =
  let rec go acc i = function
    []      when i > 0 -> failwith "take_drop"
  | x :: xs when i > 0 -> go (x::acc) (i-1) xs
  | xs -> List.rev acc, xs
  in go [] n

let take n l = fst (take_drop n l)

let rec findi p l =
  let rec loop n = function
    | [] -> raise Not_found
    | h :: t ->
      if p n h then (n,h) else loop (n+1) t
  in loop 0 l

let concat_map f l = List.concat (List.map f l)

let fsum = List.fold_left (+.) 0.

let rec last = function
    [] -> failwith "last"
  | [h] -> h
  | h :: t -> last t

let rec union1 x y = match x with
    [] -> y
  | h :: t -> if List.mem h y then union1 t y else h :: union1 t y

(* tail-recursive version -- reverses first argument *)
let rec union2 x y = match x with
    [] -> y
  | h :: t -> if List.mem h y then union1 t y else union2 t (h :: y)

let rec fold_right1 f = function
    x :: [] -> x
  | x :: xs -> f x (fold_right1 f xs)
  | [] -> failwith "fold_right1"

let fold_left_map f acc = List.fold_left
  (fun (acc, ys) x -> let (acc', y) = f acc x in (acc', y :: ys)) (acc, [])

let fold_right_map f acc xs = List.fold_right
  (fun x (acc, ys) -> let (acc', y) = f acc x in (acc', y :: ys)) xs (acc, [])

let fold_map f sf l = let (sf, rev) = fold_left_map f sf l in sf, List.rev rev

let rec filter_map f = function
    [] -> []
  | x :: xs -> (match f x with None -> filter_map f xs | Some y -> y :: filter_map f xs)

let exists_unique p l =
  let rec go acc = function
    [] -> acc
  | x :: xs -> if p x then (if acc then false else go true xs) else go acc xs
  in go false l

end


end

(* ------------------------------------------------------------------------- *)
(* Adapted from meson.ml. The main change is that creating HOL versions of   *)
(* fresh variables requires HOL types.                                       *)
(* ------------------------------------------------------------------------- *)


module Mapping = struct

  let reset_vars,fol_of_var,hol_of_var =
    let vstore = ref []
    and gstore = ref []
    and vcounter = ref 0 in
    let inc_vcounter() =
      let n = !vcounter in
      let m = n + 1 in
      (vcounter := m; n) in
    let reset_vars() = vstore := []; gstore := []; vcounter := 0 in
    let fol_of_var v =
      try assoc v !vstore with Failure _ ->
      let n = inc_vcounter() in
      if !copverb then
        Format.printf "fol_of_var: %s (ty = %s) <- %d\n%!"
        (string_of_term v) (string_of_type (type_of v)) n;
      vstore := (v,n)::!vstore; n in
    let hol_of_var v ty =
      try rev_assoc v !gstore with Failure _ ->
      let gv = genvar ty in
      gstore := (gv,v)::!gstore; gv in
    reset_vars,fol_of_var,hol_of_var

  let reset_consts,fol_of_const,hol_of_const =
    Meson.reset_consts,Meson.fol_of_const,Meson.hol_of_const

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

  let rec hol_of_term ty tm =
    match tm with
      Fvar v -> hol_of_var v ty
    | Fnapp (f,args) -> hol_of_atom (f, args)
  and hol_of_atom (f, args) =
    let f' = hol_of_const f in
    let tys = fst (splitlist dest_fun_ty (type_of f')) in
    (* Functions can be translated to FOF
       without the full number of its arguments (due to partial application).
       Therefore obtain only as many types of arguments
       as present in the FO term. *)
    assert (List.length args <= List.length tys);
    let tys' = Utils.List.take (List.length args) tys in
    list_mk_comb (f', List.map2 hol_of_term tys' args)

  let hol_of_literal (p,args) =
    if p < 0 then mk_neg(hol_of_atom(-p,args))
    else hol_of_atom (p,args)


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
      | h::t -> let nw = (map Meson.mk_negated (used @ t),h),(n,th) in
                mk_contraposes (n + 1) th (used@[h]) t (nw::sofar) in
    let fol_of_hol_clause th =
      let lconsts = freesl (hyp th) in
      let tm = concl th in
      let hlits = disjuncts tm in
      let flits = map (fol_of_literal [] lconsts) hlits in
      let basics = mk_contraposes 0 th [] flits [] in
      if forall (fun (p,_) -> p < 0) flits then
        ((map Meson.mk_negated flits,(1,[])),(-1,th))::basics
      else basics in
    fun thms ->
      let rawrules = itlist (union' eqt o fol_of_hol_clause) thms [] in
      let prs = setify (map (fst o snd o fst) rawrules) in
      let prules =
        map (fun t -> t,filter ((=) t o fst o snd o fst) rawrules) prs in
      let srules = sort (fun (p,_) (q,_) -> abs(p) <= abs(q)) prules in
      srules

end
