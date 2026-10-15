(* ========================================================================= *)
(* Term nets: reasonably fast lookup based on term matchability.             *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "basics.ml";;

(* ------------------------------------------------------------------------- *)
(* Term nets are a finitely branching tree structure; at each level we       *)
(* have a set of branches and a set of "values". Linearization is            *)
(* performed from the left of a combination; even in iterated                *)
(* combinations we look at the head first. This is probably fastest, and     *)
(* anyway it's useful to allow our restricted second order matches: if       *)
(* the head is a variable then then whole term is treated as a variable.     *)
(* ------------------------------------------------------------------------- *)

type term_label = Vnet                          (* variable (instantiable)   *)
                 | Lcnet of (string * int)      (* local constant            *)
                 | Cnet of (string * int)       (* constant                  *)
                 | Lnet of int;;                (* lambda term (abstraction) *)

(* ------------------------------------------------------------------------- *)
(* Edges out of a net node are split by label kind. The Vnet edge is unique  *)
(* (so it's a direct field, looked up in O(1)); the others are persistent    *)
(* balanced trees keyed by (string * int) or int with monomorphic            *)
(* comparators. This gives O(log n) per-edge lookup.                         *)
(* ------------------------------------------------------------------------- *)

module Sikey = struct
  type t = string * int
  let compare (s1,i1) (s2,i2) =
    let c = String.compare s1 s2 in
    if c <> 0 then c else compare (i1:int) i2
end;;

module Intkey = struct
  type t = int
  let compare (i1:int) i2 = compare i1 i2
end;;

module Si_map = Map.Make(Sikey);;
module I_map = Map.Make(Intkey);;

type 'a netnode_data = {
  vnet: 'a net option;
  cnets: 'a net Si_map.t;
  lcnets: 'a net Si_map.t;
  lnets: 'a net I_map.t;
  tips: 'a list;
}
and 'a net = Netnode of 'a netnode_data;;

(* ------------------------------------------------------------------------- *)
(* The empty net.                                                            *)
(* ------------------------------------------------------------------------- *)

let empty_net =
  Netnode { vnet = None;
            cnets = Si_map.empty;
            lcnets = Si_map.empty;
            lnets = I_map.empty;
            tips = [] };;

(* ------------------------------------------------------------------------- *)
(* Insert a new element into a net.                                          *)
(* ------------------------------------------------------------------------- *)

let enter =
  let label_to_store (lconsts:term list) (tm:term) : term_label * term list =
    let op,args = strip_comb tm in
    if is_const op then Cnet(fst(dest_const op),length args),args
    else if is_abs op then
      let bv,bod = dest_abs op in
      let bod' = if mem bv lconsts then vsubst [genvar(type_of bv),bv] bod
                 else bod in
      Lnet(length args),bod'::args
    else if mem op lconsts then Lcnet(fst(dest_var op),length args),args
    else Vnet,[] in
  let canon_eq x y =
    try compare x y = 0 with Invalid_argument _ -> false
  and canon_lt x y =
    try compare x y < 0 with Invalid_argument _ -> false in
  let rec sinsert x l =
    if l = [] then [x] else
    let h = hd l in
    if canon_eq h x then failwith "sinsert" else
    if canon_lt x h then x::l else
    h::(sinsert x (tl l)) in
  let set_insert x l = try sinsert x l with Failure "sinsert" -> l in
  let update_si k upd m =
    let child0 = try Si_map.find k m with Not_found -> empty_net in
    Si_map.add k (upd child0) m in
  let update_int k upd m =
    let child0 = try I_map.find k m with Not_found -> empty_net in
    I_map.add k (upd child0) m in
  let rec net_update (lconsts:term list) (elem:'a)
                     (tms:term list) (net:'a net) : 'a net =
    let Netnode r = net in
    match tms with
      [] -> Netnode { r with tips = set_insert elem r.tips }
    | (tm::rtms) ->
        let label,ntms = label_to_store lconsts tm in
        let upd child = net_update lconsts elem (ntms@rtms) child in
        match (label:term_label) with
          Vnet ->
            let child0 =
              match r.vnet with Some c -> c | None -> empty_net in
            Netnode { r with vnet = Some (upd child0) }
        | Cnet k ->
            Netnode { r with cnets = update_si k upd r.cnets }
        | Lcnet k ->
            Netnode { r with lcnets = update_si k upd r.lcnets }
        | Lnet k ->
            Netnode { r with lnets = update_int k upd r.lnets } in
  fun lconsts (tm,elem) net -> net_update lconsts elem [tm] net;;

(* ------------------------------------------------------------------------- *)
(* Look up a term in a net and return possible matches.                      *)
(* ------------------------------------------------------------------------- *)

let lookup =
  let label_for_lookup (tm:term) : term_label * term list =
    let op,args = strip_comb tm in
    if is_const op then Cnet(fst(dest_const op),length args),args
    else if is_abs op then Lnet(length args),(body op)::args
    else Lcnet(fst(dest_var op),length args),args in
  let rec follow (tms:term list) (net:'a net) : 'a list =
    let Netnode r = net in
    match tms with
      [] -> r.tips
    | (tm::rtms) ->
        let label,ntms = label_for_lookup tm in
        let collection =
          match (label:term_label) with
            Cnet k ->
              (try follow (ntms@rtms) (Si_map.find k r.cnets)
               with Not_found -> [])
          | Lcnet k ->
              (try follow (ntms@rtms) (Si_map.find k r.lcnets)
               with Not_found -> [])
          | Lnet k ->
              (try follow (ntms@rtms) (I_map.find k r.lnets)
               with Not_found -> [])
          | Vnet -> [] in
        match r.vnet with
          None -> collection
        | Some vchild -> collection @ follow rtms vchild in
  fun tm net -> follow [tm] net;;

(* ------------------------------------------------------------------------- *)
(* Function to merge two nets (code from Don Syme's hol-lite).               *)
(* ------------------------------------------------------------------------- *)

let merge_nets =
  let canon_eq x y =
    try compare x y = 0 with Invalid_argument _ -> false
  and canon_lt x y =
    try compare x y < 0 with Invalid_argument _ -> false in
  let rec set_merge l1 l2 =
    if l1 = [] then l2
    else if l2 = [] then l1 else
    let h1 = hd l1 and t1 = tl l1
    and h2 = hd l2 and t2 = tl l2 in
    if canon_eq h1 h2 then h1::(set_merge t1 t2)
    else if canon_lt h1 h2 then h1::(set_merge t1 l2)
    else h2::(set_merge l1 t2) in
  let rec merge_nets (n1,n2) =
    let Netnode r1 = n1 and Netnode r2 = n2 in
    let merge_opt a b =
      match a,b with
        Some x, Some y -> Some (merge_nets (x,y))
      | Some _, None -> a
      | None, _ -> b in
    let merge_si =
      Si_map.union (fun _ a b -> Some (merge_nets (a,b))) in
    let merge_int =
      I_map.union (fun _ a b -> Some (merge_nets (a,b))) in
    Netnode {
      vnet = merge_opt r1.vnet r2.vnet;
      cnets = merge_si r1.cnets r2.cnets;
      lcnets = merge_si r1.lcnets r2.lcnets;
      lnets = merge_int r1.lnets r2.lnets;
      tips = set_merge r1.tips r2.tips;
    } in
  merge_nets;;
