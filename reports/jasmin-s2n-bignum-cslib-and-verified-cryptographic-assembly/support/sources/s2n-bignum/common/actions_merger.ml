(* ------------------------------------------------------------------------- *)
(* OCaml functions to merge diffs (called 'actions') that are used for       *)
(* equivalence checking, specifically EQUIV_STEPS_TAC.                       *)
(* ------------------------------------------------------------------------- *)

let rec get_ranges_base (actions1,actions2) =
  match actions1,actions2 with
  | [],[] -> []
  | [],(op2,lbeg2',lend2',_,_)::actions2' ->
    lend2'::get_ranges_base ([],actions2')
  | (op1,_,_,lbeg2,lend2)::actions1',[] ->
    lend2::get_ranges_base (actions1',[])
  | (_,_,_,lbeg2,lend2)::actions1', (_,lbeg2',lend2',_,_)::actions2' ->
    if lend2 < lend2' then
      lend2::get_ranges_base (actions1',actions2)
    else if lend2' < lend2 then
      lend2'::get_ranges_base (actions1,actions2')
    else
      lend2::get_ranges_base (actions1',actions2');;

let get_ranges (actions1,actions2) =
  let r = get_ranges_base (actions1,actions2) in
  let rec f r =
    match r with
    | 0::t -> f t
    | h1::h2::t ->
      if h1 = h2 then f (h1::t)
      else h1::f (h2::t)
    | t -> t
    in
  f r;;

assert (get_ranges (["equal",0,2,0,2;"insert",2,2,2,4], ["equal",0,4,0,4])
  = [2;4]);;

assert (get_ranges (["equal",0,2,0,2], ["insert",0,0,0,3;"equal",0,2,3,5])
  = [2]);;

assert (get_ranges (["delete",0,2,0,0;"equal",2,4,0,2], ["insert",0,0,0,3;"equal",0,2,3,5])
  = [2]);;

let rec split_actions1 actions ranges =
  match actions,ranges with
  | [],[] -> []
  | [],_ -> failwith "ranges don't match"
  | ("delete",lbeg1,lend1,lbeg2,lend2)::actions', _ ->
    assert (lbeg2 = lend2);
    ("delete",lbeg1,lend1,lbeg2,lend2)::split_actions1 actions' ranges
  | (op,lbeg1,lend1,lbeg2,lend2)::actions', r::ranges' ->
    assert (r <= lend2);
    if (r = lend2) then
      (op,lbeg1,lend1,lbeg2,lend2)::split_actions1 actions' ranges'
    else
      let len = r - lbeg2 in
      begin match op with
      | "equal" ->
        (op,lbeg1,lbeg1+len,lbeg2,lbeg2+len)::
        split_actions1 ((op,lbeg1+len,lend1,lbeg2+len,lend2)::actions') ranges'
      | "insert" ->
        assert (lbeg1 = lend1);
        (op,lbeg1,lbeg1,lbeg2,lbeg2+len)::
        split_actions1 ((op,lbeg1,lbeg1,lbeg2+len,lend2)::actions') ranges'
      | _ -> failwith "unknown case"
      end;;

assert (split_actions1 ["equal",0,3,0,3] [1;3] =
  [("equal", 0, 1, 0, 1); ("equal", 1, 3, 1, 3)]);;

assert (split_actions1 ["insert",0,0,0,3] [1;3] =
  [("insert", 0, 0, 0, 1); ("insert", 0, 0, 1, 3)]);;

assert (split_actions1 ["delete",0,3,0,0;"equal",3,5,0,2] [1;2] =
  [("delete", 0, 3, 0, 0); ("equal", 3, 4, 0, 1); ("equal", 4, 5, 1, 2)]);;

let rec split_actions2 actions ranges =
  match actions,ranges with
  | [],[] -> []
  | [],_ -> failwith "ranges don't match"
  | ("insert",lbeg2,lend2,lbeg3,lend3)::actions', _ ->
    assert (lbeg2 = lend2);
    ("insert",lbeg2,lend2,lbeg3,lend3)::split_actions2 actions' ranges
  | (op,lbeg2,lend2,lbeg3,lend3)::actions', r::ranges' ->
    assert (r <= lend2);
    if (r = lbeg2) then split_actions2 actions ranges'
    else if (r = lend2) then
      (op,lbeg2,lend2,lbeg3,lend3)::split_actions2 actions' ranges'
    else
      let len = r - lbeg2 in
      begin match op with
      | "equal" ->
        (op,lbeg2,lbeg2+len,lbeg3,lbeg3+len)::
        split_actions2 ((op,lbeg2+len,lend2,lbeg3+len,lend3)::actions') ranges'
      | "delete" ->
        assert (lbeg3 = lend3);
        (op,lbeg2,lbeg2+len,lbeg3,lbeg3)::
        split_actions2 ((op,lbeg2+len,lend2,lbeg3,lend3)::actions') ranges'
      | _ -> failwith "unknown case"
      end;;

assert (split_actions2 ["equal",0,3,0,3] [1;3] =
  [("equal", 0, 1, 0, 1); ("equal", 1, 3, 1, 3)]);;

assert (split_actions2 ["delete",0,3,0,0] [1;3] =
  [("delete", 0, 1, 0, 0); ("delete", 1, 3, 0, 0)]);;

assert (split_actions2 [("equal", 1, 2, 3, 4)] [1;2] =
  [("equal", 1, 2, 3, 4)]);;


let rec merge_actions_base
    ((actions1:(string*int*int*int*int) list),
     (actions2:(string*int*int*int*int) list))
    (file1_lastofs,file2_lastofs) =
  match actions1, actions2 with
  | (op1,lbeg1,lend1,lbeg2,lend2)::actions1',
    (op2,lbeg2',lend2',lbeg3,lend3)::actions2' ->
    assert (lbeg2 = lbeg2');
    assert (file1_lastofs <= lend1 && file2_lastofs <= lend3);
    if op1 = "delete" then begin
      assert (lbeg2 = lend2);
      (op1,lbeg1,lend1,lbeg3,lbeg3)::merge_actions_base (actions1',actions2) (lend1,lend3)
    end
    else if op2 = "insert" then begin
      assert (lbeg2' = lend2');
      (op2,lbeg1,lbeg1,lbeg3,lend3)::merge_actions_base (actions1,actions2') (lend1,lend3)
    end
    else begin
      assert (lend2 = lend2');
      begin match op1,op2 with
      | "equal","equal" ->
        ("equal",lbeg1,lend1,lbeg3,lend3)::merge_actions_base (actions1',actions2') (lend1,lend3)
      | "insert","equal" ->
        assert (lbeg1 = lend1);
        ("insert",lbeg1,lend1,lbeg3,lend3)::merge_actions_base (actions1',actions2') (lend1,lend3)
      | "equal","delete" ->
        assert (lbeg3 = lend3);
        ("delete",lbeg1,lend1,lbeg3,lend3)::merge_actions_base (actions1',actions2') (lend1,lend3)
      | "insert","delete" ->
        merge_actions_base (actions1',actions2') (file1_lastofs,file2_lastofs)
      | _ -> failwith (Printf.sprintf "unknown op: %s,%s" op1 op2)
      end
    end
  | [],("insert",lbeg2',lend2',lbeg3,lend3)::actions2' ->
    ("insert",file1_lastofs,file1_lastofs,lbeg3,lend3)::
    merge_actions_base ([], actions2') (file1_lastofs,lend3)
  | ("delete",lbeg1,lend1,lbeg2,lend2)::actions1',[] ->
    ("delete",lbeg1,lend1,file2_lastofs,file2_lastofs)::
    merge_actions_base (actions1',[]) (lend1,file2_lastofs)
  | [],[] -> [];;

(* Combine fragmented operations *)
let rec merge_actions_combine actions =
  match actions with
  | [] -> []
  | a::[] -> a::[]
  | ("equal",lbeg1,lend1,lbeg2,lend2)::("equal",lbeg1',lend1',lbeg2',lend2')::t ->
    assert (lend1 = lbeg1' && lend2 = lbeg2');
    merge_actions_combine (("equal",lbeg1,lend1',lbeg2,lend2')::t)
  | ("insert",lbeg1,lend1,lbeg2,lend2)::("insert",lbeg2',lend2',lbeg3,lend3)::t ->
    assert (lbeg1 = lend1 && lbeg1 = lbeg2' && lbeg1 = lend2');
    assert (lend2 = lbeg3);
    merge_actions_combine (("insert",lbeg1,lend1,lbeg2,lend3)::t)
  | h1::t ->
    h1::merge_actions_combine t;;

(* The main function. *)
let merge_actions (actions1, actions2) =
  let rec preproc actions =
    match actions with
    | ("replace",b,e,b2,e2)::actions' ->
      ("delete",b,e,b2,b2)::("insert",e,e,b2,e2)::preproc actions'
    | h::t -> h::preproc t
    | [] -> [] in
  let actions1,actions2 = preproc actions1,preproc actions2 in
  let rs = get_ranges (actions1, actions2) in
  let actions1 = split_actions1 actions1 rs in
  let actions2 = split_actions2 actions2 rs in
  let res_base = merge_actions_base (actions1, actions2) (0,0) in
  merge_actions_combine res_base;;

assert (merge_actions
  ([("equal",0,2,0,2)],
   [("equal",0,2,0,2)]) = [("equal",0,2,0,2)]);;

assert (merge_actions
  ([("equal",0,2,0,2)],
   [("insert",0,0,0,1);("equal",0,2,1,3)]) =
  [("insert", 0, 0, 0, 1); ("equal", 0, 2, 1, 3)]);;

assert (merge_actions
  ([("equal",0,2,0,2)],
   [("equal",0,2,0,2);("insert",2,2,2,4)]) =
  [("equal", 0, 2, 0, 2); ("insert", 2, 2, 2, 4)]);;

assert (merge_actions
  ([("equal",0,2,0,2)],
   [("equal",0,1,0,1);("insert",1,1,1,3);("equal",1,2,3,4)]) =
  [("equal", 0, 1, 0, 1); ("insert", 1, 1, 1, 3); ("equal", 1, 2, 3, 4)]);;

assert (merge_actions
  ([("equal",0,1,0,1);("insert",1,1,1,2)], [("equal",0,2,0,2)]) =
  [("equal", 0, 1, 0, 1); ("insert", 1, 1, 1, 2)]);;

assert (merge_actions
  ([("insert",0,0,0,1)], [("equal",0,1,0,1);("insert",1,1,1,2)]) =
   [("insert", 0, 0, 0, 2)]);;

assert (merge_actions
  ([("insert",0,0,0,2)], [("equal",0,1,0,1);("insert",1,1,1,2);("equal",1,2,2,3)]) =
   [("insert", 0, 0, 0, 3)]);;

assert (merge_actions
  ([("equal",0,10,0,10);("insert",10,10,10,20);("equal",10,20,20,30)],
   [("equal",0,30,0,30)]) =
  ([("equal", 0, 10, 0, 10); ("insert", 10, 10, 10, 20);
   ("equal", 10, 20, 20, 30)]));;

assert (merge_actions
  ([("equal", 0, 3, 0, 3);
    ("insert", 3, 3, 3, 5);
    ("equal", 3, 4, 5, 6);
    ("insert", 4, 4, 6, 8);
    ("equal", 4, 51, 8, 55)],
   [("equal", 0, 1, 0, 1);
    ("insert", 1, 1, 1, 3);
    ("equal", 1, 55, 3, 57)]) =
   [("equal", 0, 1, 0, 1); ("insert", 1, 1, 1, 3); ("equal", 1, 3, 3, 5);
    ("insert", 3, 3, 5, 7); ("equal", 3, 4, 7, 8); ("insert", 4, 4, 8, 10);
    ("equal", 4, 51, 10, 57)]);;

assert (merge_actions
  ([("replace",0,2,0,3)], [("replace",0,3,0,4)]) =
  [("delete", 0, 2, 0, 0); ("insert", 2, 2, 0, 4)]);;


