(* ========================================================================= *)
(* Metis first-order theorem proving derived rule/tactic for HOL Light.      *)
(*                                                                           *)
(* The original Metis was written by Joe Hurd, and it has been widely used   *)
(* for first-order proofs in HOL4 and Isabelle; see:                         *)
(*                                                                           *)
(*            http://www.gilith.com/research/metis/                          *)
(*                                                                           *)
(* This is a port from SML to OCaml and proof-reconstructing integration     *)
(* with HOL Light, written by Michael Faerber and Cezary Kaliszyk.           *)
(*                                                                           *)
(*                (c) Copyright, Joe Hurd, 2001                              *)
(*             (c) Copyright, Joe Leslie-Hurd, 2004                          *)
(*   (c) Copyright, Michael Faerber and Cezary Kaliszyk, 2014-2018.          *)
(*                                                                           *)
(*            Distributed under the same license as HOL Light.               *)
(* ========================================================================= *)

needs "firstorder.ml";;

let metisverb = ref false;;

module Metis_prover = struct

(* ------------------------------------------------------------------------- *)
(* Emulating SML Word type (which is unsigned) and other operations.         *)
(* ------------------------------------------------------------------------- *)

module Word = struct

type word = int;;
let compare (x : word) (y : word) = compare x y;;

let shiftLeft (x, y) = x lsl y;;
let shiftRight (x, y) = x lsr y;;

(* This is only the same as the SML version, if there is no overflow *)
let minus (x,y) = x - y;;

let andb (x,y) = x land y;;
let orb  (x,y) = x lor y;;
let xorb (x,y) = x lxor y;;
let notb x = lnot x

let toInt x = x;;
let fromInt x = x;;

end

module Mlist = struct

let foldl f a l = List.fold_left  (fun acc x -> f (x, acc)) a l;;
let foldr f a l = List.fold_right (fun x acc -> f (x, acc)) l a;;
let null = function
    [] -> true
  | _  -> false
let tabulate (n,f) =
  let rec go i = if i == n then [] else f i :: go (i+1)
  in  go 0
let find p l = try Some (List.find p l) with Not_found -> None;;
let rec first f = function
    [] -> None
  | (x :: xs) -> (match f x with None -> first f xs | s -> s);;
let enumerate l = mapi (fun x y -> (x, y)) l
let revDivide l =
  let rec revDiv acc = function
      (l, 0) -> (acc,l)
    | ([], _) -> invalid_arg "Metis_prover.Mlist.revDivide"
    | (h :: t, n) -> revDiv (h :: acc) (t, n - 1)
  in fun n -> revDiv [] (l, n);;
let updateNth (n,x) l =
    let (a,b) = revDivide l n
    in
      match b with
        [] -> invalid_arg "Metis_prover.Mlist.updateNth"
      | (_ :: t) -> List.rev_append a (x :: t)
;;
let sortMap f cmp = function
    [] -> []
  | ([_] as l) -> l
  | xs ->
      let ncmp (m,_) (n,_) = cmp m n
      in let nxs = List.map (fun x -> (f x, x)) xs
      in let nys = List.sort ncmp nxs
    in
      List.map snd nys
    ;;

end

module Option = struct

let is_some = function
    Some _ -> true
  | None -> false;;

let bind opt f =
  match opt with
  | Some x -> f x
  | None   -> None

let value opt ~default =
  match opt with
  | Some x -> x
  | None   -> default

end

(* ========================================================================= *)
(* ML UTILITY FUNCTIONS                                                      *)
(* ========================================================================= *)

module Useful = struct

(* Marking critical sections of code. *)
let critical x = x;;

(* ------------------------------------------------------------------------- *)
(* Characters (MF).                                                          *)
(* ------------------------------------------------------------------------- *)

let isDigit c = '0' <= c && c <= '9'

(* ------------------------------------------------------------------------- *)
(* Exceptions.                                                               *)
(* ------------------------------------------------------------------------- *)

exception Bug of string;;

let total f x = try Some (f x) with Failure _ -> None;;

let exp m =
      let rec f x y z = match y with
          0 -> z
        | _ -> f (m (x,x)) (y / 2) (if y mod 2 = 0 then z else m (z,x))
    in
      f
    ;;

(* ------------------------------------------------------------------------- *)
(* Comparisons.                                                              *)
(* ------------------------------------------------------------------------- *)

let revCompare cmp x y = cmp y x;;

let prodCompare xCmp yCmp (x1,y1) (x2,y2) =
    let c = xCmp x1 x2 in if c <> 0 then c else yCmp y1 y2;;

let lexCompare cmp =
      let rec lex xs ys = match (xs, ys) with
          ([],[]) -> 0
        | ([], _ :: _) -> -1
        | (_ :: _, []) -> 1
        | (x :: xs, y :: ys) ->
            let c = cmp x y in if c <> 0 then c else lex xs ys
    in lex;;

let boolCompare x y = match (x, y) with
    (false, true) -> -1
  | (true, false) -> 1
  | _ -> 0;;

let intCompare (x : int) y = compare x y;;

(* ------------------------------------------------------------------------- *)
(* Strings.                                                                  *)
(* ------------------------------------------------------------------------- *)

let mkPrefix p s = p ^ s

let stripSuffix pred s =
  let rec strip pos =
    if pos < 0 then "" else
    if pred (s.[pos]) then strip (pos - 1)
    else String.sub s 0 (pos + 1)
  in strip (String.length s - 1);;

(* ------------------------------------------------------------------------- *)
(* Integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

let rec interval m = function
    0 -> []
  | len -> m :: interval (m + 1) (len - 1);;

let divides = function
    (_, 0) -> true
  | (0, _) -> false
  | (a, b) -> b mod (abs a) = 0;;
let divides = curry divides;;

(* ------------------------------------------------------------------------- *)
(* Useful impure features.                                                   *)
(* ------------------------------------------------------------------------- *)

let generator = ref 0;;

  let newIntThunk () =
      let n = !generator
      in generator := n + 1;
        n
      ;;

  let newIntsThunk k () =
      let
        n = !generator

        in generator := n + k;
          interval n k
      ;;

  let newInt () = newIntThunk ();;

  let newInts k =
      if k <= 0 then []
      else (newIntsThunk k) ();;

end

(* ========================================================================= *)
(* FINITE MAPS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* ========================================================================= *)

module Pmap = struct

(* ------------------------------------------------------------------------- *)
(* Converting a comparison function to an equality function.                 *)
(* ------------------------------------------------------------------------- *)

let equalKey compareKey key1 key2 = compareKey key1 key2 = 0;;

(* ------------------------------------------------------------------------- *)
(* Priorities.                                                               *)
(* ------------------------------------------------------------------------- *)

type priority = Word.word;;

let randomPriority = Random.bits;;

let comparePriority = Word.compare;;

(* ------------------------------------------------------------------------- *)
(* Priority search trees.                                                    *)
(* ------------------------------------------------------------------------- *)

type ('key,'value) tree =
    Empty
  | Tree of ('key,'value) node

and ('key,'value) node =
      {size : int;
       priority : priority;
       left : ('key,'value) tree;
       key : 'key;
       value : 'value;
       right : ('key,'value) tree};;

let lowerPriorityNode node1 node2 =
      let {priority = p1} = node1
      and {priority = p2} = node2
    in
      comparePriority p1 p2 < 0
    ;;

(* ------------------------------------------------------------------------- *)
(* Tree debugging functions.                                                 *)
(* ------------------------------------------------------------------------- *)

(*BasicDebug
local
  let checkSizes tree =
      match tree with
        Empty -> 0
      | Tree (Node {size,left,right,...}) ->
        let
          let l = checkSizes left
          and r = checkSizes right

          let () = if l + 1 + r = size then () else raise Useful.Bug "wrong size"
        in
          size
        end;;

  let checkSorted compareKey x tree =
      match tree with
        Empty -> x
      | Tree (Node {left,key,right,...}) ->
        let
          let x = checkSorted compareKey x left

          let () =
              match x with
                None -> ()
              | Some k ->
                let c = compareKey k key in
                if c < 0 then ()
                else if c = 0 then raise Useful.Bug "duplicate keys"
                else raise Useful.Bug "unsorted"

          let x = Some key
        in
          checkSorted compareKey x right
        end;;

  let checkPriorities compareKey tree =
      match tree with
        Empty -> None
      | Tree node ->
        let
          let Node {left,right,...} = node

          let () =
              match checkPriorities compareKey left with
                None -> ()
              | Some lnode ->
                if not (lowerPriorityNode node lnode) then ()
                else raise Useful.Bug "left child has greater priority"

          let () =
              match checkPriorities compareKey right with
                None -> ()
              | Some rnode ->
                if not (lowerPriorityNode node rnode) then ()
                else raise Useful.Bug "right child has greater priority"
        in
          Some node
        end;;
in
  let treeCheckInvariants compareKey tree =
      let
        let _ = checkSizes tree

        let _ = checkSorted compareKey None tree

        let _ = checkPriorities compareKey tree
      in
        tree
      end
      handle Failure err -> raise (Useful.Bug err);;
end;;
*)

(* ------------------------------------------------------------------------- *)
(* Tree operations.                                                          *)
(* ------------------------------------------------------------------------- *)

let treeNew () = Empty;;

let nodeSize ({size = x}) = x;;

let treeSize tree =
    match tree with
      Empty -> 0
    | Tree x -> nodeSize x;;

let mkNode priority left key value right =
      let size = treeSize left + 1 + treeSize right
    in
        {size = size;
         priority = priority;
         left = left;
         key = key;
         value = value;
         right = right}
    ;;

let mkTree priority left key value right =
      let node = mkNode priority left key value right
    in
      Tree node
    ;;

(* ------------------------------------------------------------------------- *)
(* Extracting the left and right spines of a tree.                           *)
(* ------------------------------------------------------------------------- *)

let rec treeLeftSpine acc tree =
    match tree with
      Empty -> acc
    | Tree node -> nodeLeftSpine acc node

and nodeLeftSpine acc node =
      let {left=left} = node
    in
      treeLeftSpine (node :: acc) left
    ;;

let rec treeRightSpine acc tree =
    match tree with
      Empty -> acc
    | Tree node -> nodeRightSpine acc node

and nodeRightSpine acc node =
      let {right=right} = node
    in
      treeRightSpine (node :: acc) right
    ;;

(* ------------------------------------------------------------------------- *)
(* Singleton trees.                                                          *)
(* ------------------------------------------------------------------------- *)

let mkNodeSingleton priority key value =
      let size = 1
      and left = Empty
      and right = Empty
    in
        {size = size;
         priority = priority;
         left = left;
         key = key;
         value = value;
         right = right}
    ;;

let nodeSingleton (key,value) =
      let priority = randomPriority ()
    in
      mkNodeSingleton priority key value
    ;;

let treeSingleton key_value =
      let node = nodeSingleton key_value
    in
      Tree node
    ;;

(* ------------------------------------------------------------------------- *)
(* Appending two trees, where every element of the first tree is less than   *)
(* every element of the second tree.                                         *)
(* ------------------------------------------------------------------------- *)

let rec treeAppend tree1 tree2 =
    match tree1 with
      Empty -> tree2
    | Tree node1 ->
      match tree2 with
        Empty -> tree1
      | Tree node2 ->
        if lowerPriorityNode node1 node2 then
            let {priority=priority;left=left;key=key;value=value;right=right} = node2

            in let left = treeAppend tree1 left
          in
            mkTree priority left key value right
        else
            let {priority=priority;left=left;key=key;value=value;right=right} = node1

            in let right = treeAppend right tree2
          in
            mkTree priority left key value right
          ;;

(* ------------------------------------------------------------------------- *)
(* Appending two trees and a node, where every element of the first tree is  *)
(* less than the node, which in turn is less than every element of the       *)
(* second tree.                                                              *)
(* ------------------------------------------------------------------------- *)

let treeCombine left node right =
      let left_node = treeAppend left (Tree node)
    in
      treeAppend left_node right
    ;;

(* ------------------------------------------------------------------------- *)
(* Searching a tree for a value.                                             *)
(* ------------------------------------------------------------------------- *)

let rec treePeek compareKey pkey tree =
    match tree with
      Empty -> None
    | Tree node -> nodePeek compareKey pkey node

and nodePeek compareKey pkey node =
      let {left=left;key=key;value=value;right=right} = node
    in
      let c = compareKey pkey key in
      if c < 0 then treePeek compareKey pkey left
      else if c = 0 then Some value
      else treePeek compareKey pkey right
    ;;

(* ------------------------------------------------------------------------- *)
(* Tree paths.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Generating a path by searching a tree for a key/value pair *)

let rec treePeekPath compareKey pkey path tree =
    match tree with
      Empty -> (path,None)
    | Tree node -> nodePeekPath compareKey pkey path node

and nodePeekPath compareKey pkey path node =
      let {left=left;key=key;right=right} = node
    in
      let c = compareKey pkey key in
      if c < 0 then treePeekPath compareKey pkey ((true,node) :: path) left
      else if c = 0 then (path, Some node)
      else treePeekPath compareKey pkey ((false,node) :: path) right
    ;;

(* A path splits a tree into left/right components *)

let addSidePath ((wentLeft,node),(leftTree,rightTree)) =
      let {priority=priority;left=left;key=key;value=value;right=right} = node
    in
      if wentLeft then (leftTree, mkTree priority rightTree key value right)
      else (mkTree priority left key value leftTree, rightTree)
    ;;

let addSidesPath left_right = Mlist.foldl addSidePath left_right;;

let mkSidesPath path = addSidesPath (Empty,Empty) path;;

(* Updating the subtree at a path *)

  let updateTree ((wentLeft,node),tree) =
        let {priority=priority;left=left;key=key;value=value;right=right} = node
      in
        if wentLeft then mkTree priority tree key value right
        else mkTree priority left key value tree;;
  let updateTreePath tree = Mlist.foldl updateTree tree;;

(* Inserting a new node at a path position *)

let insertNodePath node =
      let rec insert left_right path =
          match path with
            [] ->
              let (left,right) = left_right
            in
              treeCombine left node right
          | ((_,snode) as step) :: rest ->
            if lowerPriorityNode snode node then
                let left_right = addSidePath (step,left_right)
              in
                insert left_right rest
            else
                let (left,right) = left_right

                in let tree = treeCombine left node right
              in
                updateTreePath tree path
    in
      insert (Empty,Empty)
    ;;

(* ------------------------------------------------------------------------- *)
(* Using a key to split a node into three components: the keys comparing     *)
(* less than the supplied key, an optional equal key, and the keys comparing *)
(* greater.                                                                  *)
(* ------------------------------------------------------------------------- *)

let nodePartition compareKey pkey node =
      let (path,pnode) = nodePeekPath compareKey pkey [] node
    in
      match pnode with
        None ->
          let (left,right) = mkSidesPath path
        in
          (left,None,right)
      | Some node ->
          let {left=left;key=key;value=value;right=right} = node

          in let (left,right) = addSidesPath (left,right) path
        in
          (left, Some (key,value), right)
    ;;

(* ------------------------------------------------------------------------- *)
(* Searching a tree for a key/value pair.                                    *)
(* ------------------------------------------------------------------------- *)

let rec treePeekKey compareKey pkey tree =
    match tree with
      Empty -> None
    | Tree node -> nodePeekKey compareKey pkey node

and nodePeekKey compareKey pkey node =
      let {left=left;key=key;value=value;right=right} = node
    in
      let c = compareKey pkey key in
      if c < 0 then treePeekKey compareKey pkey left
      else if c = 0 then Some (key,value)
      else treePeekKey compareKey pkey right
    ;;

(* ------------------------------------------------------------------------- *)
(* Inserting new key/values into the tree.                                   *)
(* ------------------------------------------------------------------------- *)

let treeInsert compareKey key_value tree =
      let (key,value) = key_value

      in let (path,inode) = treePeekPath compareKey key [] tree
    in
      match inode with
        None ->
          let node = nodeSingleton (key,value)
        in
          insertNodePath node path
      | Some node ->
          let {size=size;priority=priority;left=left;right=right} = node

          in let node =
                {size = size;
                 priority = priority;
                 left = left;
                 key = key;
                 value = value;
                 right = right}
        in
          updateTreePath (Tree node) path
    ;;

(* ------------------------------------------------------------------------- *)
(* Deleting key/value pairs: it raises an exception if the supplied key is   *)
(* not present.                                                              *)
(* ------------------------------------------------------------------------- *)

let rec treeDelete compareKey dkey tree =
    match tree with
      Empty -> raise (Useful.Bug "Map.delete: element not found")
    | Tree node -> nodeDelete compareKey dkey node

and nodeDelete compareKey dkey node =
      let {size=size;priority=priority;left=left;key=key;value=value;right=right} = node
    in
      let c = compareKey dkey key in
      if c < 0 then
          let size = size - 1
          and left = treeDelete compareKey dkey left

          in let node =
                {size = size;
                 priority = priority;
                 left = left;
                 key = key;
                 value = value;
                 right = right}
        in
          Tree node
      else if c = 0 then treeAppend left right
      else
          let size = size - 1
          and right = treeDelete compareKey dkey right

          in let node =
                {size = size;
                 priority = priority;
                 left = left;
                 key = key;
                 value = value;
                 right = right}
        in
          Tree node
    ;;

(* ------------------------------------------------------------------------- *)
(* Partial map is the basic operation for preserving tree structure.         *)
(* It applies its argument function to the elements *in order*.              *)
(* ------------------------------------------------------------------------- *)

let rec treeMapPartial f tree =
    match tree with
      Empty -> Empty
    | Tree node -> nodeMapPartial f node

and nodeMapPartial f ({priority=priority;left=left;key=key;value=value;right=right}) =
      let left = treeMapPartial f left
      and vo = f (key,value)
      and right = treeMapPartial f right
    in
      match vo with
        None -> treeAppend left right
      | Some value -> mkTree priority left key value right
    ;;

(* ------------------------------------------------------------------------- *)
(* Mapping tree values.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec treeMap f tree =
    match tree with
      Empty -> Empty
    | Tree node -> Tree (nodeMap f node)

and nodeMap f node =
      let {size=size;priority=priority;left=left;key=key;value=value;right=right} = node

      in let left = treeMap f left
      and value = f (key,value)
      and right = treeMap f right
    in
        {size = size;
         priority = priority;
         left = left;
         key = key;
         value = value;
         right = right}
    ;;

(* ------------------------------------------------------------------------- *)
(* Merge is the basic operation for joining two trees. Note that the merged  *)
(* key is always the one from the second map.                                *)
(* ------------------------------------------------------------------------- *)

let rec treeMerge compareKey f1 f2 fb tree1 tree2 =
    match tree1 with
      Empty -> treeMapPartial f2 tree2
    | Tree node1 ->
      match tree2 with
        Empty -> treeMapPartial f1 tree1
      | Tree node2 -> nodeMerge compareKey f1 f2 fb node1 node2

and nodeMerge compareKey f1 f2 fb node1 node2 =
      let {priority=priority;left=left;key=key;value=value;right=right} = node2

      in let (l,kvo,r) = nodePartition compareKey key node1

      in let left = treeMerge compareKey f1 f2 fb l left
      and right = treeMerge compareKey f1 f2 fb r right

      in let vo =
          match kvo with
            None -> f2 (key,value)
          | Some kv -> fb (kv,(key,value))
    in
      match vo with
        None -> treeAppend left right
      | Some value ->
          let node = mkNodeSingleton priority key value
        in
          treeCombine left node right
    ;;

(* ------------------------------------------------------------------------- *)
(* A union operation on trees.                                               *)
(* ------------------------------------------------------------------------- *)

let rec treeUnion compareKey f f2 tree1 tree2 =
    match tree1 with
      Empty -> tree2
    | Tree node1 ->
      match tree2 with
        Empty -> tree1
      | Tree node2 -> nodeUnion compareKey f f2 node1 node2

and nodeUnion compareKey f f2 node1 node2 =
    if node1 == node2 then nodeMapPartial f2 node1
    else
        let {priority=priority;left=left;key=key;value=value;right=right} = node2

        in let (l,kvo,r) = nodePartition compareKey key node1

        in let left = treeUnion compareKey f f2 l left
        and right = treeUnion compareKey f f2 r right

        in let vo =
            match kvo with
              None -> Some value
            | Some kv -> f (kv,(key,value))
      in
        match vo with
          None -> treeAppend left right
        | Some value ->
            let node = mkNodeSingleton priority key value
          in
            treeCombine left node right
      ;;

(* ------------------------------------------------------------------------- *)
(* An intersect operation on trees.                                          *)
(* ------------------------------------------------------------------------- *)

let rec treeIntersect compareKey f t1 t2 =
    match t1 with
      Empty -> Empty
    | Tree n1 ->
      match t2 with
        Empty -> Empty
      | Tree n2 -> nodeIntersect compareKey f n1 n2

and nodeIntersect compareKey f n1 n2 =
      let {priority=priority;left=left;key=key;value=value;right=right} = n2

      in let (l,kvo,r) = nodePartition compareKey key n1

      in let left = treeIntersect compareKey f l left
      and right = treeIntersect compareKey f r right

      in let vo =
          match kvo with
            None -> None
          | Some kv -> f (kv,(key,value))
    in
      match vo with
        None -> treeAppend left right
      | Some value -> mkTree priority left key value right
    ;;

(* ------------------------------------------------------------------------- *)
(* A union operation on trees which simply chooses the second value.         *)
(* ------------------------------------------------------------------------- *)

let rec treeUnionDomain compareKey tree1 tree2 =
    match tree1 with
      Empty -> tree2
    | Tree node1 ->
      match tree2 with
        Empty -> tree1
      | Tree node2 ->
        if node1 == node2 then tree2
        else nodeUnionDomain compareKey node1 node2

and nodeUnionDomain compareKey node1 node2 =
      let {priority=priority;left=left;key=key;value=value;right=right} = node2

      in let (l,_,r) = nodePartition compareKey key node1

      in let left = treeUnionDomain compareKey l left
      and right = treeUnionDomain compareKey r right

      in let node = mkNodeSingleton priority key value
    in
      treeCombine left node right
    ;;

(* ------------------------------------------------------------------------- *)
(* An intersect operation on trees which simply chooses the second value.    *)
(* ------------------------------------------------------------------------- *)

let rec treeIntersectDomain compareKey tree1 tree2 =
    match tree1 with
      Empty -> Empty
    | Tree node1 ->
      match tree2 with
        Empty -> Empty
      | Tree node2 ->
        if node1 == node2 then tree2
        else nodeIntersectDomain compareKey node1 node2

and nodeIntersectDomain compareKey node1 node2 =
      let {priority=priority;left=left;key=key;value=value;right=right} = node2

      in let (l,kvo,r) = nodePartition compareKey key node1

      in let left = treeIntersectDomain compareKey l left
      and right = treeIntersectDomain compareKey r right
    in
      if Option.is_some kvo then mkTree priority left key value right
      else treeAppend left right
    ;;

(* ------------------------------------------------------------------------- *)
(* A difference operation on trees.                                          *)
(* ------------------------------------------------------------------------- *)

let rec treeDifferenceDomain compareKey t1 t2 =
    match t1 with
      Empty -> Empty
    | Tree n1 ->
      match t2 with
        Empty -> t1
      | Tree n2 -> nodeDifferenceDomain compareKey n1 n2

and nodeDifferenceDomain compareKey n1 n2 =
    if n1 == n2 then Empty
    else
        let {priority=priority;left=left;key=key;value=value;right=right} = n1

        in let (l,kvo,r) = nodePartition compareKey key n2

        in let left = treeDifferenceDomain compareKey left l
        and right = treeDifferenceDomain compareKey right r
      in
        if Option.is_some kvo then treeAppend left right
        else mkTree priority left key value right
      ;;

(* ------------------------------------------------------------------------- *)
(* A subset operation on trees.                                              *)
(* ------------------------------------------------------------------------- *)

let rec treeSubsetDomain compareKey tree1 tree2 =
    match tree1 with
      Empty -> true
    | Tree node1 ->
      match tree2 with
        Empty -> false
      | Tree node2 -> nodeSubsetDomain compareKey node1 node2

and nodeSubsetDomain compareKey node1 node2 =
    node1 == node2 ||
      let {size=size;left=left;key=key;right=right} = node1
    in
      size <= nodeSize node2 &&
        let (l,kvo,r) = nodePartition compareKey key node2
      in
        Option.is_some kvo &&
        treeSubsetDomain compareKey left l &&
        treeSubsetDomain compareKey right r
    ;;

(* ------------------------------------------------------------------------- *)
(* Picking an arbitrary key/value pair from a tree.                          *)
(* ------------------------------------------------------------------------- *)

let rec nodePick node =
      let {key=key;value=value} = node
    in
      (key,value)
    ;;

let treePick tree =
    match tree with
      Empty -> raise (Useful.Bug "Map.treePick")
    | Tree node -> nodePick node;;

(* ------------------------------------------------------------------------- *)
(* Removing an arbitrary key/value pair from a tree.                         *)
(* ------------------------------------------------------------------------- *)

let rec nodeDeletePick node =
      let {left=left;key=key;value=value;right=right} = node
    in
      ((key,value), treeAppend left right)
    ;;

let treeDeletePick tree =
    match tree with
      Empty -> raise (Useful.Bug "Map.treeDeletePick")
    | Tree node -> nodeDeletePick node;;

(* ------------------------------------------------------------------------- *)
(* Finding the nth smallest key/value (counting from 0).                     *)
(* ------------------------------------------------------------------------- *)

let rec treeNth n tree =
    match tree with
      Empty -> raise (Useful.Bug "Map.treeNth")
    | Tree node -> nodeNth n node

and nodeNth n node =
      let {left=left;key=key;value=value;right=right} = node

      in let k = treeSize left
    in
      if n = k then (key,value)
      else if n < k then treeNth n left
      else treeNth (n - (k + 1)) right
    ;;

(* ------------------------------------------------------------------------- *)
(* Removing the nth smallest key/value (counting from 0).                    *)
(* ------------------------------------------------------------------------- *)

let rec treeDeleteNth n tree =
    match tree with
      Empty -> raise (Useful.Bug "Map.treeDeleteNth")
    | Tree node -> nodeDeleteNth n node

and nodeDeleteNth n node =
      let {size=size;priority=priority;left=left;key=key;value=value;right=right} = node

      in let k = treeSize left
    in
      if n = k then ((key,value), treeAppend left right)
      else if n < k then
          let (key_value,left) = treeDeleteNth n left

          in let size = size - 1

          in let node =
                {size = size;
                 priority = priority;
                 left = left;
                 key = key;
                 value = value;
                 right = right}
        in
          (key_value, Tree node)
      else
          let n = n - (k + 1)

          in let (key_value,right) = treeDeleteNth n right

          in let size = size - 1

          in let node =
                {size = size;
                 priority = priority;
                 left = left;
                 key = key;
                 value = value;
                 right = right}
        in
          (key_value, Tree node)
    ;;

(* ------------------------------------------------------------------------- *)
(* Iterators.                                                                *)
(* ------------------------------------------------------------------------- *)

type ('key,'value) iterator =
    Left_to_right_iterator of
      ('key * 'value) * ('key,'value) tree * ('key,'value) node list
  | Right_to_left_iterator of
      ('key * 'value) * ('key,'value) tree * ('key,'value) node list;;

let fromSpineLeftToRightIterator nodes =
    match nodes with
      [] -> None
    | {key=key;value=value;right=right} :: nodes ->
      Some (Left_to_right_iterator ((key,value),right,nodes));;

let fromSpineRightToLeftIterator nodes =
    match nodes with
      [] -> None
    | {key=key;value=value;left=left} :: nodes ->
      Some (Right_to_left_iterator ((key,value),left,nodes));;

let addLeftToRightIterator nodes tree = fromSpineLeftToRightIterator (treeLeftSpine nodes tree);;

let addRightToLeftIterator nodes tree = fromSpineRightToLeftIterator (treeRightSpine nodes tree);;

let treeMkIterator tree = addLeftToRightIterator [] tree;;

let treeMkRevIterator tree = addRightToLeftIterator [] tree;;

let readIterator iter =
    match iter with
      Left_to_right_iterator (key_value,_,_) -> key_value
    | Right_to_left_iterator (key_value,_,_) -> key_value;;

let advanceIterator iter =
    match iter with
      Left_to_right_iterator (_,tree,nodes) -> addLeftToRightIterator nodes tree
    | Right_to_left_iterator (_,tree,nodes) -> addRightToLeftIterator nodes tree;;

let rec foldIterator f acc io =
    match io with
      None -> acc
    | Some iter ->
        let (key,value) = readIterator iter
      in
        foldIterator f (f (key,value,acc)) (advanceIterator iter)
      ;;

let rec findIterator pred io =
    match io with
      None -> None
    | Some iter ->
        let key_value = readIterator iter
      in
        if pred key_value then Some key_value
        else findIterator pred (advanceIterator iter)
      ;;

let rec firstIterator f io =
    match io with
      None -> None
    | Some iter ->
        let key_value = readIterator iter
      in
        match f key_value with
          None -> firstIterator f (advanceIterator iter)
        | s -> s
      ;;

let rec compareIterator compareKey compareValue io1 io2 =
    match (io1,io2) with
      (None,None) -> 0
    | (None, Some _) -> -1
    | (Some _, None) -> 1
    | (Some i1, Some i2) ->
        let (k1,v1) = readIterator i1
        and (k2,v2) = readIterator i2
      in
        let c = compareKey k1 k2 in
        if c <> 0 then c
        else
          let c = compareValue v1 v2 in
          if c <> 0 then c
          else
               let io1 = advanceIterator i1
               and io2 = advanceIterator i2
             in
               compareIterator compareKey compareValue io1 io2
      ;;

let rec equalIterator equalKey equalValue io1 io2 =
    match (io1,io2) with
      (None,None) -> true
    | (None, Some _) -> false
    | (Some _, None) -> false
    | (Some i1, Some i2) ->
        let (k1,v1) = readIterator i1
        and (k2,v2) = readIterator i2
      in
        equalKey k1 k2 &&
        equalValue v1 v2 &&
          let io1 = advanceIterator i1
          and io2 = advanceIterator i2
        in
          equalIterator equalKey equalValue io1 io2
      ;;

(* ------------------------------------------------------------------------- *)
(* A type of finite maps.                                                    *)
(* ------------------------------------------------------------------------- *)

type ('key,'value) map =
    Map of ('key -> 'key -> int) * ('key,'value) tree;;

(* ------------------------------------------------------------------------- *)
(* Map debugging functions.                                                  *)
(* ------------------------------------------------------------------------- *)

(*BasicDebug
let checkInvariants s m =
    let
      let Map (compareKey,tree) = m

      let _ = treeCheckInvariants compareKey tree
    in
      m
    end
    handle Useful.Bug bug -> raise (Useful.Bug (s ^ "\n" ^ "Map.checkInvariants: " ^ bug));;
*)

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

let newMap compareKey =
      let tree = treeNew ()
    in
      Map (compareKey,tree)
    ;;

let singleton compareKey key_value =
      let tree = treeSingleton key_value
    in
      Map (compareKey,tree)
    ;;

(* ------------------------------------------------------------------------- *)
(* Map size.                                                                 *)
(* ------------------------------------------------------------------------- *)

let size (Map (_,tree)) = treeSize tree;;

let null m = size m = 0;;

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

let peekKey (Map (compareKey,tree)) key = treePeekKey compareKey key tree;;

let peek (Map (compareKey,tree)) key = treePeek compareKey key tree;;

let inDomain key m = Option.is_some (peek m key);;

let get m key =
    match peek m key with
      None -> failwith "Map.get: element not found"
    | Some value -> value;;

let pick (Map (_,tree)) = treePick tree;;

let nth (Map (_,tree)) n = treeNth n tree;;

let random m =
      let n = size m
    in
      if n = 0 then raise (Useful.Bug "Map.random: empty")
      else nth m (Random.int n)
    ;;

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

let insert (Map (compareKey,tree)) key_value =
      let tree = treeInsert compareKey key_value tree
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let insert = fun m -> fun kv ->
    checkInvariants "Map.insert: result"
      (insert (checkInvariants "Map.insert: input" m) kv);;
*)

let insertList m =
      let ins (key_value,acc) = insert acc key_value
    in
      Mlist.foldl ins m
    ;;

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

let delete (Map (compareKey,tree)) dkey =
      let tree = treeDelete compareKey dkey tree
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let delete = fun m -> fun k ->
    checkInvariants "Map.delete: result"
      (delete (checkInvariants "Map.delete: input" m) k);;
*)

let remove m key = if inDomain key m then delete m key else m;;

let deletePick (Map (compareKey,tree)) =
      let (key_value,tree) = treeDeletePick tree
    in
      (key_value, Map (compareKey,tree))
    ;;

(*BasicDebug
let deletePick = fun m ->
    let
      let (kv,m) = deletePick (checkInvariants "Map.deletePick: input" m)
    in
      (kv, checkInvariants "Map.deletePick: result" m)
    end;;
*)

let deleteNth (Map (compareKey,tree)) n =
      let (key_value,tree) = treeDeleteNth n tree
    in
      (key_value, Map (compareKey,tree))
    ;;

(*BasicDebug
let deleteNth = fun m -> fun n ->
    let
      let (kv,m) = deleteNth (checkInvariants "Map.deleteNth: input" m) n
    in
      (kv, checkInvariants "Map.deleteNth: result" m)
    end;;
*)

let deleteRandom m =
      let n = size m
    in
      if n = 0 then raise (Useful.Bug "Map.deleteRandom: empty")
      else deleteNth m (Random.int n)
    ;;

(* ------------------------------------------------------------------------- *)
(* Joining (all join operations prefer keys in the second map).              *)
(* ------------------------------------------------------------------------- *)

let merge (first,second,both) (Map (compareKey,tree1)) (Map (_,tree2)) =
      let tree = treeMerge compareKey first second both tree1 tree2
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let merge = fun f -> fun m1 -> fun m2 ->
    checkInvariants "Map.merge: result"
      (merge f
         (checkInvariants "Map.merge: input 1" m1)
         (checkInvariants "Map.merge: input 2" m2));;
*)

let union f (Map (compareKey,tree1)) (Map (_,tree2)) =
      let f2 kv = f (kv,kv)

      in let tree = treeUnion compareKey f f2 tree1 tree2
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let union = fun f -> fun m1 -> fun m2 ->
    checkInvariants "Map.union: result"
      (union f
         (checkInvariants "Map.union: input 1" m1)
         (checkInvariants "Map.union: input 2" m2));;
*)

let intersect f (Map (compareKey,tree1)) (Map (_,tree2)) =
      let tree = treeIntersect compareKey f tree1 tree2
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let intersect = fun f -> fun m1 -> fun m2 ->
    checkInvariants "Map.intersect: result"
      (intersect f
         (checkInvariants "Map.intersect: input 1" m1)
         (checkInvariants "Map.intersect: input 2" m2));;
*)

(* ------------------------------------------------------------------------- *)
(* Iterators over maps.                                                      *)
(* ------------------------------------------------------------------------- *)

let mkIterator (Map (_,tree)) = treeMkIterator tree;;

let mkRevIterator (Map (_,tree)) = treeMkRevIterator tree;;

(* ------------------------------------------------------------------------- *)
(* Mapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

let mapPartial f (Map (compareKey,tree)) =
      let tree = treeMapPartial f tree
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let mapPartial = fun f -> fun m ->
    checkInvariants "Map.mapPartial: result"
      (mapPartial f (checkInvariants "Map.mapPartial: input" m));;
*)

let map f (Map (compareKey,tree)) =
      let tree = treeMap f tree
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let map = fun f -> fun m ->
    checkInvariants "Map.map: result"
      (map f (checkInvariants "Map.map: input" m));;
*)

let transform f = map (fun (_,value) -> f value);;

let filter pred =
      let f ((_,value) as key_value) =
          if pred key_value then Some value else None
    in
      mapPartial f
    ;;

let partition p =
      let np x = not (p x)
    in
      fun m -> (filter p m, filter np m)
    ;;

let foldl f b m = foldIterator f b (mkIterator m);;

let foldr f b m = foldIterator f b (mkRevIterator m);;

let app f m = foldl (fun (key,value,()) -> f (key,value)) () m;;

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

let findl p m = findIterator p (mkIterator m);;

let findr p m = findIterator p (mkRevIterator m);;

let firstl f m = firstIterator f (mkIterator m);;

let firstr f m = firstIterator f (mkRevIterator m);;

let exists p m = Option.is_some (findl p m);;

let all p =
      let np x = not (p x)
    in
      fun m -> not (exists np m)
    ;;

let count pred =
      let f (k,v,acc) = if pred (k,v) then acc + 1 else acc
    in
      foldl f 0
    ;;

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

let compare compareValue m1 m2 =
    if m1 == m2 then 0
    else
      let c = Useful.intCompare (size m1) (size m2) in
      if c <> 0 then c
      else
          let Map (compareKey,_) = m1

          in let io1 = mkIterator m1
          and io2 = mkIterator m2
        in
          compareIterator compareKey compareValue io1 io2
    ;;

let equal equalValue m1 m2 =
    m1 == m2 ||
    (size m1 = size m2 &&
       let Map (compareKey,_) = m1

       in let io1 = mkIterator m1
       and io2 = mkIterator m2
     in
       equalIterator (equalKey compareKey) equalValue io1 io2
     );;

(* ------------------------------------------------------------------------- *)
(* Set operations on the domain.                                             *)
(* ------------------------------------------------------------------------- *)

let unionDomain (Map (compareKey,tree1)) (Map (_,tree2)) =
      let tree = treeUnionDomain compareKey tree1 tree2
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let unionDomain = fun m1 -> fun m2 ->
    checkInvariants "Map.unionDomain: result"
      (unionDomain
         (checkInvariants "Map.unionDomain: input 1" m1)
         (checkInvariants "Map.unionDomain: input 2" m2));;
*)

  let uncurriedUnionDomain (m,acc) = unionDomain acc m;;
  let unionListDomain ms =
      match ms with
        [] -> raise (Useful.Bug "Map.unionListDomain: no sets")
      | m :: ms -> Mlist.foldl uncurriedUnionDomain m ms;;

let intersectDomain (Map (compareKey,tree1)) (Map (_,tree2)) =
      let tree = treeIntersectDomain compareKey tree1 tree2
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let intersectDomain = fun m1 -> fun m2 ->
    checkInvariants "Map.intersectDomain: result"
      (intersectDomain
         (checkInvariants "Map.intersectDomain: input 1" m1)
         (checkInvariants "Map.intersectDomain: input 2" m2));;
*)

  let uncurriedIntersectDomain (m,acc) = intersectDomain acc m;;
  let intersectListDomain ms =
      match ms with
        [] -> raise (Useful.Bug "Map.intersectListDomain: no sets")
      | m :: ms -> Mlist.foldl uncurriedIntersectDomain m ms;;

let differenceDomain (Map (compareKey,tree1)) (Map (_,tree2)) =
      let tree = treeDifferenceDomain compareKey tree1 tree2
    in
      Map (compareKey,tree)
    ;;

(*BasicDebug
let differenceDomain = fun m1 -> fun m2 ->
    checkInvariants "Map.differenceDomain: result"
      (differenceDomain
         (checkInvariants "Map.differenceDomain: input 1" m1)
         (checkInvariants "Map.differenceDomain: input 2" m2));;
*)

let symmetricDifferenceDomain m1 m2 =
    unionDomain (differenceDomain m1 m2) (differenceDomain m2 m1);;

let equalDomain m1 m2 = equal (K (K true)) m1 m2;;

let subsetDomain (Map (compareKey,tree1)) (Map (_,tree2)) =
    treeSubsetDomain compareKey tree1 tree2;;

let disjointDomain m1 m2 = null (intersectDomain m1 m2);;

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

let keys m = foldr (fun (key,_,l) -> key :: l) [] m;;

let values m = foldr (fun (_,value,l) -> value :: l) [] m;;

let toList m = foldr (fun (key,value,l) -> (key,value) :: l) [] m;;

let fromList compareKey l =
      let m = newMap compareKey
    in
      insertList m l
    ;;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

let toString m = "<" ^ (if null m then "" else string_of_int (size m)) ^ ">";;

end

(* ------------------------------------------------------------------------- *)
(* More map and set modules to support Metis.                                *)
(* ------------------------------------------------------------------------- *)

(* ========================================================================= *)
(* FINITE SETS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* ========================================================================= *)

module Pset = struct

(* ------------------------------------------------------------------------- *)
(* A type of finite sets.                                                    *)
(* ------------------------------------------------------------------------- *)

type ('elt,'a) map = ('elt,'a) Pmap.map;;

type 'elt set = Set of ('elt,unit) map;;

(* ------------------------------------------------------------------------- *)
(* Converting to and from maps.                                              *)
(* ------------------------------------------------------------------------- *)

let dest (Set m) = m;;

let mapPartial f =
      let mf (elt,()) = f elt
    in
      fun (Set m) -> Pmap.mapPartial mf m
    ;;

let map f =
      let mf (elt,()) = f elt
    in
      fun (Set m) -> Pmap.map mf m
    ;;

let domain m = Set (Pmap.transform (fun _ -> ()) m);;

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

let empty cmp = Set (Pmap.newMap cmp);;

let singleton cmp elt = Set (Pmap.singleton cmp (elt,()));;

(* ------------------------------------------------------------------------- *)
(* Set size.                                                                 *)
(* ------------------------------------------------------------------------- *)

let null (Set m) = Pmap.null m;;

let size (Set m) = Pmap.size m;;

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

let peek (Set m) elt =
    match Pmap.peekKey m elt with
      Some (elt,()) -> Some elt
    | None -> None;;

let member elt (Set m) = Pmap.inDomain elt m;;

let pick (Set m) =
      let (elt,_) = Pmap.pick m
    in
      elt
    ;;

let nth (Set m) n =
      let (elt,_) = Pmap.nth m n
    in
      elt
    ;;

let random (Set m) =
      let (elt,_) = Pmap.random m
    in
      elt
    ;;

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

let add (Set m) elt =
      let m = Pmap.insert m (elt,())
    in
      Set m
    ;;

  let uncurriedAdd (elt,set) = add set elt;;
  let addList set = Mlist.foldl uncurriedAdd set;;

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

let delete (Set m) elt =
      let m = Pmap.delete m elt
    in
      Set m
    ;;

let remove (Set m) elt =
      let m = Pmap.remove m elt
    in
      Set m
    ;;

let deletePick (Set m) =
      let ((elt,()),m) = Pmap.deletePick m
    in
      (elt, Set m)
    ;;

let deleteNth (Set m) n =
      let ((elt,()),m) = Pmap.deleteNth m n
    in
      (elt, Set m)
    ;;

let deleteRandom (Set m) =
      let ((elt,()),m) = Pmap.deleteRandom m
    in
      (elt, Set m)
    ;;

(* ------------------------------------------------------------------------- *)
(* Joining.                                                                  *)
(* ------------------------------------------------------------------------- *)

let union (Set m1) (Set m2) = Set (Pmap.unionDomain m1 m2);;

let unionList sets =
      let ms = List.map dest sets
    in
      Set (Pmap.unionListDomain ms)
    ;;

let intersect (Set m1) (Set m2) = Set (Pmap.intersectDomain m1 m2);;

let intersectList sets =
      let ms = List.map dest sets
    in
      Set (Pmap.intersectListDomain ms)
    ;;

let difference (Set m1) (Set m2) =
    Set (Pmap.differenceDomain m1 m2);;

let symmetricDifference (Set m1) (Set m2) =
    Set (Pmap.symmetricDifferenceDomain m1 m2);;

(* ------------------------------------------------------------------------- *)
(* Pmapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

let filter pred =
      let mpred (elt,()) = pred elt
    in
      fun (Set m) -> Set (Pmap.filter mpred m)
    ;;

let partition pred =
      let mpred (elt,()) = pred elt
    in
      fun (Set m) ->
           let (m1,m2) = Pmap.partition mpred m
         in
           (Set m1, Set m2)
    ;;

let app f =
      let mf (elt,()) = f elt
    in
      fun (Set m) -> Pmap.app mf m
    ;;

let foldl f =
      let mf (elt,(),acc) = f (elt,acc)
    in
      fun acc -> fun (Set m) -> Pmap.foldl mf acc m
    ;;

let foldr f =
      let mf (elt,(),acc) = f (elt,acc)
    in
      fun acc -> fun (Set m) -> Pmap.foldr mf acc m
    ;;

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

let findl p =
      let mp (elt,()) = p elt
    in
      fun (Set m) ->
         match Pmap.findl mp m with
           Some (elt,()) -> Some elt
         | None -> None
    ;;

let findr p =
      let mp (elt,()) = p elt
    in
      fun (Set m) ->
         match Pmap.findr mp m with
           Some (elt,()) -> Some elt
         | None -> None
    ;;

let firstl f =
      let mf (elt,()) = f elt
    in
      fun (Set m) -> Pmap.firstl mf m
    ;;

let firstr f =
      let mf (elt,()) = f elt
    in
      fun (Set m) -> Pmap.firstr mf m
    ;;

let exists p =
      let mp (elt,()) = p elt
    in
      fun (Set m) -> Pmap.exists mp m
    ;;

let all p =
      let mp (elt,()) = p elt
    in
      fun (Set m) -> Pmap.all mp m
    ;;

let count p =
      let mp (elt,()) = p elt
    in
      fun (Set m) -> Pmap.count mp m
    ;;

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

let compareValue () () = 0;;

let equalValue () () = true;;

let compare (Set m1) (Set m2) = Pmap.compare compareValue m1 m2;;

let equal (Set m1) (Set m2) = Pmap.equal equalValue m1 m2;;

let subset (Set m1) (Set m2) = Pmap.subsetDomain m1 m2;;

let disjoint (Set m1) (Set m2) = Pmap.disjointDomain m1 m2;;

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

let transform f =
      let inc (x,l) = f x :: l
    in
      foldr inc []
    ;;

let toList (Set m) = Pmap.keys m;;

let fromList cmp elts = addList (empty cmp) elts;;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

let toString set =
    "{" ^ (if null set then "" else string_of_int (size set)) ^ "}";;

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type 'elt iterator = ('elt,unit) Pmap.iterator;;

let mkIterator (Set m) = Pmap.mkIterator m;;

let mkRevIterator (Set m) = Pmap.mkRevIterator m;;

let readIterator iter =
      let (elt,()) = Pmap.readIterator iter
    in
      elt
    ;;

let advanceIterator iter = Pmap.advanceIterator iter;;


end

(* ========================================================================= *)
(* More map and set types for Metis.                                         *)
(* ========================================================================= *)

module Mmap = struct

module type Ordered =
sig
  type t
  val compare : t -> t -> int
end

module Make (Ord : Ordered) =
struct
  module Ma = Map.Make (Ord)

  type +'a map = 'a Ma.t

  let newMap () = Ma.empty;;
  let null = Ma.is_empty;;
  let singleton (k, x) = Ma.singleton k x;;
  let size = Ma.cardinal;;
  let get m k = try Ma.find k m with Not_found -> failwith "Mmap.get: element not found";;
  let peek m k = try Some (Ma.find k m) with Not_found -> None;;
  let insert m (k, v) = Ma.add k v m;;
  let toList = Ma.bindings;;
  let fromList l = List.fold_right (fun (v,tm) -> Ma.add v tm) l Ma.empty;;
  let foldl f b m = List.fold_left (fun s (v, tm) -> f (v, tm, s)) b (Ma.bindings m);;
  let foldr = foldl;;
  let filter f = Ma.filter (fun x y -> f (x, y));;
  let inDomain = Ma.mem;;
  let union f m1 m2 =
    let f' k = function
        (Some x, Some y) -> f ((k, x), (k, y))
      | (Some x, None) -> Some x
      | (None, Some y) -> Some y
      | (None, None) -> None
    in Ma.merge (fun k x y -> f' k (x, y)) m1 m2
  let delete m k = Ma.remove k m
  let mapPartial f m = Ma.fold (fun k x acc -> match f (k, x) with Some y -> Ma.add k y acc | None -> acc) m Ma.empty;;
  let transform = Ma.map;;
  let exists f = Ma.exists (fun k m -> f (k,m));;
end
end


module Intmap = struct

module Ordered = struct type t = int let compare = compare end

include Mmap.Make (Ordered);;

end

module Stringmap = struct

module Ordered = struct type t = string let compare = compare end

include Mmap.Make (Ordered);;

end

module Mset = struct

module type Ordered =
sig
  type t
  val compare : t -> t -> int
end

module Make (Ord : Ordered) =
struct
  module Se = Set.Make (Ord)

  type set = Se.t;;
  let compare = Se.compare;;

  let add s x = Se.add x s;;
  let foldr f a s = Se.fold (fun x acc -> f (x,acc)) s a;;
  let foldl = foldr;;
  let member = Se.mem;;
  let empty = Se.empty;;
  let union = Se.union;;
  let difference = Se.diff;;
  let toList = Se.elements;;
  let singleton = Se.singleton;;
  let null = Se.is_empty;;
  let size = Se.cardinal;;
  let pick = Se.choose;;
  let equal = Se.equal;;
  let exists = Se.exists;;
  let fromList l = List.fold_right Se.add l Se.empty;;
  let delete s x = Se.remove x s;;
  let subset = Se.subset;;
  let intersect = Se.inter;;
  let intersectList = function
      [] -> Se.empty
    | (s::ss) -> List.fold_right Se.inter ss s
  let findl p s =
    let go x = function
        (Some _) as s -> s
      | None -> if p x then Some x else None
    in Se.fold go s None;;
  let firstl f s =
    let go x = function
        (Some _) as s -> s
      | None -> f x
     in Se.fold go s None;;
  let transform f s = Se.fold (fun x acc -> f x :: acc) s []
  let all = Se.for_all;;
  let count p s = Se.fold (fun x c -> if p x then c+1 else c) s 0
end

end


module Intset = struct

module Ordered = struct type t = int let compare = compare end

include Mset.Make (Ordered);;

end


(* ========================================================================= *)
(* A HEAP DATATYPE FOR ML                                                    *)
(* ========================================================================= *)

module Heap = struct

(* Leftist heaps as in Purely Functional Data Structures, by Chris Okasaki *)

exception Empty;;

type 'a node = Em | Tr of int * 'a * 'a node * 'a node;;

type 'a heap = Heap of ('a -> 'a -> int) * int * 'a node;;

let rank = function
    Em -> 0
  | (Tr (r,_,_,_)) -> r;;

let makeT (x,a,b) =
  if rank a >= rank b then Tr (rank b + 1, x, a, b) else Tr (rank a + 1, x, b, a);;

let merge cmp =
      let rec mrg = function
          (h,Em) -> h
        | (Em,h) -> h
        | (Tr (_,x,a1,b1) as h1, (Tr (_,y,a2,b2) as h2)) ->
          if cmp x y > 0 then makeT (y, a2, mrg (h1,b2))
          else makeT (x, a1, mrg (b1,h2))
    in
      mrg
    ;;

let newHeap cmp = Heap (cmp,0,Em);;

let add (Heap (f,n,a)) x = Heap (f, n + 1, merge f (Tr (1,x,Em,Em), a));;

let size (Heap (_, n, _)) = n;;

let null h = size h = 0;;

let top = function
    (Heap (_,_,Em)) -> raise Empty
  | (Heap (_, _, Tr (_,x,_,_))) -> x;;

let remove = function
    (Heap (_,_,Em)) -> raise Empty
  | (Heap (f, n, Tr (_,x,a,b))) -> (x, Heap (f, n - 1, merge f (a,b)));;

let app f =
      let rec ap = function
          [] -> ()
        | (Em :: rest) -> ap rest
        | (Tr (_,d,a,b) :: rest) -> (f d; ap (a :: b :: rest))
    in
      function Heap (_,_,a) -> ap [a]
    ;;

let rec toList h =
    if null h then []
    else
        let (x,h) = remove h
      in
        x :: toList h
      ;;

let toString h =
    "Heap[" ^ (if null h then "" else string_of_int (size h)) ^ "]";;

end

(* ========================================================================= *)
(* NAMES                                                                     *)
(* ========================================================================= *)

module Name = struct

(* ------------------------------------------------------------------------- *)
(* A type of names.                                                          *)
(* ------------------------------------------------------------------------- *)

type name = string;;

(* ------------------------------------------------------------------------- *)
(* A total ordering.                                                         *)
(* ------------------------------------------------------------------------- *)

let compare = (compare : name -> name -> int);;

let equal n1 n2 = n1 = n2;;

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

let prefix  = "_";;
let numName i = Useful.mkPrefix prefix (string_of_int i);;
let newName () = numName (Useful.newInt ());;
let newNames n = List.map numName (Useful.newInts n);;

let variantPrime avoid =
    let rec variant n = if avoid n then variant (n ^ "'") else n
    in variant;;

let variantNum avoid n =
  let isDigitOrPrime c = c = '\'' || Useful.isDigit c
  in if not (avoid n) then n
      else
        let n = Useful.stripSuffix isDigitOrPrime n in
        let rec variant i =
          let n_i = n ^ string_of_int i
          in if avoid n_i then variant (i + 1) else n_i
        in variant 0
;;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

let toString s : string = s;;

let fromString s : name = s;;

module Ordered =
struct type t = name let compare = compare end

module Map = Mmap.Make (Ordered);;
module Set = Mset.Make (Ordered);;

end

(* ========================================================================= *)
(* NAME/ARITY PAIRS                                                          *)
(* ========================================================================= *)

module Name_arity = struct

(* ------------------------------------------------------------------------- *)
(* A type of name/arity pairs.                                               *)
(* ------------------------------------------------------------------------- *)

type nameArity = Name.name * int;;

let name ((n,_) : nameArity) = n;;

let arity ((_,i) : nameArity) = i;;

(* ------------------------------------------------------------------------- *)
(* Testing for different arities.                                            *)
(* ------------------------------------------------------------------------- *)

let nary i n_i = arity n_i = i;;

let nullary = nary 0
and unary = nary 1
and binary = nary 2
and ternary = nary 3;;

(* ------------------------------------------------------------------------- *)
(* A total ordering.                                                         *)
(* ------------------------------------------------------------------------- *)

let compare (n1,i1) (n2,i2) =
    let c = Name.compare n1 n2 in
    if c <> 0 then c else Useful.intCompare i1 i2;;

let equal (n1,i1) (n2,i2) = i1 = i2 && Name.equal n1 n2;;


module Ordered =
struct type t = nameArity let compare = compare end

module Map = struct
  include Mmap.Make (Ordered)

  let compose m1 m2 =
      let pk ((_,a),n) = peek m2 (n,a)
    in
      mapPartial pk m1
    ;;
end

module Set = struct
  include Mset.Make (Ordered)

  let allNullary = all nullary;
end

end

(* ========================================================================= *)
(* FIRST ORDER LOGIC TERMS                                                   *)
(* ========================================================================= *)

module Term = struct

(* ------------------------------------------------------------------------- *)
(* A type of first order logic terms.                                        *)
(* ------------------------------------------------------------------------- *)

type var = Name.name;;

type functionName = Name.name;;

type function_t = functionName * int;;

type const = functionName;;

type term =
    Var of Name.name
  | Fn of (Name.name * term list);;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Variables *)

let destVar = function
    (Var v) -> v
  | (Fn _) -> failwith "destVar";;

let isVar = can destVar;;

let equalVar v = function
   (Var v') -> Name.equal v v'
  | _       -> false;;

(* Functions *)

let destFn = function
    (Fn f) -> f
  | (Var _) -> failwith "destFn";;

let isFn = can destFn;;

let fnName tm = fst (destFn tm);;

let fnArguments tm = snd (destFn tm);;

let fnArity tm = List.length (fnArguments tm);;

let fnFunction tm = (fnName tm, fnArity tm);;

let functions tm =
  let rec letc fs = function
      [] -> fs
    | (Var _ :: tms) -> letc fs tms
    | (Fn (n,l) :: tms) -> letc (Name_arity.Set.add fs (n, List.length l)) (l @ tms)

  in letc Name_arity.Set.empty [tm];;

let functionNames tm =
  let rec letc fs = function
      [] -> fs
    | (Var _ :: tms) -> letc fs tms
    | (Fn (n,l) :: tms) -> letc (Name.Set.add fs n) (l @ tms)
  in letc Name.Set.empty [tm];;

(* Constants *)

let mkConst c = (Fn (c, []));;

let destConst = function
    (Fn (c, [])) -> c
  | _ -> failwith "destConst";;

let isConst = can destConst;;

(* Binary functions *)

let mkBinop f (a,b) = Fn (f,[a;b]);;

let destBinop f = function
  (Fn (x,[a;b])) ->
    if Name.equal x f then (a,b) else failwith "Term.destBinop: wrong binop"
  | _ -> failwith "Term.destBinop: not a binop";;

let isBinop f = can (destBinop f);;

(* ------------------------------------------------------------------------- *)
(* The size of a term in symbols.                                            *)
(* ------------------------------------------------------------------------- *)

let vAR_SYMBOLS = 1;;

let fN_SYMBOLS = 1;;

let symbols tm =
  let rec sz n = function
      [] -> n
    | (Var _ :: tms) -> sz (n + vAR_SYMBOLS) tms
    | (Fn (letc,args) :: tms) -> sz (n + fN_SYMBOLS) (args @ tms)
  in sz 0 [tm];;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for terms.                                    *)
(* ------------------------------------------------------------------------- *)

let compare tm1 tm2 =
  let rec cmp = function
      ([], []) -> 0
    | (tm1 :: tms1, tm2 :: tms2) ->
        if tm1 == tm2 then cmp (tms1, tms2)
        else
          (match (tm1,tm2) with
            (Var v1, Var v2) ->
              let c = Name.compare v1 v2 in
              if c <> 0 then c else cmp (tms1, tms2)
          | (Var _, Fn _) -> -1
          | (Fn _, Var _) -> 1
          | (Fn (f1,a1), Fn (f2,a2)) ->
              let c = Name.compare f1 f2 in
              if c <> 0 then c
              else
                let c = Useful.intCompare (List.length a1) (List.length a2) in
                if c <> 0 then c else cmp (a1 @ tms1, a2 @ tms2))
    | _ -> raise (Useful.Bug "Term.compare")
  in cmp ([tm1], [tm2]);;

let equal tm1 tm2 = compare tm1 tm2 = 0;;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

type path = int list;;

let rec subterm' = function
    (tm, []) -> tm
  | (Var _, _ :: _) -> failwith "Term.subterm: Var"
  | (Fn (_,tms), h :: t) ->
    if h >= List.length tms then failwith "Term.replace: Fn"
    else subterm' (List.nth tms h, t);;
let subterm s t = subterm' (s, t);;

let subterms tm =
  let rec subtms = function
      ([], acc) -> acc
    | ((path,tm) :: rest, acc) ->
        let f (n,arg) = (n :: path, arg)
        and acc = (List.rev path, tm) :: acc
        in match tm with
          Var _ -> subtms (rest, acc)
        | Fn (_,args) -> subtms ((List.map f (Mlist.enumerate args) @ rest), acc)
  in subtms ([([],tm)], []);;


let rec replace tm = function
    ([],res) -> if equal res tm then tm else res
  | (h :: t, res) ->
    match tm with
      Var _ -> failwith "Term.replace: Var"
    | Fn (letc,tms) ->
      if h >= List.length tms then failwith "Term.replace: Fn"
      else
        let arg = List.nth tms h in
        let arg' = replace arg (t,res)
        in
          if arg' == arg then tm
          else Fn (letc, Mlist.updateNth (h,arg') tms)
;;

let find pred =
      let rec search = function
          [] -> None
        | ((path,tm) :: rest) ->
          if pred tm then Some (List.rev path)
          else
            match tm with
              Var _ -> search rest
            | Fn (_,a) ->
              let subtms = List.map (fun (i,t) -> (i :: path, t)) (Mlist.enumerate a)
              in search (subtms @ rest)
    in
      fun tm -> search [([],tm)];;


(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v tm =
  let rec free v = function
      [] -> false
    | (Var w :: tms) -> Name.equal v w || free v tms
    | (Fn (_,args) :: tms) -> free v (args @ tms);
  in free v [tm];;

let freeVarsList =
  let rec free vs = function
      [] -> vs
    | (Var v :: tms) -> free (Name.Set.add vs v) tms
    | (Fn (_,args) :: tms) -> free vs (args @ tms);
  in free Name.Set.empty;;

let freeVars tm = freeVarsList [tm];;

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

let newVar () = Var (Name.newName ());;

let newVars n = List.map (fun x -> Var x) (Name.newNames n);;

let avoid av n = Name.Set.member n av;;
let variantPrime av = Name.variantPrime (avoid av);;
let variantNum av = Name.variantNum (avoid av);;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

let hasTypeFunctionName = Name.fromString ":";;

let hasTypeFunction = (hasTypeFunctionName,2);;

let destFnHasType ((f,a) : functionName * term list) =
    if not (Name.equal f hasTypeFunctionName) then
      failwith "Term.destFnHasType"
    else
      match a with
        [tm;ty] -> (tm,ty)
      | _ -> failwith "Term.destFnHasType";;

let isFnHasType = can destFnHasType;;

let isTypedVar tm =
    match tm with
      Var _ -> true
    | Fn letc ->
      match Useful.total destFnHasType letc with
        Some (Var _, _) -> true
      | _ -> false;;

let typedSymbols tm =
  let rec sz n = function
      [] -> n
    | (tm :: tms) ->
      match tm with
        Var _ -> sz (n + 1) tms
      | Fn letc ->
        match Useful.total destFnHasType letc with
          Some (tm,_) -> sz n (tm :: tms)
        | None ->
          let (_,a) = letc
          in sz (n + 1) (a @ tms)
  in sz 0 [tm];;

let nonVarTypedSubterms tm =
  let rec subtms = function
      ([], acc) -> acc
    | ((path,tm) :: rest, acc) ->
      (match tm with
        Var _ -> subtms (rest, acc)
      | Fn letc ->
        (match Useful.total destFnHasType letc with
          Some (t,_) ->
          (match t with
             Var _ -> subtms (rest, acc)
           | Fn _ ->
             let acc = (List.rev path, tm) :: acc
             and rest = (0 :: path, t) :: rest
             in subtms (rest, acc)
          )
        | None ->
            let f (n,arg) = (n :: path, arg) in
            let (_,args) = letc in
            let acc = (List.rev path, tm) :: acc in
            let rest = List.map f (Mlist.enumerate args) @ rest
          in
            subtms (rest, acc)))
  in subtms ([([],tm)], []);;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with an explicit function application operator. *)
(* ------------------------------------------------------------------------- *)

let appName = Name.fromString ".";;

let mkFnApp (fTm,aTm) = (appName, [fTm;aTm]);;

let mkApp f_a = Fn (mkFnApp f_a);;

let destFnApp ((f,a) : Name.name * term list) =
    if not (Name.equal f appName) then failwith "Term.destFnApp"
    else
      match a with
        [fTm;aTm] -> (fTm,aTm)
      | _ -> failwith "Term.destFnApp";;

let isFnApp = can destFnApp;;

let destApp tm =
    match tm with
      Var _ -> failwith "Term.destApp"
    | Fn letc -> destFnApp letc;;

let isApp = can destApp;;

let listMkApp (f,l) = List.fold_left (fun acc x -> mkApp (x, acc)) f l;;

let stripApp tm =
  let rec strip tms tm =
      match Useful.total destApp tm with
        Some (f,a) -> strip (a :: tms) f
      | None -> (tm,tms)
  in strip [] tm;;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

let rec toString = function
    Var v -> v
  | Fn (n, []) -> n
  | Fn (n, l) -> n ^ "(" ^ String.concat ", " (List.map toString l) ^ ")";;

module Ordered =
struct type t = term let compare = compare end

module Map = Map.Make (Ordered);;

module Set = Set.Make (Ordered);;

end

(* ========================================================================= *)
(* FIRST ORDER LOGIC SUBSTITUTIONS                                           *)
(* ========================================================================= *)

module Substitute = struct

(* ------------------------------------------------------------------------- *)
(* A type of first order logic substitutions.                                *)
(* ------------------------------------------------------------------------- *)

type subst = Subst of Term.term Name.Map.map;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let empty = Subst (Name.Map.newMap ());;

let null (Subst m) = Name.Map.null m;;

let size (Subst m) = Name.Map.size m;;

let peek (Subst m) v = Name.Map.peek m v;;

let insert (Subst m) v_tm = Subst (Name.Map.insert m v_tm);;

let singleton v_tm = insert empty v_tm;;

let toList (Subst m) = Name.Map.toList m;;

let fromList l = Subst (Name.Map.fromList l);;

let foldl f b (Subst m) = Name.Map.foldl f b m;;

let foldr f b (Subst m) = Name.Map.foldr f b m;;


(* ------------------------------------------------------------------------- *)
(* Normalizing removes identity substitutions.                               *)
(* ------------------------------------------------------------------------- *)

let normalize (Subst m as sub) =
  let isNotId (v, tm) = not (Term.equalVar v tm) in
  let m' = Name.Map.filter isNotId m
  in if Name.Map.size m = Name.Map.size m' then sub else Subst m'
;;

(* ------------------------------------------------------------------------- *)
(* Applying a substitution to a first order logic term.                      *)
(* ------------------------------------------------------------------------- *)

let subst sub =
  let rec tmSub = function
        (Term.Var v as tm) ->
          (match peek sub v with
             Some tm' -> if tm == tm' then tm else tm'
           | None -> tm)
      | (Term.Fn (f,args) as tm) ->
          let args' = List.map tmSub args
          in
            if args == args' then tm
            else Term.Fn (f,args')
    in
      fun tm -> if null sub then tm else tmSub tm
    ;;

(* ------------------------------------------------------------------------- *)
(* Restricting a substitution to a given set of variables.                   *)
(* ------------------------------------------------------------------------- *)

let restrict (Subst m as sub) varSet =
      let isRestrictedVar (v, _) = Name.Set.member v varSet in
      let m' = Name.Map.filter isRestrictedVar m
    in
      if Name.Map.size m = Name.Map.size m' then sub else Subst m'
    ;;

let remove (Subst m as sub) varSet =
      let isRestrictedVar (v, _) = not (Name.Set.member v varSet) in
      let m' = Name.Map.filter isRestrictedVar m
    in
      if Name.Map.size m = Name.Map.size m' then sub else Subst m'
    ;;

(* ------------------------------------------------------------------------- *)
(* Composing two substitutions so that the following identity holds:         *)
(*                                                                           *)
(* subst (compose sub1 sub2) tm = subst sub2 (subst sub1 tm)                 *)
(* ------------------------------------------------------------------------- *)

let compose (Subst m1 as sub1) sub2 =
      let f (v,tm,s) = insert s (v, subst sub2 tm)
    in
      if null sub2 then sub1 else Name.Map.foldl f sub2 m1
    ;;

(* ------------------------------------------------------------------------- *)
(* Creating the union of two compatible substitutions.                       *)
(* ------------------------------------------------------------------------- *)

let union (Subst m1 as s1) (Subst m2 as s2) =
  let compatible ((_,tm1),(_,tm2)) =
      if Term.equal tm1 tm2 then Some tm1
      else failwith "Substitute.union: incompatible"
  in
      if Name.Map.null m1 then s2
      else if Name.Map.null m2 then s1
      else Subst (Name.Map.union compatible m1 m2)
;;

(* ------------------------------------------------------------------------- *)
(* Substitutions can be inverted iff they are renaming substitutions.        *)
(* ------------------------------------------------------------------------- *)

let invert (Subst m) =
  let inv = function
      (v, Term.Var w, s) ->
      if Name.Map.inDomain w s then failwith "Substitute.invert: non-injective"
      else Name.Map.insert s (w, Term.Var v)
    | (_, Term.Fn _, _) -> failwith "Substitute.invert: non-variable"
  in Subst (Name.Map.foldl inv (Name.Map.newMap ()) m)
;;

let isRenaming = can invert;;

(* ------------------------------------------------------------------------- *)
(* Creating a substitution to freshen variables.                             *)
(* ------------------------------------------------------------------------- *)

let freshVars s =
    let add (v, m) = insert m (v, Term.newVar ())
    in
      Name.Set.foldl add empty s
    ;;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let redexes =
    let add (v,_,s) = Name.Set.add s v
    in
      foldl add Name.Set.empty
    ;;

let residueFreeVars =
    let add (_,t,s) = Name.Set.union s (Term.freeVars t)
    in
      foldl add Name.Set.empty
    ;;

let freeVars =
    let add (v,t,s) = Name.Set.union (Name.Set.add s v) (Term.freeVars t)
    in
      foldl add Name.Set.empty
    ;;

(* ------------------------------------------------------------------------- *)
(* Functions.                                                                *)
(* ------------------------------------------------------------------------- *)

let functions =
    let add (_,t,s) = Name_arity.Set.union s (Term.functions t)
    in
      foldl add Name_arity.Set.empty
    ;;

(* ------------------------------------------------------------------------- *)
(* Matching for first order logic terms.                                     *)
(* ------------------------------------------------------------------------- *)

let matchTerms sub tm1 tm2 =
  let rec matchList sub = function
      [] -> sub
    | ((Term.Var v, tm) :: rest) ->
        let sub =
            match peek sub v with
              None -> insert sub (v,tm)
            | Some tm' ->
              if Term.equal tm tm' then sub
              else failwith "Substitute.match: incompatible matches"
      in
        matchList sub rest
    | ((Term.Fn (f1,args1), Term.Fn (f2,args2)) :: rest) ->
      if Name.equal f1 f2 && length args1 = length args2 then
        matchList sub (zip args1 args2 @ rest)
      else failwith "Substitute.match: different structure"
    | _ -> failwith "Substitute.match: functions can't match vars"
  in matchList sub [(tm1,tm2)]
;;

(* ------------------------------------------------------------------------- *)
(* Unification for first order logic terms.                                  *)
(* ------------------------------------------------------------------------- *)

let unify sub tm1 tm2 =
  let rec solve sub = function
      [] -> sub
    | ((tm1,tm2) :: rest) ->
      if tm1 == tm2 then solve sub rest
      else solve' sub (subst sub tm1, subst sub tm2, rest)

  and solve' sub = function
      ((Term.Var v), tm, rest) ->
      if Term.equalVar v tm then solve sub rest
      else if Term.freeIn v tm then failwith "Substitute.unify: occurs check"
      else
        (match peek sub v with
           None -> solve (compose sub (singleton (v,tm))) rest
         | Some tm' -> solve' sub (tm', tm, rest))
    | (tm1, ((Term.Var _) as tm2), rest) -> solve' sub (tm2, tm1, rest)
    | (Term.Fn (f1,args1), Term.Fn (f2,args2), rest) ->
      if Name.equal f1 f2 && length args1 = length args2 then
        solve sub (zip args1 args2 @ rest)
      else
        failwith "Substitute.unify: different structure"

  in solve sub [(tm1,tm2)];;

end

(* ========================================================================= *)
(* FIRST ORDER LOGIC ATOMS                                                   *)
(* ========================================================================= *)

module Atom = struct

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic atoms.                               *)
(* ------------------------------------------------------------------------- *)

type relationName = Name.name;;

type relation = relationName * int;;

type atom = relationName * Term.term list;;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

let name ((rel,_) : atom) = rel;;

let arguments ((_,args) : atom) = args;;

let arity atm = length (arguments atm);;

let relation atm = (name atm, arity atm);;

let functions =
    let f (tm,acc) = Name_arity.Set.union (Term.functions tm) acc
    in
      fun atm -> Mlist.foldl f Name_arity.Set.empty (arguments atm)
    ;;

let functionNames =
    let f (tm,acc) = Name.Set.union (Term.functionNames tm) acc
    in
      fun atm -> Mlist.foldl f Name.Set.empty (arguments atm)
    ;;

(* Binary relations *)

let mkBinop p (a,b) : atom = (p,[a;b]);;

let destBinop p = function
    (x,[a;b]) ->
    if Name.equal x p then (a,b) else failwith "Atom.destBinop: wrong binop"
  | _ -> failwith "Atom.destBinop: not a binop";;

let isBinop p = can (destBinop p);;

(* ------------------------------------------------------------------------- *)
(* The size of an atom in symbols.                                           *)
(* ------------------------------------------------------------------------- *)

let symbols atm =
    Mlist.foldl (fun (tm,z) -> Term.symbols tm + z) 1 (arguments atm);;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for atoms.                                    *)
(* ------------------------------------------------------------------------- *)

let compare (p1,tms1) (p2,tms2) =
    let c = Name.compare p1 p2 in
    if c <> 0 then c else Useful.lexCompare Term.compare tms1 tms2;;

let equal atm1 atm2 = compare atm1 atm2 = 0;;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

let subterm =
  let subterm' = function
    (_, []) -> raise (Useful.Bug "Atom.subterm: empty path")
  | ((_,tms), h :: t) ->
    if h >= length tms then failwith "Atom.subterm: bad path"
    else Term.subterm (List.nth tms h) t
  in fun x y -> subterm' (x, y)

let subterms ((_,tms) : atom) =
    let f ((n,tm),l) = List.map (fun (p,s) -> (n :: p, s)) (Term.subterms tm) @ l
    in
      Mlist.foldl f [] (Mlist.enumerate tms)
    ;;

let replace ((rel,tms) as atm) = function
    ([],_) -> raise (Useful.Bug "Atom.replace: empty path")
  | (h :: t, res) ->
    if h >= length tms then failwith "Atom.replace: bad path"
    else
      let tm = List.nth tms h
      in let tm' = Term.replace tm (t,res)
      in
        if tm == tm' then atm
        else (rel, Mlist.updateNth (h,tm') tms)
      ;;

let find pred =
      let f (i,tm) =
          match Term.find pred tm with
            Some path -> Some (i :: path)
          | None -> None
    in
      fun (_,tms) -> Mlist.first f (Mlist.enumerate tms)
    ;;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v atm = List.exists (Term.freeIn v) (arguments atm);;

let freeVars =
    let f (tm,acc) = Name.Set.union (Term.freeVars tm) acc
    in
      fun atm -> Mlist.foldl f Name.Set.empty (arguments atm)
    ;;

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

let subst sub ((p,tms) as atm) : atom =
    let tms' = List.map (Substitute.subst sub) tms
    in
      if tms' == tms then atm else (p,tms')
    ;;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

let matchAtoms sub (p1,tms1) (p2,tms2) =
  let matchArg ((tm1,tm2),sub) = Substitute.matchTerms sub tm1 tm2 in
        let _ = (Name.equal p1 p2 && length tms1 = length tms2) ||
                failwith "Atom.match"
      in
        Mlist.foldl matchArg sub (zip tms1 tms2)
      ;;

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

let unify sub (p1,tms1) (p2,tms2) =
  let unifyArg ((tm1,tm2),sub) = Substitute.unify sub tm1 tm2 in
        let _ = (Name.equal p1 p2 && length tms1 = length tms2) ||
                failwith "Atom.unify"
      in
        Mlist.foldl unifyArg sub (zip tms1 tms2)
      ;;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

let eqRelationName = Name.fromString "=";;

let eqRelationArity = 2;;

let eqRelation = (eqRelationName,eqRelationArity);;

let mkEq = mkBinop eqRelationName;;

let destEq x = destBinop eqRelationName x;;

let isEq x = isBinop eqRelationName x;;

let mkRefl tm = mkEq (tm,tm);;

let destRefl atm =
    let (l,r) = destEq atm
    in let _ = Term.equal l r || failwith "Atom.destRefl"
    in
      l
    ;;

let isRefl x = can destRefl x;;

let sym atm =
    let (l,r) = destEq atm
    in let _ = not (Term.equal l r) || failwith "Atom.sym: refl"
    in
      mkEq (r,l)
    ;;

let lhs atm = fst (destEq atm);;

let rhs atm = snd (destEq atm);;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

let typedSymbols ((_,tms) : atom) =
    Mlist.foldl (fun (tm,z) -> Term.typedSymbols tm + z) 1 tms;;

let nonVarTypedSubterms (_,tms) =
      let addArg ((n,arg),acc) =
          let addTm ((path,tm),acc) = (n :: path, tm) :: acc
          in
            Mlist.foldl addTm acc (Term.nonVarTypedSubterms arg)
    in
      Mlist.foldl addArg [] (Mlist.enumerate tms)
    ;;


module Ordered =
struct type t = atom let compare = compare end

module Map = Mmap.Make (Ordered);;

module Set = Mset.Make (Ordered);;

end


(* ========================================================================= *)
(* FIRST ORDER LOGIC FORMULAS                                                *)
(* ========================================================================= *)

module Formula = struct

(* ------------------------------------------------------------------------- *)
(* A type of first order logic formulas.                                     *)
(* ------------------------------------------------------------------------- *)

type formula =
    True
  | False
  | Atom of Atom.atom
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of Term.var * formula
  | Exists of Term.var * formula;;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Booleans *)

let mkBoolean = function
    true -> True
  | false -> False;;

let destBoolean =
    function True -> true
  | False -> false
  | _ -> failwith "destBoolean";;

let isBoolean = can destBoolean;;

let isTrue fm =
    match fm with
      True -> true
    | _ -> false;;

let isFalse fm =
    match fm with
      False -> true
    | _ -> false;;

(* Functions *)

let functions fm =
  let rec funcs fs = function
      [] -> fs
    | (True :: fms) -> funcs fs fms
    | (False :: fms) -> funcs fs fms
    | (Atom atm :: fms) -> funcs (Name_arity.Set.union (Atom.functions atm) fs) fms
    | (Not p :: fms) -> funcs fs (p :: fms)
    | (And (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Or (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Imp (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Iff (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Forall (_,p) :: fms) -> funcs fs (p :: fms)
    | (Exists (_,p) :: fms) -> funcs fs (p :: fms)
  in
    funcs Name_arity.Set.empty [fm];;

let functionNames fm =
  let rec funcs fs = function
      [] -> fs
    | (True :: fms) -> funcs fs fms
    | (False :: fms) -> funcs fs fms
    | (Atom atm :: fms) -> funcs (Name.Set.union (Atom.functionNames atm) fs) fms
    | (Not p :: fms) -> funcs fs (p :: fms)
    | (And (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Or (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Imp (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Iff (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Forall (_,p) :: fms) -> funcs fs (p :: fms)
    | (Exists (_,p) :: fms) -> funcs fs (p :: fms)
  in
    funcs Name.Set.empty [fm];;

(* Relations *)
let relations fm =
  let rec rels fs = function
      [] -> fs
    | (True :: fms) -> rels fs fms
    | (False :: fms) -> rels fs fms
    | (Atom atm :: fms) ->
      rels (Name_arity.Set.add fs (Atom.relation atm)) fms
    | (Not p :: fms) -> rels fs (p :: fms)
    | (And (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Or (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Imp (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Iff (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Forall (_,p) :: fms) -> rels fs (p :: fms)
    | (Exists (_,p) :: fms) -> rels fs (p :: fms)
  in rels Name_arity.Set.empty [fm];;


let relationNames fm =
  let rec rels fs = function
      [] -> fs
    | (True :: fms) -> rels fs fms
    | (False :: fms) -> rels fs fms
    | (Atom atm :: fms) -> rels (Name.Set.add fs (Atom.name atm)) fms
    | (Not p :: fms) -> rels fs (p :: fms)
    | (And (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Or (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Imp (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Iff (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Forall (_,p) :: fms) -> rels fs (p :: fms)
    | (Exists (_,p) :: fms) -> rels fs (p :: fms)
  in rels Name.Set.empty [fm];;

(* Atoms *)

let destAtom = function
    (Atom atm) -> atm
  | _ -> failwith "Formula.destAtom";;

let isAtom = can destAtom;;

(* Negations *)

let destNeg = function
    (Not p) -> p
  | _ -> failwith "Formula.destNeg";;

let isNeg = can destNeg;;

let stripNeg =
    let rec strip n = function
          (Not fm) -> strip (n + 1) fm
        | fm -> (n,fm)
    in
      strip 0
    ;;

(* Conjunctions *)

let listMkConj fms =
    match List.rev fms with
      [] -> True
    | fm :: fms -> Mlist.foldl (fun (x, y) -> And (x, y)) fm fms;;

let stripConj =
  let rec strip cs = function
      (And (p,q)) -> strip (p :: cs) q
    | fm -> List.rev (fm :: cs)
  in function
      True -> []
    | fm -> strip [] fm;;

let flattenConj =
      let rec flat acc = function
          [] -> acc
        | (And (p,q) :: fms) -> flat acc (q :: p :: fms)
        | (True :: fms) -> flat acc fms
        | (fm :: fms) -> flat (fm :: acc) fms
    in
      fun fm -> flat [] [fm]
    ;;

(* Disjunctions *)

let listMkDisj fms =
    match List.rev fms with
      [] -> False
    | fm :: fms -> Mlist.foldl (fun (x,y) -> Or (x,y)) fm fms;;

let stripDisj =
  let rec strip cs = function
      (Or (p,q)) -> strip (p :: cs) q
    | fm -> List.rev (fm :: cs)
  in function
      False -> []
    | fm -> strip [] fm;;

let flattenDisj =
      let rec flat acc = function
          [] -> acc
        | (Or (p,q) :: fms) -> flat acc (q :: p :: fms)
        | (False :: fms) -> flat acc fms
        | (fm :: fms) -> flat (fm :: acc) fms
    in
      fun fm -> flat [] [fm]
    ;;

(* Equivalences *)

let listMkEquiv fms =
    match List.rev fms with
      [] -> True
    | fm :: fms -> Mlist.foldl (fun (x,y) -> Iff (x,y)) fm fms;;

let stripEquiv =
  let rec strip cs = function
      (Iff (p,q)) -> strip (p :: cs) q
    | fm -> List.rev (fm :: cs)
  in function
      True -> []
    | fm -> strip [] fm;;

let flattenEquiv =
      let rec flat acc = function
          [] -> acc
        | (Iff (p,q) :: fms) -> flat acc (q :: p :: fms)
        | (True :: fms) -> flat acc fms
        | (fm :: fms) -> flat (fm :: acc) fms
    in
      fun fm -> flat [] [fm]
    ;;

(* Universal quantifiers *)

let destForall = function
    (Forall (v,f)) -> (v,f)
  | _ -> failwith "destForall";;

let isForall = can destForall;;

let rec listMkForall = function
    ([],body) -> body
  | (v :: vs, body) -> Forall (v, listMkForall (vs,body));;

let setMkForall (vs,body) = Name.Set.foldr (fun (x,y) -> Forall (x,y)) body vs;;

let stripForall =
  let rec strip vs = function
      (Forall (v,b)) -> strip (v :: vs) b
    | tm -> (List.rev vs, tm)
  in
    strip [];;

(* Existential quantifiers *)

let destExists = function
    (Exists (v,f)) -> (v,f)
  | _ -> failwith "destExists";;

let isExists = can destExists;;

let rec listMkExists = function
    ([],body) -> body
  | (v :: vs, body) -> Exists (v, listMkExists (vs,body));;

let setMkExists (vs,body) = Name.Set.foldr (fun (x,y) -> Exists (x,y)) body vs;;

let stripExists =
  let rec strip vs = function
      (Exists (v,b)) -> strip (v :: vs) b
    | tm -> (List.rev vs, tm)
  in
    strip [];;

(* ------------------------------------------------------------------------- *)
(* The size of a formula in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

let symbols fm =
  let rec sz n = function
      [] -> n
    | (True :: fms) -> sz (n + 1) fms
    | (False :: fms) -> sz (n + 1) fms
    | (Atom atm :: fms) -> sz (n + Atom.symbols atm) fms
    | (Not p :: fms) -> sz (n + 1) (p :: fms)
    | (And (p,q) :: fms) -> sz (n + 1) (p :: q :: fms)
    | (Or (p,q) :: fms) -> sz (n + 1) (p :: q :: fms)
    | (Imp (p,q) :: fms) -> sz (n + 1) (p :: q :: fms)
    | (Iff (p,q) :: fms) -> sz (n + 1) (p :: q :: fms)
    | (Forall (_,p) :: fms) -> sz (n + 1) (p :: fms)
    | (Exists (_,p) :: fms) -> sz (n + 1) (p :: fms)
in
  sz 0 [fm];;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for formulas.                                 *)
(* ------------------------------------------------------------------------- *)

let compare fm1 fm2 =
  let rec cmp = function
      [] -> 0
    | (((f1, f2) as f1_f2) :: fs) ->
      if f1 == f2 then cmp fs
      else
        match f1_f2 with
          (True,True) -> cmp fs
        | (True,_) -> -1
        | (_,True) -> 1
        | (False,False) -> cmp fs
        | (False,_) -> -1
        | (_,False) -> 1
        | (Atom atm1, Atom atm2) ->
            let c = Atom.compare atm1 atm2 in
            if c <> 0 then c else cmp fs
        | (Atom _, _) -> -1
        | (_, Atom _) -> 1
        | (Not p1, Not p2) -> cmp ((p1,p2) :: fs)
        | (Not _, _) -> -1
        | (_, Not _) -> 1
        | (And (p1,q1), And (p2,q2)) -> cmp ((p1,p2) :: (q1,q2) :: fs)
        | (And _, _) -> -1
        | (_, And _) -> 1
        | (Or (p1,q1), Or (p2,q2)) -> cmp ((p1,p2) :: (q1,q2) :: fs)
        | (Or _, _) -> -1
        | (_, Or _) -> 1
        | (Imp (p1,q1), Imp (p2,q2)) -> cmp ((p1,p2) :: (q1,q2) :: fs)
        | (Imp _, _) -> -1
        | (_, Imp _) -> 1
        | (Iff (p1,q1), Iff (p2,q2)) -> cmp ((p1,p2) :: (q1,q2) :: fs)
        | (Iff _, _) -> -1
        | (_, Iff _) -> 1
        | (Forall (v1,p1), Forall (v2,p2)) ->
            let c = Name.compare v1 v2 in
            if c <> 0 then c else cmp ((p1,p2) :: fs)
        | (Forall _, Exists _) -> -1
        | (Exists _, Forall _) -> 1
        | (Exists (v1,p1), Exists (v2,p2)) ->
            let c = Name.compare v1 v2 in
            if c <> 0 then c else cmp ((p1,p2) :: fs)
in
  cmp [(fm1,fm2)];;

let equal fm1 fm2 = compare fm1 fm2 = 0;;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v =
      let rec f = function
          [] -> false
        | (True :: fms) -> f fms
        | (False :: fms) -> f fms
        | (Atom atm :: fms) -> Atom.freeIn v atm || f fms
        | (Not p :: fms) -> f (p :: fms)
        | (And (p,q) :: fms) -> f (p :: q :: fms)
        | (Or (p,q) :: fms) -> f (p :: q :: fms)
        | (Imp (p,q) :: fms) -> f (p :: q :: fms)
        | (Iff (p,q) :: fms) -> f (p :: q :: fms)
        | (Forall (w,p) :: fms) ->
          if Name.equal v w then f fms else f (p :: fms)
        | (Exists (w,p) :: fms) ->
          if Name.equal v w then f fms else f (p :: fms)
    in
      fun fm -> f [fm]
    ;;

let add (fm,vs) =
  let rec fv vs = function
      [] -> vs
    | ((_,True) :: fms) -> fv vs fms
    | ((_,False) :: fms) -> fv vs fms
    | ((bv, Atom atm) :: fms) ->
      fv (Name.Set.union vs (Name.Set.difference (Atom.freeVars atm) bv)) fms
    | ((bv, Not p) :: fms) -> fv vs ((bv,p) :: fms)
    | ((bv, And (p,q)) :: fms) -> fv vs ((bv,p) :: (bv,q) :: fms)
    | ((bv, Or (p,q)) :: fms) -> fv vs ((bv,p) :: (bv,q) :: fms)
    | ((bv, Imp (p,q)) :: fms) -> fv vs ((bv,p) :: (bv,q) :: fms)
    | ((bv, Iff (p,q)) :: fms) -> fv vs ((bv,p) :: (bv,q) :: fms)
    | ((bv, Forall (v,p)) :: fms) -> fv vs ((Name.Set.add bv v, p) :: fms)
    | ((bv, Exists (v,p)) :: fms) -> fv vs ((Name.Set.add bv v, p) :: fms)

   in fv vs [(Name.Set.empty,fm)];;

  let freeVars fm = add (fm,Name.Set.empty);;

  let freeVarsList fms = Mlist.foldl add Name.Set.empty fms;;

let specialize fm = snd (stripForall fm);;

let generalize fm = listMkForall (Name.Set.toList (freeVars fm), fm);;

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

  let rec substCheck sub fm = if Substitute.null sub then fm else substFm sub fm

  and substFm sub fm = match fm with
        True -> fm
      | False -> fm
      | Atom (p,tms) ->
          let tms' = List.map (Substitute.subst sub) tms
        in
          if tms == tms' then fm else Atom (p,tms')
      | Not p ->
          let p' = substFm sub p
        in
          if p == p' then fm else Not p'
      | And (p,q) -> substConn sub fm (fun (x,y) -> And (x,y)) p q
      | Or (p,q) -> substConn sub fm (fun (x,y) -> Or (x,y)) p q
      | Imp (p,q) -> substConn sub fm (fun (x,y) -> Imp (x,y)) p q
      | Iff (p,q) -> substConn sub fm (fun (x,y) -> Iff (x,y)) p q
      | Forall (v,p) -> substQuant sub fm (fun (x,y) -> Forall (x,y)) v p
      | Exists (v,p) -> substQuant sub fm (fun (x,y) -> Exists (x,y)) v p

  and substConn sub fm conn p q =
        let p' = substFm sub p
        and q' = substFm sub q
      in
        if p == p' && q == q'
        then fm
        else conn (p',q')

  and substQuant sub fm quant v p =
        let v' =
              let f (w,s) =
                  if Name.equal w v then s
                  else
                    match Substitute.peek sub w with
                      None -> Name.Set.add s w
                    | Some tm -> Name.Set.union s (Term.freeVars tm)

              in let vars = freeVars p
              in let vars = Name.Set.foldl f Name.Set.empty vars
            in
              Term.variantPrime vars v

        in let sub =
            if Name.equal v v' then Substitute.remove sub (Name.Set.singleton v)
            else Substitute.insert sub (v, Term.Var v')

        in let p' = substCheck sub p
      in
        if Name.equal v v' && p == p' then fm
        else quant (v',p');;

  let subst = substCheck;;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

let mkEq a_b = Atom (Atom.mkEq a_b);;

let destEq fm = Atom.destEq (destAtom fm);;

let isEq = can destEq;;

let mkNeq a_b = Not (mkEq a_b);;

let destNeq = function
    (Not fm) -> destEq fm
  | _ -> failwith "Formula.destNeq";;

let isNeq = can destNeq;;

let mkRefl tm = Atom (Atom.mkRefl tm);;

let destRefl fm = Atom.destRefl (destAtom fm);;

let isRefl = can destRefl;;

let sym fm = Atom (Atom.sym (destAtom fm));;

let lhs fm = fst (destEq fm);;

let rhs fm = snd (destEq fm);;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

let truthName = Name.fromString "T"
and falsityName = Name.fromString "F"
and conjunctionName = Name.fromString "/\\"
and disjunctionName = Name.fromString "\\/"
and implicationName = Name.fromString "==>"
and equivalenceName = Name.fromString "<=>"
and universalName = Name.fromString "!"
and existentialName = Name.fromString "?";;

  let rec demote = function
      True -> Term.Fn (truthName,[])
    | False -> Term.Fn (falsityName,[])
    | (Atom (p,tms)) -> Term.Fn (p,tms)
    | (Not p) ->
      let
        s = "~"
      in
        Term.Fn (Name.fromString s, [demote p])
    | (And (p,q)) -> Term.Fn (conjunctionName, [demote p; demote q])
    | (Or (p,q)) -> Term.Fn (disjunctionName, [demote p; demote q])
    | (Imp (p,q)) -> Term.Fn (implicationName, [demote p; demote q])
    | (Iff (p,q)) -> Term.Fn (equivalenceName, [demote p; demote q])
    | (Forall (v,b)) -> Term.Fn (universalName, [Term.Var v; demote b])
    | (Exists (v,b)) ->
      Term.Fn (existentialName, [Term.Var v; demote b]);;

  let toString fm = Term.toString (demote fm);;


(* ------------------------------------------------------------------------- *)
(* Splitting goals.                                                          *)
(* ------------------------------------------------------------------------- *)

  let add_asms asms goal =
      if Mlist.null asms then goal else Imp (listMkConj (List.rev asms), goal);;

  let add_var_asms asms v goal = add_asms asms (Forall (v,goal));;

  let rec split asms pol fm =
      match (pol,fm) with
        (* Positive splittables *)
        (true,True) -> []
      | (true, Not f) -> split asms false f
      | (true, And (f1,f2)) -> split asms true f1 @ split (f1 :: asms) true f2
      | (true, Or (f1,f2)) -> split (Not f1 :: asms) true f2
      | (true, Imp (f1,f2)) -> split (f1 :: asms) true f2
      | (true, Iff (f1,f2)) ->
        split (f1 :: asms) true f2 @ split (f2 :: asms) true f1
      | (true, Forall (v,f)) -> List.map (add_var_asms asms v) (split [] true f)
        (* Negative splittables *)
      | (false,False) -> []
      | (false, Not f) -> split asms true f
      | (false, And (f1,f2)) -> split (f1 :: asms) false f2
      | (false, Or (f1,f2)) ->
        split asms false f1 @ split (Not f1 :: asms) false f2
      | (false, Imp (f1,f2)) -> split asms true f1 @ split (f1 :: asms) false f2
      | (false, Iff (f1,f2)) ->
        split (f1 :: asms) false f2 @ split (Not f2 :: asms) true f1
      | (false, Exists (v,f)) -> List.map (add_var_asms asms v) (split [] false f)
        (* Unsplittables *)
      | _ -> [add_asms asms (if pol then fm else Not fm)];;

  let splitGoal fm = split [] true fm;;

(*MetisTrace3
let splitGoal = fun fm =>
    let
      let result = splitGoal fm
      let () = Print.trace pp "Formula.splitGoal: fm" fm
      let () = Print.trace (Print.ppList pp) "Formula.splitGoal: result" result
    in
      result
    end;;
*)

module Ordered =
struct type t = formula let compare = compare end

module Map = Mmap.Make (Ordered);;

module Set = Mset.Make (Ordered);;

end


(* ========================================================================= *)
(* FIRST ORDER LOGIC LITERALS                                                *)
(* ========================================================================= *)

module Literal = struct

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic literals.                            *)
(* ------------------------------------------------------------------------- *)

type polarity = bool;;

type literal = polarity * Atom.atom;;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

let polarity ((pol,_) : literal) = pol;;

let atom ((_,atm) : literal) = atm;;

let name lit = Atom.name (atom lit);;

let arguments lit = Atom.arguments (atom lit);;

let arity lit = Atom.arity (atom lit);;

let positive lit = polarity lit;;

let negative lit = not (polarity lit);;

let negate (pol,atm) : literal = (not pol, atm)

let relation lit = Atom.relation (atom lit);;

let functions lit = Atom.functions (atom lit);;

let functionNames lit = Atom.functionNames (atom lit);;

(* Binary relations *)

let mkBinop rel (pol,a,b) : literal = (pol, Atom.mkBinop rel (a,b));;

let destBinop rel ((pol,atm) : literal) =
    match Atom.destBinop rel atm with (a,b) -> (pol,a,b);;

let isBinop rel = can (destBinop rel);;

(* Formulas *)

let toFormula = function
    (true,atm) -> Formula.Atom atm
  | (false,atm) -> Formula.Not (Formula.Atom atm);;

let fromFormula = function
    (Formula.Atom atm) -> (true,atm)
  | (Formula.Not (Formula.Atom atm)) -> (false,atm)
  | _ -> failwith "Literal.fromFormula";;

(* ------------------------------------------------------------------------- *)
(* The size of a literal in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

let symbols ((_,atm) : literal) = Atom.symbols atm;;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for literals.                                 *)
(* ------------------------------------------------------------------------- *)

let compare = Useful.prodCompare Useful.boolCompare Atom.compare;;

let equal (p1,atm1) (p2,atm2) = p1 = p2 && Atom.equal atm1 atm2;;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

let subterm lit path = Atom.subterm (atom lit) path;;

let subterms lit = Atom.subterms (atom lit);;

let replace ((pol,atm) as lit) path_tm =
      let atm' = Atom.replace atm path_tm
    in
      if atm == atm' then lit else (pol,atm')
    ;;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v lit = Atom.freeIn v (atom lit);;

let freeVars lit = Atom.freeVars (atom lit);;

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

let subst sub ((pol,atm) as lit) : literal =
      let atm' = Atom.subst sub atm
    in
      if atm' == atm then lit else (pol,atm')
    ;;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

let matchLiterals sub ((pol1,atm1) : literal) (pol2,atm2) =
      let _ = pol1 = pol2 || failwith "Literal.match"
    in
      Atom.matchAtoms sub atm1 atm2
    ;;

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

let unify sub ((pol1,atm1) : literal) (pol2,atm2) =
      let _ = pol1 = pol2 || failwith "Literal.unify"
    in
      Atom.unify sub atm1 atm2
    ;;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

let mkEq l_r : literal = (true, Atom.mkEq l_r);;

let destEq = function
    ((true,atm) : literal) -> Atom.destEq atm
  | (false,_) -> failwith "Literal.destEq";;

let isEq = can destEq;;

let mkNeq l_r : literal = (false, Atom.mkEq l_r);;

let destNeq = function
    ((false,atm) : literal) -> Atom.destEq atm
  | (true,_) -> failwith "Literal.destNeq";;

let isNeq = can destNeq;;

let mkRefl tm = (true, Atom.mkRefl tm);;

let destRefl = function
    (true,atm) -> Atom.destRefl atm
  | (false,_) -> failwith "Literal.destRefl";;

let isRefl = can destRefl;;

let mkIrrefl tm = (false, Atom.mkRefl tm);;

let destIrrefl = function
    (true,_) -> failwith "Literal.destIrrefl"
  | (false,atm) -> Atom.destRefl atm;;

let isIrrefl = can destIrrefl;;

let sym (pol,atm) : literal = (pol, Atom.sym atm);;

let lhs ((_,atm) : literal) = Atom.lhs atm;;

let rhs ((_,atm) : literal) = Atom.rhs atm;;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

let typedSymbols ((_,atm) : literal) = Atom.typedSymbols atm;;

let nonVarTypedSubterms ((_,atm) : literal) = Atom.nonVarTypedSubterms atm;;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

let toString literal = Formula.toString (toFormula literal);;


module Ordered =
struct type t = literal let compare = compare end

module Map = Mmap.Make (Ordered);;

module Set =
struct
  include Mset.Make (Ordered);;

  let negateMember lit set = member (negate lit) set;;

  let negate =
        let f (lit,set) = add set (negate lit)
      in
        foldl f empty
      ;;

  let relations =
        let f (lit,set) = Name_arity.Set.add set (relation lit)
      in
        foldl f Name_arity.Set.empty
      ;;

  let functions =
        let f (lit,set) = Name_arity.Set.union set (functions lit)
      in
        foldl f Name_arity.Set.empty
      ;;

  let freeIn v = exists (freeIn v);;

  let freeVars =
        let f (lit,set) = Name.Set.union set (freeVars lit)
      in
        foldl f Name.Set.empty
      ;;

  let freeVarsList =
        let f (lits,set) = Name.Set.union set (freeVars lits)
      in
        Mlist.foldl f Name.Set.empty
      ;;

  let symbols =
        let f (lit,z) = symbols lit + z
      in
        foldl f 0
      ;;

  let typedSymbols =
        let f (lit,z) = typedSymbols lit + z
      in
        foldl f 0
      ;;

  let subst sub lits =
        let substLit (lit,(eq,lits')) =
              let lit' = subst sub lit
              in let eq = eq && lit == lit'
            in
              (eq, add lits' lit')

        in let (eq,lits') = foldl substLit (true,empty) lits
      in
        if eq then lits else lits'
      ;;

  let conjoin set =
      Formula.listMkConj (List.map toFormula (toList set));;

  let disjoin set =
      Formula.listMkDisj (List.map toFormula (toList set));;

  let toString cl =
    "{" ^ String.concat ", " (List.map toString (toList cl)) ^ "}"

end

module Set_ordered =
struct type t = Set.set let compare = Set.compare end

module Set_map = Mmap.Make (Set_ordered);;

module Set_set = Mset.Make (Set_ordered);;

end


(* ========================================================================= *)
(* A LOGICAL KERNEL FOR FIRST ORDER CLAUSAL THEOREMS                         *)
(* ========================================================================= *)

module Thm = struct

(* ------------------------------------------------------------------------- *)
(* An abstract type of first order logic theorems.                           *)
(* ------------------------------------------------------------------------- *)

type clause = Literal.Set.set;;

type inferenceType =
    Axiom
  | Assume
  | Subst
  | Factor
  | Resolve
  | Refl
  | Equality;;

type thm = Thm of clause * (inferenceType * thm list);;

type inference = inferenceType * thm list;;

(* ------------------------------------------------------------------------- *)
(* Theorem destructors.                                                      *)
(* ------------------------------------------------------------------------- *)

let clause (Thm (cl,_)) = cl;;

let inference (Thm (_,inf)) = inf;;

(* Tautologies *)

let isTautology th =
  let chk = function
      (_,None) -> None
    | ((pol,atm), Some set) ->
      if (pol && Atom.isRefl atm) || Atom.Set.member atm set then None
      else Some (Atom.Set.add set atm)
  in
      match Literal.Set.foldl chk (Some Atom.Set.empty) (clause th) with
        Some _ -> false
      | None -> true;;

(* Contradictions *)

let isContradiction th = Literal.Set.null (clause th);;

(* Unit theorems *)

let destUnit (Thm (cl,_)) =
    if Literal.Set.size cl = 1 then Literal.Set.pick cl
    else failwith "Thm.destUnit";;

let isUnit = can destUnit;;

(* Unit equality theorems *)

let destUnitEq th = Literal.destEq (destUnit th);;

let isUnitEq = can destUnitEq;;

(* Literals *)

let member lit (Thm (cl,_)) = Literal.Set.member lit cl;;

let negateMember lit (Thm (cl,_)) = Literal.Set.negateMember lit cl;;

(* ------------------------------------------------------------------------- *)
(* A total order.                                                            *)
(* ------------------------------------------------------------------------- *)

let compare th1 th2 = Literal.Set.compare (clause th1) (clause th2);;

let equal th1 th2 = Literal.Set.equal (clause th1) (clause th2);;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v (Thm (cl,_)) = Literal.Set.freeIn v cl;;

let freeVars (Thm (cl,_)) = Literal.Set.freeVars cl;;


(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

open Format

let inferenceTypeToString = function
    Axiom -> "axiom"
  | Assume -> "assume"
  | Subst -> "subst"
  | Factor -> "factor"
  | Resolve -> "resolve"
  | Refl -> "refl"
  | Equality -> "equality"

let toString (Thm (cl, (infType, ths))) =
  inferenceTypeToString infType ^ ": " ^ Literal.Set.toString cl

let rec print_proof (Thm (cl, (infType, ths))) =
  print_string ("Inference: " ^ inferenceTypeToString infType);
  print_break 0 0;

  print_string ("Clauses: " ^ Literal.Set.toString cl);
  print_break 0 0;

  print_string "Theorems: ";
  if ths = []
  then print_string "<none>"
  else begin
    print_break 0 0;
    open_vbox 2;
    print_break 0 0;
    List.iter (print_proof) ths;
    close_box ()
  end;
  print_break 0 0


(* ------------------------------------------------------------------------- *)
(* Primitive rules of inference.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----- axiom C                                                             *)
(*   C                                                                       *)
(* ------------------------------------------------------------------------- *)

let axiom cl = Thm (cl,(Axiom,[]));;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----------- assume L                                                      *)
(*   L \/ ~L                                                                 *)
(* ------------------------------------------------------------------------- *)

let assume lit =
    Thm (Literal.Set.fromList [lit; Literal.negate lit], (Assume,[]));;

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- subst s                                                          *)
(*   C[s]                                                                    *)
(* ------------------------------------------------------------------------- *)

let subst sub (Thm (cl,inf) as th) =
      let cl' = Literal.Set.subst sub cl
    in
      if cl == cl' then th
      else
        match inf with
          (Subst,_) -> Thm (cl',inf)
        | _ -> Thm (cl',(Subst,[th]))
    ;;

(* ------------------------------------------------------------------------- *)
(*   L \/ C    ~L \/ D                                                       *)
(* --------------------- resolve L                                           *)
(*        C \/ D                                                             *)
(*                                                                           *)
(* The literal L must occur in the first theorem, and the literal ~L must    *)
(* occur in the second theorem.                                              *)
(* ------------------------------------------------------------------------- *)

let resolve lit (Thm (cl1,_) as th1) (Thm (cl2,_) as th2) =
      let cl1' = Literal.Set.delete cl1 lit
      and cl2' = Literal.Set.delete cl2 (Literal.negate lit)
    in
      Thm (Literal.Set.union cl1' cl2', (Resolve,[th1;th2]))
    ;;

(*MetisDebug
let resolve = fun lit -> fun pos -> fun neg ->
    resolve lit pos neg
    handle Failure err ->
      raise Failure ("Thm.resolve:\nlit = " ^ Literal.toString lit ^
                     "\npos = " ^ toString pos ^
                     "\nneg = " ^ toString neg ^ "\n" ^ err);;
*)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- refl t                                                          *)
(*   t = t                                                                   *)
(* ------------------------------------------------------------------------- *)

let refl tm = Thm (Literal.Set.singleton (true, Atom.mkRefl tm), (Refl,[]));;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------ equality L p t                                   *)
(*   ~(s = t) \/ ~L \/ L'                                                    *)
(*                                                                           *)
(* where s is the subterm of L at path p, and L' is L with the subterm at    *)
(* path p being replaced by t.                                               *)
(* ------------------------------------------------------------------------- *)

let equality lit path t =
      let s = Literal.subterm lit path

      in let lit' = Literal.replace lit (path,t)

      in let eqLit = Literal.mkNeq (s,t)

      in let cl = Literal.Set.fromList [eqLit; Literal.negate lit; lit']
    in
      Thm (cl,(Equality,[]))
    ;;

end


(* ========================================================================= *)
(* PROOFS IN FIRST ORDER LOGIC                                               *)
(* ========================================================================= *)

module Proof = struct

(* ------------------------------------------------------------------------- *)
(* A type of first order logic proofs.                                       *)
(* ------------------------------------------------------------------------- *)

type inference =
    Axiom of Literal.Set.set
  | Assume of Atom.atom
  | Subst of Substitute.subst * Thm.thm
  | Resolve of Atom.atom * Thm.thm * Thm.thm
  | Refl of Term.term
  | Equality of Literal.literal * Term.path * Term.term;;

type proof = (Thm.thm * inference) list;;


(* ------------------------------------------------------------------------- *)
(* Reconstructing single inferences.                                         *)
(* ------------------------------------------------------------------------- *)

let parents = function
    (Axiom _) -> []
  | (Assume _) -> []
  | (Subst (_,th)) -> [th]
  | (Resolve (_,th,th')) -> [th;th']
  | (Refl _) -> []
  | (Equality _) -> [];;

let inferenceToThm = function
    (Axiom cl) -> Thm.axiom cl
  | (Assume atm) -> Thm.assume (true,atm)
  | (Subst (sub,th)) -> Thm.subst sub th
  | (Resolve (atm,th,th')) -> Thm.resolve (true,atm) th th'
  | (Refl tm) -> Thm.refl tm
  | (Equality (lit,path,r)) -> Thm.equality lit path r;;

  let reconstructSubst cl cl' =
        let rec recon = function
            [] ->
(*MetisTrace3
              let () = Print.trace Literal.Set.pp "reconstructSubst: cl" cl
              let () = Print.trace Literal.Set.pp "reconstructSubst: cl'" cl'
*)
              raise (Useful.Bug "can't reconstruct Subst rule")
          | (([],sub) :: others) ->
            if Literal.Set.equal (Literal.Set.subst sub cl) cl' then sub
            else recon others
          | ((lit :: lits, sub) :: others) ->
              let checkLit (lit',acc) =
                  match Useful.total (Literal.matchLiterals sub lit) lit' with
                    None -> acc
                  | Some sub -> (lits,sub) :: acc
            in
              recon (Literal.Set.foldl checkLit others cl')
      in
        Substitute.normalize (recon [(Literal.Set.toList cl, Substitute.empty)])
      ;;
(*MetisDebug
      handle Failure err ->
        raise (Useful.Bug ("Proof.recontructSubst: shouldn't fail:\n" ^ err));;
*)

  let reconstructResolvant cl1 cl2 cl =
      (if not (Literal.Set.subset cl1 cl) then
         Literal.Set.pick (Literal.Set.difference cl1 cl)
       else if not (Literal.Set.subset cl2 cl) then
         Literal.negate (Literal.Set.pick (Literal.Set.difference cl2 cl))
       else
         (* A useless resolution, but we must reconstruct it anyway *)
           let cl1' = Literal.Set.negate cl1
           and cl2' = Literal.Set.negate cl2
           in let lits = Literal.Set.intersectList [cl1;cl1';cl2;cl2']
         in
           if not (Literal.Set.null lits) then Literal.Set.pick lits
           else raise (Useful.Bug "can't reconstruct Resolve rule")
         );;
(*MetisDebug
      handle Failure err ->
        raise (Useful.Bug ("Proof.recontructResolvant: shouldn't fail:\n" ^ err));;
*)

  let reconstructEquality cl =
(*MetisTrace3
        let () = Print.trace Literal.Set.pp "Proof.reconstructEquality: cl" cl
*)

        let rec sync s t path (f,a) (f',a') =
            if not (Name.equal f f' && length a = length a') then None
            else
                let itms = Mlist.enumerate (zip a a')
              in
                (match List.filter (fun x -> not (uncurry Term.equal (snd x))) itms with
                  [(i,(tm,tm'))] ->
                    let path = i :: path
                  in
                    if Term.equal tm s && Term.equal tm' t then
                      Some (List.rev path)
                    else
                      (match (tm,tm') with
                        (Term.Fn f_a, Term.Fn f_a') -> sync s t path f_a f_a'
                      | _ -> None)
                | _ -> None)

        in let recon (neq,(pol,atm),(pol',atm')) =
            if pol = pol' then None
            else
                let (s,t) = Literal.destNeq neq

                in let path =
                    if not (Term.equal s t) then sync s t [] atm atm'
                    else if not (Atom.equal atm atm') then None
                    else Atom.find (Term.equal s) atm
              in
                match path with
                  Some path -> Some ((pol',atm),path,t)
                | None -> None

        in let candidates =
            match List.partition Literal.isNeq (Literal.Set.toList cl) with
              ([l1],[l2;l3]) -> [(l1,l2,l3);(l1,l3,l2)]
            | ([l1;l2],[l3]) -> [(l1,l2,l3);(l1,l3,l2);(l2,l1,l3);(l2,l3,l1)]
            | ([l1],[l2]) -> [(l1,l1,l2);(l1,l2,l1)]
            | _ -> raise (Useful.Bug "reconstructEquality: malformed")

(*MetisTrace3
        let ppCands =
            Print.ppList (Print.ppTriple Literal.pp Literal.pp Literal.pp)
        let () = Print.trace ppCands
                   "Proof.reconstructEquality: candidates" candidates
*)
      in
        match Mlist.first recon candidates with
          Some info -> info
        | None -> raise (Useful.Bug "can't reconstruct Equality rule")
      ;;
(*MetisDebug
      handle Failure err ->
        raise (Useful.Bug ("Proof.recontructEquality: shouldn't fail:\n" ^ err));;
*)

  let reconstruct cl = function
      (Thm.Axiom,[]) -> Axiom cl
    | (Thm.Assume,[]) ->
      (match Literal.Set.findl Literal.positive cl with
         Some (_,atm) -> Assume atm
       | None -> raise (Useful.Bug "malformed Assume inference"))
    | (Thm.Subst,[th]) ->
      Subst (reconstructSubst (Thm.clause th) cl, th)
    | (Thm.Resolve,[th1;th2]) ->
        let cl1 = Thm.clause th1
        and cl2 = Thm.clause th2
        in let (pol,atm) = reconstructResolvant cl1 cl2 cl
      in
        if pol then Resolve (atm,th1,th2) else Resolve (atm,th2,th1)
    | (Thm.Refl,[]) ->
      (match Literal.Set.findl (K true) cl with
         Some lit -> Refl (Literal.destRefl lit)
       | None -> raise (Useful.Bug "malformed Refl inference"))
    | (Thm.Equality,[]) -> let (x,y,z) = (reconstructEquality cl) in Equality (x,y,z)
    | _ -> raise (Useful.Bug "malformed inference");;

  let thmToInference th =
(*MetisTrace3
        let () = Print.trace Thm.pp "Proof.thmToInference: th" th
*)

        let cl = Thm.clause th

        in let thmInf = Thm.inference th

(*MetisTrace3
        let ppThmInf = Print.ppPair Thm.ppInferenceType (Print.ppList Thm.pp)
        let () = Print.trace ppThmInf "Proof.thmToInference: thmInf" thmInf
*)

        in let inf = reconstruct cl thmInf

(*MetisTrace3
        let () = Print.trace ppInference "Proof.thmToInference: inf" inf
*)
(*MetisDebug
        let () =
            let
              let th' = inferenceToThm inf
            in
              if Literal.Set.equal (Thm.clause th') cl then ()
              else
                raise
                  Useful.Bug
                    ("Proof.thmToInference: bad inference reconstruction:" ^
                     "\n  th = " ^ Thm.toString th ^
                     "\n  inf = " ^ inferenceToString inf ^
                     "\n  inf th = " ^ Thm.toString th')
            end
*)
      in
        inf
(*MetisDebug
      handle Failure err ->
        raise (Useful.Bug ("Proof.thmToInference: shouldn't fail:\n" ^ err));;
*)
;;

(* ------------------------------------------------------------------------- *)
(* Reconstructing whole proofs.                                              *)
(* ------------------------------------------------------------------------- *)

let proof th =
  let emptyThms : Thm.thm Literal.Set_map.map = Literal.Set_map.newMap ()

  in let rec addThms (th,ths) =
        let cl = Thm.clause th
      in
        if Literal.Set_map.inDomain cl ths then ths
        else
            let (_,pars) = Thm.inference th
            in let ths = Mlist.foldl addThms ths pars
          in
            if Literal.Set_map.inDomain cl ths then ths
            else Literal.Set_map.insert ths (cl,th)

  in let mkThms th = addThms (th,emptyThms)

  in let rec addProof (th,(ths,acc)) =
        let cl = Thm.clause th
      in
        match Literal.Set_map.peek ths cl with
          None -> (ths,acc)
        | Some th ->
            let (_,pars) = Thm.inference th
            in let (ths,acc) = Mlist.foldl addProof (ths,acc) pars
            in let ths = Literal.Set_map.delete ths cl
            in let acc = (th, thmToInference th) :: acc
          in
            (ths,acc)

  in let mkProof ths th =
        let (ths,acc) = addProof (th,(ths,[]))
(*MetisTrace4
        let () = Print.trace Print.ppInt "Proof.proof: unnecessary clauses" (Literal.Set_map.size ths)
*)
      in
        List.rev acc

(*MetisTrace3
        let () = Print.trace Thm.pp "Proof.proof: th" th
*)
  in    let ths = mkThms th
        in let infs = mkProof ths th
(*MetisTrace3
        let () = Print.trace Print.ppInt "Proof.proof: size" (length infs)
*)
      in
        infs
      ;;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v =
      let free th_inf =
          match th_inf with
            (_, Axiom lits) -> Literal.Set.freeIn v lits
          | (_, Assume atm) -> Atom.freeIn v atm
          | (th, Subst _) -> Thm.freeIn v th
          | (_, Resolve _) -> false
          | (_, Refl tm) -> Term.freeIn v tm
          | (_, Equality (lit,_,tm)) ->
            Literal.freeIn v lit || Term.freeIn v tm
    in
      List.exists free
    ;;

let freeVars =
      let inc (th_inf,set) =
          Name.Set.union set
          (match th_inf with
             (_, Axiom lits) -> Literal.Set.freeVars lits
           | (_, Assume atm) -> Atom.freeVars atm
           | (th, Subst _) -> Thm.freeVars th
           | (_, Resolve _) -> Name.Set.empty
           | (_, Refl tm) -> Term.freeVars tm
           | (_, Equality (lit,_,tm)) ->
             Name.Set.union (Literal.freeVars lit) (Term.freeVars tm))
    in
      Mlist.foldl inc Name.Set.empty
    ;;

end


(* ========================================================================= *)
(* DERIVED RULES FOR CREATING FIRST ORDER LOGIC THEOREMS                     *)
(* ========================================================================= *)

module Rule = struct

(* ------------------------------------------------------------------------- *)
(* Variable names.                                                           *)
(* ------------------------------------------------------------------------- *)

let xVarName = Name.fromString "x";;
let xVar = Term.Var xVarName;;

let yVarName = Name.fromString "y";;
let yVar = Term.Var yVarName;;

let zVarName = Name.fromString "z";;
let zVar = Term.Var zVarName;;

let xIVarName i = Name.fromString ("x" ^ string_of_int i);;
let xIVar i = Term.Var (xIVarName i);;

let yIVarName i = Name.fromString ("y" ^ string_of_int i);;
let yIVar i = Term.Var (yIVarName i);;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- reflexivity                                                     *)
(*   x = x                                                                   *)
(* ------------------------------------------------------------------------- *)

let reflexivityRule x = Thm.refl x;;

let reflexivity = reflexivityRule xVar;;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------- symmetry                                            *)
(*   ~(x = y) \/ y = x                                                       *)
(* ------------------------------------------------------------------------- *)

let symmetryRule x y =
      let reflTh = reflexivityRule x
      in let reflLit = Thm.destUnit reflTh
      in let eqTh = Thm.equality reflLit [0] y
    in
      Thm.resolve reflLit reflTh eqTh
    ;;

let symmetry = symmetryRule xVar yVar;;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------------------- transitivity                            *)
(*   ~(x = y) \/ ~(y = z) \/ x = z                                           *)
(* ------------------------------------------------------------------------- *)

let transitivity =
      let eqTh = Thm.equality (Literal.mkEq (yVar,zVar)) [0] xVar
    in
      Thm.resolve (Literal.mkEq (yVar,xVar)) symmetry eqTh
    ;;

(* ------------------------------------------------------------------------- *)
(*   x = y \/ C                                                              *)
(* -------------- symEq (x = y)                                              *)
(*   y = x \/ C                                                              *)
(* ------------------------------------------------------------------------- *)

let symEq lit th =
      let (x,y) = Literal.destEq lit
    in
      if Term.equal x y then th
      else
          let sub = Substitute.fromList [(xVarName,x);(yVarName,y)]

          in let symTh = Thm.subst sub symmetry
        in
          Thm.resolve lit th symTh
    ;;

(* ------------------------------------------------------------------------- *)
(* An equation consists of two terms (t,u) plus a theorem (stronger than)    *)
(* t = u \/ C.                                                               *)
(* ------------------------------------------------------------------------- *)

type equation = (Term.term * Term.term) * Thm.thm;;

let equationLiteral (t_u,th) =
      let lit = Literal.mkEq t_u
    in
      if Literal.Set.member lit (Thm.clause th) then Some lit else None
    ;;

let reflEqn t = ((t,t), Thm.refl t);;

let symEqn (((t,u), th) as eqn) =
    if Term.equal t u then eqn
    else
      ((u,t),
       match equationLiteral eqn with
         Some t_u -> symEq t_u th
       | None -> th);;

let transEqn (((x,y), th1) as eqn1) (((_,z), th2) as eqn2) =
    if Term.equal x y then eqn2
    else if Term.equal y z then eqn1
    else if Term.equal x z then reflEqn x
    else
      ((x,z),
       match equationLiteral eqn1 with
         None -> th1
       | Some x_y ->
         match equationLiteral eqn2 with
           None -> th2
         | Some y_z ->
             let sub = Substitute.fromList [(xVarName,x);(yVarName,y);(zVarName,z)]
             in let th = Thm.subst sub transitivity
             in let th = Thm.resolve x_y th1 th
             in let th = Thm.resolve y_z th2 th
           in
             th
           );;

(*MetisDebug
let transEqn = fun eqn1 -> fun eqn2 ->
    transEqn eqn1 eqn2
    handle Failure err ->
      raise Failure ("Rule.transEqn:\neqn1 = " ^ equationToString eqn1 ^
                   "\neqn2 = " ^ equationToString eqn2 ^ "\n" ^ err);;
*)

(* ------------------------------------------------------------------------- *)
(* A conversion takes a term t and either:                                   *)
(* 1. Returns a term u together with a theorem (stronger than) t = u \/ C.   *)
(* 2. Raises an Failure exception.                                             *)
(* ------------------------------------------------------------------------- *)

type conv = Term.term -> Term.term * Thm.thm;;

let allConv tm = (tm, Thm.refl tm);;

let noConv : conv = fun _ -> failwith "noConv";;

(*MetisDebug
let traceConv s conv tm =
    let
      let res as (tm',th) = conv tm
      let () = trace (s ^ ": " ^ Term.toString tm ^ " --> " ^
                      Term.toString tm' ^ " " ^ Thm.toString th ^ "\n")
    in
      res
    end
    handle Failure err ->
      (trace (s ^ ": " ^ Term.toString tm ^ " --> Failure: " ^ err ^ "\n");;
       raise (Failure (s ^ ": " ^ err)));;
*)

let thenConvTrans tm (tm',th1) (tm'',th2) =
      let eqn1 = ((tm,tm'),th1)
      and eqn2 = ((tm',tm''),th2)
      in let (_,th) = transEqn eqn1 eqn2
    in
      (tm'',th)
    ;;

let thenConv conv1 conv2 tm =
      let (tm',_) as res1 = conv1 tm
      in let res2 = conv2 tm'
    in
      thenConvTrans tm res1 res2
    ;;

let orelseConv (conv1 : conv) conv2 tm = try conv1 tm with Failure _ -> conv2 tm;;

let tryConv conv = orelseConv conv allConv;;

let changedConv conv tm =
      let (tm',_) as res = conv tm
    in
      if tm = tm' then failwith "changedConv" else res
    ;;

let rec repeatConv conv tm = tryConv (thenConv conv (repeatConv conv)) tm;;

let flip f = fun x y -> f y x;;

let rec firstConv tm = function
    [] -> failwith "firstConv"
  | [conv] -> conv tm
  | (conv :: convs) -> orelseConv conv (flip firstConv convs) tm;;
let firstConv convs tm = firstConv tm convs;;

let rec everyConv tm = function
    [] -> allConv tm
  | [conv] -> conv tm
  | (conv :: convs) -> thenConv conv (flip everyConv convs) tm;;
let everyConv convs tm = everyConv tm convs;;

let rewrConv (((x,y), eqTh) as eqn) path tm =
    if Term.equal x y then allConv tm
    else if Mlist.null path then (y,eqTh)
    else
        let reflTh = Thm.refl tm
        in let reflLit = Thm.destUnit reflTh
        in let th = Thm.equality reflLit (1 :: path) y
        in let th = Thm.resolve reflLit reflTh th
        in let th =
            match equationLiteral eqn with
              None -> th
            | Some x_y -> Thm.resolve x_y eqTh th
        in let tm' = Term.replace tm (path,y)
      in
        (tm',th)
      ;;

(*MetisDebug
let rewrConv = fun eqn as ((x,y),eqTh) -> fun path -> fun tm ->
    rewrConv eqn path tm
    handle Failure err ->
      raise Failure ("Rule.rewrConv:\nx = " ^ Term.toString x ^
                   "\ny = " ^ Term.toString y ^
                   "\neqTh = " ^ Thm.toString eqTh ^
                   "\npath = " ^ Term.pathToString path ^
                   "\ntm = " ^ Term.toString tm ^ "\n" ^ err);;
*)

let pathConv conv path tm =
      let x = Term.subterm tm path
      in let (y,th) = conv x
    in
      rewrConv ((x,y),th) path tm
    ;;

let subtermConv conv i = pathConv conv [i];;

let subtermsConv conv = function
    (Term.Var _ as tm) -> allConv tm
  | (Term.Fn (_,a) as tm) ->
    everyConv (List.map (subtermConv conv) (Useful.interval 0 (length a))) tm;;

(* ------------------------------------------------------------------------- *)
(* Applying a conversion to every subterm, with some traversal strategy.     *)
(* ------------------------------------------------------------------------- *)

let rec bottomUpConv conv tm =
    thenConv (subtermsConv (bottomUpConv conv)) (repeatConv conv) tm;;

let rec topDownConv conv tm =
    thenConv (repeatConv conv) (subtermsConv (topDownConv conv)) tm;;

let repeatTopDownConv conv =
      let rec f tm = thenConv (repeatConv conv) g tm
      and g tm = thenConv (subtermsConv f) h tm
      and h tm = tryConv (thenConv conv f) tm
    in
      f
    ;;

(*MetisDebug
let repeatTopDownConv = fun conv -> fun tm ->
    repeatTopDownConv conv tm
    handle Failure err -> failwith ("repeatTopDownConv: " ^ err);;
*)

(* ------------------------------------------------------------------------- *)
(* A literule (bad pun) takes a literal L and either:                        *)
(* 1. Returns a literal L' with a theorem (stronger than) ~L \/ L' \/ C.     *)
(* 2. Raises an Failure exception.                                           *)
(* ------------------------------------------------------------------------- *)

type literule = Literal.literal -> Literal.literal * Thm.thm;;

let allLiterule lit = (lit, Thm.assume lit);;

let noLiterule : literule = fun _ -> failwith "noLiterule";;

let thenLiterule literule1 literule2 lit =
      let (lit',th1) as res1 = literule1 lit
      in let (lit'',th2) as res2 = literule2 lit'
    in
      if Literal.equal lit lit' then res2
      else if Literal.equal lit' lit'' then res1
      else if Literal.equal lit lit'' then allLiterule lit
      else
        (lit'',
         if not (Thm.member lit' th1) then th1
         else if not (Thm.negateMember lit' th2) then th2
         else Thm.resolve lit' th1 th2)
    ;;

let orelseLiterule (literule1 : literule) literule2 lit =
    try literule1 lit with Failure _ -> literule2 lit;;

let tryLiterule literule = orelseLiterule literule allLiterule;;

let changedLiterule literule lit =
      let (lit',_) as res = literule lit
    in
      if lit = lit' then failwith "changedLiterule" else res
    ;;

let rec repeatLiterule literule lit =
    tryLiterule (thenLiterule literule (repeatLiterule literule)) lit;;

let rec firstLiterule lit = function
    [] -> failwith "firstLiterule"
  | [literule] -> literule lit
  | (literule :: literules) ->
    orelseLiterule literule (flip firstLiterule literules) lit;;
let firstLiterule literules lit = firstLiterule lit literules;;

let rec everyLiterule lit = function
    [] -> allLiterule lit
  | [literule] -> literule lit
  | (literule :: literules) ->
    thenLiterule literule (flip everyLiterule literules) lit;;
let everyLiterule literules lit = everyLiterule lit literules;;

let rewrLiterule (((x,y),eqTh) as eqn) path lit =
    if Term.equal x y then allLiterule lit
    else
        let th = Thm.equality lit path y
        in let th =
            match equationLiteral eqn with
              None -> th
            | Some x_y -> Thm.resolve x_y eqTh th
        in let lit' = Literal.replace lit (path,y)
      in
        (lit',th)
      ;;

(*MetisDebug
let rewrLiterule = fun eqn -> fun path -> fun lit ->
    rewrLiterule eqn path lit
    handle Failure err ->
      raise Failure ("Rule.rewrLiterule:\neqn = " ^ equationToString eqn ^
                     "\npath = " ^ Term.pathToString path ^
                     "\nlit = " ^ Literal.toString lit ^ "\n" ^ err);;
*)

let pathLiterule conv path lit =
      let tm = Literal.subterm lit path
      in let (tm',th) = conv tm
    in
      rewrLiterule ((tm,tm'),th) path lit
    ;;

let argumentLiterule conv i = pathLiterule conv [i];;

let allArgumentsLiterule conv lit =
    everyLiterule
      (List.map (argumentLiterule conv) (Useful.interval 0 (Literal.arity lit))) lit;;

(* ------------------------------------------------------------------------- *)
(* A rule takes one theorem and either deduces another or raises an Failure  *)
(* exception.                                                                *)
(* ------------------------------------------------------------------------- *)

type rule = Thm.thm -> Thm.thm;;

let allRule : rule = fun th -> th;;

let noRule : rule = fun _ -> failwith "noRule";;

let thenRule (rule1 : rule) (rule2 : rule) th = rule1 (rule2 th);;

let orelseRule (rule1 : rule) rule2 th = try rule1 th with Failure _ -> rule2 th;;

let tryRule rule = orelseRule rule allRule;;

let changedRule rule th =
      let th' = rule th
    in
      if not (Literal.Set.equal (Thm.clause th) (Thm.clause th')) then th'
      else failwith "changedRule"
    ;;

let rec repeatRule rule lit = tryRule (thenRule rule (repeatRule rule)) lit;;

let rec firstRule th = function
    [] -> failwith "firstRule"
  | [rule] -> rule th
  | (rule :: rules) -> orelseRule rule (flip firstRule rules) th;;
let firstRule rules th = firstRule th rules;;

let rec everyRule th = function
    [] -> allRule th
  | [rule] -> rule th
  | (rule :: rules) -> thenRule rule (flip everyRule rules) th;;
let everyRule rules th = everyRule th rules;;

let literalRule literule lit th =
      let (lit',litTh) = literule lit
    in
      if Literal.equal lit lit' then th
      else if not (Thm.negateMember lit litTh) then litTh
      else Thm.resolve lit th litTh
    ;;

(*MetisDebug
let literalRule = fun literule -> fun lit -> fun th ->
    literalRule literule lit th
    handle Failure err ->
      raise Failure ("Rule.literalRule:\nlit = " ^ Literal.toString lit ^
                     "\nth = " ^ Thm.toString th ^ "\n" ^ err);;
*)

let rewrRule eqTh lit path = literalRule (rewrLiterule eqTh path) lit;;

let pathRule conv lit path = literalRule (pathLiterule conv path) lit;;

let literalsRule literule =
      let f (lit,th) =
          if Thm.member lit th then literalRule literule lit th else th
    in
      fun lits -> fun th -> Literal.Set.foldl f th lits
    ;;

let allLiteralsRule literule th = literalsRule literule (Thm.clause th) th;;

let convRule conv = allLiteralsRule (allArgumentsLiterule conv);;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- functionCongruence (f,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   f x0 ... x{n-1} = f y0 ... y{n-1}                                       *)
(* ------------------------------------------------------------------------- *)

let functionCongruence (f,n) =
      let xs = Mlist.tabulate (n,xIVar)
      and ys = Mlist.tabulate (n,yIVar)

      in let cong ((i,yi),(th,lit)) =
            let path = [1;i]
            in let th = Thm.resolve lit th (Thm.equality lit path yi)
            in let lit = Literal.replace lit (path,yi)
          in
            (th,lit)

      in let reflTh = Thm.refl (Term.Fn (f,xs))
      in let reflLit = Thm.destUnit reflTh
    in
      fst (Mlist.foldl cong (reflTh,reflLit) (Mlist.enumerate ys))
    ;;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- relationCongruence (R,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   ~R x0 ... x{n-1} \/ R y0 ... y{n-1}                                     *)
(* ------------------------------------------------------------------------- *)

let relationCongruence (r,n) =
      let xs = Mlist.tabulate (n,xIVar)
      and ys = Mlist.tabulate (n,yIVar)

      in let cong ((i,yi),(th,lit)) =
            let path = [i]
            in let th = Thm.resolve lit th (Thm.equality lit path yi)
            in let lit = Literal.replace lit (path,yi)
          in
            (th,lit)

      in let assumeLit = (false,(r,xs))
      in let assumeTh = Thm.assume assumeLit
    in
      fst (Mlist.foldl cong (assumeTh,assumeLit) (Mlist.enumerate ys))
    ;;

(* ------------------------------------------------------------------------- *)
(*   ~(x = y) \/ C                                                           *)
(* ----------------- symNeq ~(x = y)                                         *)
(*   ~(y = x) \/ C                                                           *)
(* ------------------------------------------------------------------------- *)

let symNeq lit th =
      let (x,y) = Literal.destNeq lit
    in
      if Term.equal x y then th
      else
          let sub = Substitute.fromList [(xVarName,y);(yVarName,x)]
          in let symTh = Thm.subst sub symmetry
        in
          Thm.resolve lit th symTh
    ;;

(* ------------------------------------------------------------------------- *)
(* sym (x = y) = symEq (x = y)  /\  sym ~(x = y) = symNeq ~(x = y)           *)
(* ------------------------------------------------------------------------- *)

let sym ((pol,_) as lit) th = if pol then symEq lit th else symNeq lit th;;

(* ------------------------------------------------------------------------- *)
(*   ~(x = x) \/ C                                                           *)
(* ----------------- removeIrrefl                                            *)
(*         C                                                                 *)
(*                                                                           *)
(* where all irreflexive equalities.                                         *)
(* ------------------------------------------------------------------------- *)

let removeIrrefl th =
  let irrefl = function
      ((true,_),th) -> th
    | ((false,atm) as lit, th) ->
      match Useful.total Atom.destRefl atm with
        Some x -> Thm.resolve lit th (Thm.refl x)
      | None -> th
in
  Literal.Set.foldl irrefl th (Thm.clause th);;

(* ------------------------------------------------------------------------- *)
(*   x = y \/ y = x \/ C                                                     *)
(* ----------------------- removeSym                                         *)
(*       x = y \/ C                                                          *)
(*                                                                           *)
(* where all duplicate copies of equalities and disequalities are removed.   *)
(* ------------------------------------------------------------------------- *)

let removeSym th =
  let rem ((pol,atm) as lit, (eqs,th)) =
      match Useful.total Atom.sym atm with
        None -> (eqs, th)
      | Some atm' ->
        if Literal.Set.member lit eqs then
          (eqs, if pol then symEq lit th else symNeq lit th)
        else
          (Literal.Set.add eqs (pol,atm'), th)
in
      snd (Literal.Set.foldl rem (Literal.Set.empty,th) (Thm.clause th));;

(* ------------------------------------------------------------------------- *)
(*   ~(v = t) \/ C                                                           *)
(* ----------------- expandAbbrevs                                           *)
(*      C[t/v]                                                               *)
(*                                                                           *)
(* where t must not contain any occurrence of the variable v.                *)
(* ------------------------------------------------------------------------- *)

let rec expandAbbrevs th =
  let expand lit =
        let (x,y) = Literal.destNeq lit
        in let _ = Term.isTypedVar x || Term.isTypedVar y ||
                failwith "Rule.expandAbbrevs: no vars"
        in let _ = not (Term.equal x y) ||
                failwith "Rule.expandAbbrevs: equal vars"
      in
        Substitute.unify Substitute.empty x y
in
      match Literal.Set.firstl (Useful.total expand) (Thm.clause th) with
        None -> removeIrrefl th
      | Some sub -> expandAbbrevs (Thm.subst sub th);;

(* ------------------------------------------------------------------------- *)
(* simplify = isTautology + expandAbbrevs + removeSym                        *)
(* ------------------------------------------------------------------------- *)

let rec simplify th =
    if Thm.isTautology th then None
    else
        let th' = th
        in let th' = expandAbbrevs th'
        in let th' = removeSym th'
      in
        if Thm.equal th th' then Some th else simplify th'
      ;;

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- freshVars                                                        *)
(*   C[s]                                                                    *)
(*                                                                           *)
(* where s is a renaming substitution chosen so that all of the variables in *)
(* C are replaced by fresh variables.                                        *)
(* ------------------------------------------------------------------------- *)

let freshVars th = Thm.subst (Substitute.freshVars (Thm.freeVars th)) th;;

(* ------------------------------------------------------------------------- *)
(*               C                                                           *)
(* ---------------------------- factor                                       *)
(*   C_s_1, C_s_2, ..., C_s_n                                                *)
(*                                                                           *)
(* where each s_i is a substitution that factors C, meaning that the theorem *)
(*                                                                           *)
(*   C_s_i = (removeIrrefl o removeSym o Thm.subst s_i) C                    *)
(*                                                                           *)
(* has fewer literals than C.                                                *)
(*                                                                           *)
(* Also, if s is any substitution that factors C, then one of the s_i will   *)
(* result in a theorem C_s_i that strictly subsumes the theorem C_s.         *)
(* ------------------------------------------------------------------------- *)

  type edge =
      Factor_edge of Atom.atom * Atom.atom
    | Refl_edge of Term.term * Term.term;;

  type joinStatus =
      Joined
    | Joinable of Substitute.subst
    | Apart;;

  let joinEdge sub edge =
        let result =
            match edge with
              Factor_edge (atm,atm') -> Useful.total (Atom.unify sub atm) atm'
            | Refl_edge (tm,tm') -> Useful.total (Substitute.unify sub tm) tm'
      in
        match result with
          None -> Apart
        | Some sub' ->
          if sub == sub' then Joined else Joinable sub'
      ;;

  let updateApart sub =
        let rec update acc = function
            [] -> Some acc
          | (edge :: edges) ->
            match joinEdge sub edge with
              Joined -> None
            | Joinable _ -> update (edge :: acc) edges
            | Apart -> update acc edges
      in
        update []
      ;;

  let addFactorEdge (pol,atm) ((pol',atm'),acc) =
      if pol <> pol' then acc
      else
          let edge = Factor_edge (atm,atm')
        in
          match joinEdge Substitute.empty edge with
            Joined -> raise (Useful.Bug "addFactorEdge: joined")
          | Joinable sub -> (sub,edge) :: acc
          | Apart -> acc
        ;;

  let addReflEdge = function
      ((false,_), acc) -> acc
    | ((true,atm), acc) ->
        let edge = let (x,y) = (Atom.destEq atm) in Refl_edge (x,y)
      in
        match joinEdge Substitute.empty edge with
          Joined -> raise (Useful.Bug "addRefl: joined")
        | Joinable _ -> edge :: acc
        | Apart -> acc
      ;;
  let addReflEdge = curry addReflEdge;;

  let addIrreflEdge = function
      ((true,_), acc) -> acc
    | ((false,atm), acc) ->
        let edge = let (x,y) = (Atom.destEq atm) in Refl_edge (x,y)
      in
        match joinEdge Substitute.empty edge with
          Joined -> raise (Useful.Bug "addRefl: joined")
        | Joinable sub -> (sub,edge) :: acc
        | Apart -> acc
      ;;
  let addIrreflEdge = curry addIrreflEdge;;

  let rec init_edges acc apart = function
      [] ->
        let init ((apart,sub,edge),(edges,acc)) =
            (edge :: edges, (apart,sub,edges) :: acc)
      in
        snd (Mlist.foldl init ([],[]) acc)
    | ((sub,edge) :: sub_edges) ->
(*MetisDebug
        let () = if not (Substitute.null sub) then ()
                 else raise Useful.Bug "Rule.factor.init_edges: empty subst"
*)
        let (acc,apart) =
            match updateApart sub apart with
              Some apart' -> ((apart',sub,edge) :: acc, edge :: apart)
            | None -> (acc,apart)
      in
        init_edges acc apart sub_edges
      ;;

  let rec mk_edges apart sub_edges = function
      [] -> init_edges [] apart sub_edges
    | (lit :: lits) ->
        let sub_edges = Mlist.foldl (addFactorEdge lit) sub_edges lits

        in let (apart,sub_edges) =
            match Useful.total Literal.sym lit with
              None -> (apart,sub_edges)
            | Some lit' ->
                let apart = addReflEdge lit apart
                in let sub_edges = addIrreflEdge lit sub_edges
                in let sub_edges = Mlist.foldl (addFactorEdge lit') sub_edges lits
              in
                (apart,sub_edges)
      in
        mk_edges apart sub_edges lits
      ;;

  let rec fact acc = function
      [] -> acc
    | ((_,sub,[]) :: others) -> fact (sub :: acc) others
    | ((apart, sub, edge :: edges) :: others) ->
        let others =
            match joinEdge sub edge with
              Joinable sub' ->
                let others = (edge :: apart, sub, edges) :: others
              in
                (match updateApart sub' apart with
                  None -> others
                | Some apart' -> (apart',sub',edges) :: others)
            | _ -> (apart,sub,edges) :: others
      in
        fact acc others
      ;;

  let factor' cl =
(*MetisTrace6
        let () = Print.trace Literal.Set.pp "Rule.factor': cl" cl
*)
        let edges = mk_edges [] [] (Literal.Set.toList cl)
(*MetisTrace6
        let ppEdgesSize = Print.ppMap length Print.ppInt
        let ppEdgel = Print.ppList ppEdge
        let ppEdges = Print.ppList (Print.ppTriple ppEdgel Substitute.pp ppEdgel)
        let () = Print.trace ppEdgesSize "Rule.factor': |edges|" edges
        let () = Print.trace ppEdges "Rule.factor': edges" edges
*)
        in let result = fact [] edges
(*MetisTrace6
        let ppResult = Print.ppList Substitute.pp
        let () = Print.trace ppResult "Rule.factor': result" result
*)
      in
        result
      ;;

let factor th =
      let fact sub = removeIrrefl (removeSym (Thm.subst sub th))
    in
      List.map fact (factor' (Thm.clause th))
    ;;


end

(* ========================================================================= *)
(* RANDOM FINITE MODELS                                                      *)
(* ========================================================================= *)

module Model = struct

(* ------------------------------------------------------------------------- *)
(* Constants.                                                                *)
(* ------------------------------------------------------------------------- *)

let maxSpace = 1000;;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let multInt x y =
  let m = int_of_float (floor (float_sqrt (float_of_int max_int))) in
  if x <= m && y <= m then Some (x * y) else None;;

  let rec iexp x y acc =
      if y mod 2 = 0 then iexp' x y acc
      else
        match multInt acc x with
          Some acc -> iexp' x y acc
        | None -> None

  and iexp' x y acc =
      if y = 1 then Some acc
      else
          let y = y / 2
        in
          match multInt x x with
            Some x -> iexp x y acc
          | None -> None
        ;;

  let expInt x y =
      if y <= 1 then
        if y = 0 then Some 1
        else if y = 1 then Some x
        else raise (Useful.Bug "expInt: negative exponent")
      else if x <= 1 then
        if 0 <= x then Some x
        else raise (Useful.Bug "expInt: negative exponand")
      else iexp x y 1;;

let boolToInt = function
    true -> 1
  | false -> 0;;

let intToBool = function
    1 -> true
  | 0 -> false
  | _ -> raise (Useful.Bug "Model.intToBool");;

let minMaxInterval i j = Useful.interval i (1 + j - i);;

(* ------------------------------------------------------------------------- *)
(* Model size.                                                               *)
(* ------------------------------------------------------------------------- *)

type size = {size : int};;

(* ------------------------------------------------------------------------- *)
(* A model of size N has integer elements 0...N-1.                           *)
(* ------------------------------------------------------------------------- *)

type element = int;;

let zeroElement = 0;;

let incrementElement {size = n} i =
      let i = i + 1
    in
      if i = n then None else Some i
    ;;

let elementListSpace {size = n} arity =
    match expInt n arity with
      None -> None
    | Some m as s -> if m <= maxSpace then s else None;;

let elementListIndex {size = n} =
      let rec f acc elts =
          match elts with
            [] -> acc
          | elt :: elts -> f (n * acc + elt) elts
    in
      f 0
    ;;

(* ------------------------------------------------------------------------- *)
(* The parts of the model that are fixed.                                    *)
(* ------------------------------------------------------------------------- *)

type fixedFunction = size -> element list -> element option;;

type fixedRelation = size -> element list -> bool option;;

type fixed =
      {functions : fixedFunction Name_arity.Map.map;
       relations : fixedRelation Name_arity.Map.map};;

let uselessFixedFunction : fixedFunction = K (K None);;

let uselessFixedRelation : fixedRelation = K (K None);;

let emptyFunctions : fixedFunction Name_arity.Map.map = Name_arity.Map.newMap ();;

let emptyRelations : fixedRelation Name_arity.Map.map = Name_arity.Map.newMap ();;

let fixed0 f sz elts =
    match elts with
      [] -> f sz
    | _ -> raise (Useful.Bug "Model.fixed0: wrong arity");;

let fixed1 f sz elts =
    match elts with
      [x] -> f sz x
    | _ -> raise (Useful.Bug "Model.fixed1: wrong arity");;

let fixed2 f sz elts =
    match elts with
      [x;y] -> f sz x y
    | _ -> raise (Useful.Bug "Model.fixed2: wrong arity");;

let emptyFixed =
      let fns = emptyFunctions
      and rels = emptyRelations
    in
        {functions = fns;
         relations = rels}
    ;;

let peekFunctionFixed fix name_arity =
      let {functions = fns} = fix
    in
      Name_arity.Map.peek fns name_arity
    ;;

let peekRelationFixed fix name_arity =
      let {relations = rels} = fix
    in
      Name_arity.Map.peek rels name_arity
    ;;

let getFunctionFixed fix name_arity =
    match peekFunctionFixed fix name_arity with
      Some f -> f
    | None -> uselessFixedFunction;;

let getRelationFixed fix name_arity =
    match peekRelationFixed fix name_arity with
      Some rel -> rel
    | None -> uselessFixedRelation;;

let insertFunctionFixed fix name_arity_fun =
      let {functions = fns; relations = rels} = fix

      in let fns = Name_arity.Map.insert fns name_arity_fun
    in
        {functions = fns;
         relations = rels}
    ;;

let insertRelationFixed fix name_arity_rel =
      let {functions = fns; relations = rels} = fix

      in let rels = Name_arity.Map.insert rels name_arity_rel
    in
        {functions = fns;
         relations = rels}
    ;;

  let union _ = raise (Useful.Bug "Model.unionFixed: nameArity clash");;
  let unionFixed fix1 fix2 =
        let {functions = fns1; relations = rels1} = fix1
        and {functions = fns2; relations = rels2} = fix2

        in let fns = Name_arity.Map.union union fns1 fns2

        in let rels = Name_arity.Map.union union rels1 rels2
      in
          {functions = fns;
           relations = rels}
      ;;

let unionListFixed =
      let union (fix,acc) = unionFixed acc fix
    in
      Mlist.foldl union emptyFixed
    ;;

  let hasTypeFn _ elts =
      match elts with
        [x;_] -> Some x
      | _ -> raise (Useful.Bug "Model.hasTypeFn: wrong arity");;

  let eqRel _ elts =
      match elts with
        [x;y] -> Some (x = y)
      | _ -> raise (Useful.Bug "Model.eqRel: wrong arity");;

  let basicFixed =
        let fns = Name_arity.Map.singleton (Term.hasTypeFunction,hasTypeFn)

        in let rels = Name_arity.Map.singleton (Atom.eqRelation,eqRel)
      in
          {functions = fns;
           relations = rels}
      ;;

(* ------------------------------------------------------------------------- *)
(* Renaming fixed model parts.                                               *)
(* ------------------------------------------------------------------------- *)

type fixedMap =
     {functionMap : Name.name Name_arity.Map.map;
      relationMap : Name.name Name_arity.Map.map};;

let mapFixed fixMap fix =
      let {functionMap = fnMap; relationMap = relMap} = fixMap
      and {functions = fns; relations = rels} = fix

      in let fns = Name_arity.Map.compose fnMap fns

      in let rels = Name_arity.Map.compose relMap rels
    in
        {functions = fns;
         relations = rels}
    ;;


(* ------------------------------------------------------------------------- *)
(* Standard fixed model parts.                                               *)
(* ------------------------------------------------------------------------- *)

(* Projections *)

let projectionMin = 1
and projectionMax = 9;;

let projectionList = minMaxInterval projectionMin projectionMax;;

let projectionName i =
      let _ = projectionMin <= i ||
              raise (Useful.Bug "Model.projectionName: less than projectionMin")

      in let _ = i <= projectionMax ||
              raise (Useful.Bug "Model.projectionName: greater than projectionMax")
    in
      Name.fromString ("project" ^ string_of_int i)
    ;;

let projectionFn i _ elts = Some (List.nth elts (i - 1));;

let arityProjectionFixed arity =
      let mkProj i = ((projectionName i, arity), projectionFn i)

      in let rec addProj i acc =
          if i > arity then acc
          else addProj (i + 1) (Name_arity.Map.insert acc (mkProj i))

      in let fns = addProj projectionMin emptyFunctions

      in let rels = emptyRelations
    in
        {functions = fns;
         relations = rels}
    ;;

let projectionFixed =
    unionListFixed (List.map arityProjectionFixed projectionList);;

(* Arithmetic *)

let numeralMin = -100
and numeralMax = 100;;

let numeralList = minMaxInterval numeralMin numeralMax;;

let numeralName i =
      let _ = numeralMin <= i ||
              raise (Useful.Bug "Model.numeralName: less than numeralMin")

      in let _ = i <= numeralMax ||
              raise (Useful.Bug "Model.numeralName: greater than numeralMax")

      in let s = if i < 0 then "negative" ^ string_of_int (-i) else string_of_int i
    in
      Name.fromString s
    ;;

let addName = Name.fromString "+"
and divName = Name.fromString "div"
and dividesName = Name.fromString "divides"
and evenName = Name.fromString "even"
and expName = Name.fromString "exp"
and geName = Name.fromString ">="
and gtName = Name.fromString ">"
and isZeroName = Name.fromString "isZero"
and leName = Name.fromString "<="
and ltName = Name.fromString "<"
and modName = Name.fromString "mod"
and multName = Name.fromString "*"
and negName = Name.fromString "~"
and oddName = Name.fromString "odd"
and preName = Name.fromString "pre"
and subName = Name.fromString "-"
and sucName = Name.fromString "suc";;

  (* Support *)

  let modN {size = n} x = x mod n;;

  let oneN sz = modN sz 1;;

  let multN sz (x,y) = modN sz (x * y);;

  (* Functions *)

  let numeralFn i sz = Some (modN sz i);;

  let addFn sz x y = Some (modN sz (x + y));;

  let divFn {size = n} x y =
        let y = if y = 0 then n else y
      in
        Some (x / y)
      ;;

  let expFn sz x y = Some (Useful.exp (multN sz) x y (oneN sz));;

  let modFn {size = n} x y =
        let y = if y = 0 then n else y
      in
        Some (x mod y)
      ;;

  let multFn sz x y = Some (multN sz (x,y));;

  let negFn {size = n} x = Some (if x = 0 then 0 else n - x);;

  let preFn {size = n} x = Some (if x = 0 then n - 1 else x - 1);;

  let subFn {size = n} x y = Some (if x < y then n + x - y else x - y);;

  let sucFn {size = n} x = Some (if x = n - 1 then 0 else x + 1);;

  (* Relations *)

  let dividesRel _ x y = Some (Useful.divides x y);;

  let evenRel _ x = Some (x mod 2 = 0);;

  let geRel _ x y = Some (x >= y);;

  let gtRel _ x y = Some (x > y);;

  let isZeroRel _ x = Some (x = 0);;

  let leRel _ x y = Some (x <= y);;

  let ltRel _ x y = Some (x < y);;

  let oddRel _ x = Some (x mod 2 = 1);;

  let modularFixed =
        let fns =
            Name_arity.Map.fromList
              (List.map (fun i -> ((numeralName i,0), fixed0 (numeralFn i)))
                 numeralList @
               [((addName,2), fixed2 addFn);
                ((divName,2), fixed2 divFn);
                ((expName,2), fixed2 expFn);
                ((modName,2), fixed2 modFn);
                ((multName,2), fixed2 multFn);
                ((negName,1), fixed1 negFn);
                ((preName,1), fixed1 preFn);
                ((subName,2), fixed2 subFn);
                ((sucName,1), fixed1 sucFn)])

        in let rels =
            Name_arity.Map.fromList
              [((dividesName,2), fixed2 dividesRel);
               ((evenName,1), fixed1 evenRel);
               ((geName,2), fixed2 geRel);
               ((gtName,2), fixed2 gtRel);
               ((isZeroName,1), fixed1 isZeroRel);
               ((leName,2), fixed2 leRel);
               ((ltName,2), fixed2 ltRel);
               ((oddName,1), fixed1 oddRel)]
      in
          {functions = fns;
           relations = rels}
      ;;

  (* Support *)

  let cutN {size = n} x = if x >= n then n - 1 else x;;

  let oneN sz = cutN sz 1;;

  let multN sz (x,y) = cutN sz (x * y);;

  (* Functions *)

  let numeralFn i sz = if i < 0 then None else Some (cutN sz i);;

  let addFn sz x y = Some (cutN sz (x + y));;

  let divFn _ x y = if y = 0 then None else Some (x / y);;

  let expFn sz x y = Some (Useful.exp (multN sz) x y (oneN sz));;

  let modFn {size = n} x y =
      if y = 0 || x = n - 1 then None else Some (x mod y);;

  let multFn sz x y = Some (multN sz (x,y));;

  let negFn _ x = if x = 0 then Some 0 else None;;

  let preFn _ x = if x = 0 then None else Some (x - 1);;

  let subFn {size = n} x y =
      if y = 0 then Some x
      else if x = n - 1 || x < y then None
      else Some (x - y);;

  let sucFn sz x = Some (cutN sz (x + 1));;

  (* Relations *)

  let dividesRel {size = n} x y =
      if x = 1 || y = 0 then Some true
      else if x = 0 then Some false
      else if y = n - 1 then None
      else Some (Useful.divides x y);;

  let evenRel {size = n} x =
      if x = n - 1 then None else Some (x mod 2 = 0);;

  let geRel {size = n} y x =
      if x = n - 1 then if y = n - 1 then None else Some false
      else if y = n - 1 then Some true else Some (x <= y);;

  let gtRel {size = n} y x =
      if x = n - 1 then if y = n - 1 then None else Some false
      else if y = n - 1 then Some true else Some (x < y);;

  let isZeroRel _ x = Some (x = 0);;

  let leRel {size = n} x y =
      if x = n - 1 then if y = n - 1 then None else Some false
      else if y = n - 1 then Some true else Some (x <= y);;

  let ltRel {size = n} x y =
      if x = n - 1 then if y = n - 1 then None else Some false
      else if y = n - 1 then Some true else Some (x < y);;

  let oddRel {size = n} x =
      if x = n - 1 then None else Some (x mod 2 = 1);;

  let overflowFixed =
        let fns =
            Name_arity.Map.fromList
              (List.map (fun i -> ((numeralName i,0), fixed0 (numeralFn i)))
                 numeralList @
               [((addName,2), fixed2 addFn);
                ((divName,2), fixed2 divFn);
                ((expName,2), fixed2 expFn);
                ((modName,2), fixed2 modFn);
                ((multName,2), fixed2 multFn);
                ((negName,1), fixed1 negFn);
                ((preName,1), fixed1 preFn);
                ((subName,2), fixed2 subFn);
                ((sucName,1), fixed1 sucFn)])

        in let rels =
            Name_arity.Map.fromList
              [((dividesName,2), fixed2 dividesRel);
               ((evenName,1), fixed1 evenRel);
               ((geName,2), fixed2 geRel);
               ((gtName,2), fixed2 gtRel);
               ((isZeroName,1), fixed1 isZeroRel);
               ((leName,2), fixed2 leRel);
               ((ltName,2), fixed2 ltRel);
               ((oddName,1), fixed1 oddRel)]
      in
          {functions = fns;
           relations = rels}
      ;;

(* Sets *)

let cardName = Name.fromString "card"
and complementName = Name.fromString "complement"
and differenceName = Name.fromString "difference"
and emptyName = Name.fromString "empty"
and memberName = Name.fromString "member"
and insertName = Name.fromString "insert"
and intersectName = Name.fromString "intersect"
and singletonName = Name.fromString "singleton"
and subsetName = Name.fromString "subset"
and symmetricDifferenceName = Name.fromString "symmetricDifference"
and unionName = Name.fromString "union"
and universeName = Name.fromString "universe";;

  (* Support *)

  let eltN {size = n} =
        let rec f acc = function
            0 -> acc
          | x -> f (acc + 1) (x / 2)
      in
        f (-1) n
      ;;

  let posN i = Word.shiftLeft (1, Word.fromInt i);;

  let univN sz = Word.minus (posN (eltN sz), 1);;

  let setN sz x = Word.andb (Word.fromInt x, univN sz);;

  (* Functions *)

  let cardFn sz x =
        let rec f acc = function
            0 -> acc
          | s ->
              let acc = if Word.andb (s,1) = 0 then acc else acc + 1
            in
              f acc (Word.shiftRight (s,1))
      in
        Some (f (setN sz x) 0)
      ;;

  let complementFn sz x = Some (Word.toInt (Word.xorb (univN sz, setN sz x)));;

  let differenceFn sz x y =
        let x = setN sz x
        and y = setN sz y
      in
        Some (Word.toInt (Word.andb (x, Word.notb y)))
      ;;

  let emptyFn _ = Some 0;;

  let insertFn sz x y =
        let x = x mod eltN sz
        and y = setN sz y
      in
        Some (Word.toInt (Word.orb (posN x, y)))
      ;;

  let intersectFn sz x y =
      Some (Word.toInt (Word.andb (setN sz x, setN sz y)));;

  let singletonFn sz x =
        let x = x mod eltN sz
      in
        Some (Word.toInt (posN x))
      ;;

  let symmetricDifferenceFn sz x y =
        let x = setN sz x
        and y = setN sz y
      in
        Some (Word.toInt (Word.xorb (x,y)))
      ;;

  let unionFn sz x y =
      Some (Word.toInt (Word.orb (setN sz x, setN sz y)));;

  let universeFn sz = Some (Word.toInt (univN sz));;

  (* Relations *)

  let memberRel sz x y =
        let x = x mod eltN sz
        and y = setN sz y
      in
        Some (Word.andb (posN x, y) <> 0)
      ;;

  let subsetRel sz x y =
        let x = setN sz x
        and y = setN sz y
      in
        Some (Word.andb (x, Word.notb y) = 0)
      ;;

  let setFixed =
        let fns =
            Name_arity.Map.fromList
              [((cardName,1), fixed1 cardFn);
               ((complementName,1), fixed1 complementFn);
               ((differenceName,2), fixed2 differenceFn);
               ((emptyName,0), fixed0 emptyFn);
               ((insertName,2), fixed2 insertFn);
               ((intersectName,2), fixed2 intersectFn);
               ((singletonName,1), fixed1 singletonFn);
               ((symmetricDifferenceName,2), fixed2 symmetricDifferenceFn);
               ((unionName,2), fixed2 unionFn);
               ((universeName,0), fixed0 universeFn)]

        in let rels =
            Name_arity.Map.fromList
              [((memberName,2), fixed2 memberRel);
               ((subsetName,2), fixed2 subsetRel)]
      in
          {functions = fns;
           relations = rels}
      ;;

(* Lists *)

let appendName = Name.fromString "@"
and consName = Name.fromString "::"
and lengthName = Name.fromString "length"
and nilName = Name.fromString "nil"
and nullName = Name.fromString "null"
and tailName = Name.fromString "tail";;

  let baseFix =
        let fix = unionFixed projectionFixed overflowFixed

        in let sucFn = getFunctionFixed fix (sucName,1)

        in let suc2Fn sz _ x = sucFn sz [x]
      in
        insertFunctionFixed fix ((sucName,2), fixed2 suc2Fn)
      ;;

  let fixMap =
      {functionMap = Name_arity.Map.fromList
                       [((appendName,2),addName);
                        ((consName,2),sucName);
                        ((lengthName,1), projectionName 1);
                        ((nilName,0), numeralName 0);
                        ((tailName,1),preName)];
       relationMap = Name_arity.Map.fromList
                       [((nullName,1),isZeroName)]};;

  let listFixed = mapFixed fixMap baseFix;;

(* ------------------------------------------------------------------------- *)
(* Valuations.                                                               *)
(* ------------------------------------------------------------------------- *)

type valuation = Valuation of element Name.Map.map;;

let emptyValuation = Valuation (Name.Map.newMap ());;

let insertValuation (Valuation m) v_i = Valuation (Name.Map.insert m v_i);;

let peekValuation (Valuation m) v = Name.Map.peek m v;;

let constantValuation i =
      let add (v,v') = insertValuation v' (v,i)
    in
      Name.Set.foldl add emptyValuation
    ;;

let zeroValuation = constantValuation zeroElement;;

let getValuation v' v =
    match peekValuation v' v with
      Some i -> i
    | None -> failwith "Model.getValuation: incomplete valuation";;

let randomValuation {size = n} vs =
      let f (v,v') = insertValuation v' (v, Random.int n)
    in
      Name.Set.foldl f emptyValuation vs
    ;;

let incrementValuation n vars =
      let rec inc vs v' =
          match vs with
            [] -> None
          | v :: vs ->
              let (carry,i) =
                  match incrementElement n (getValuation v' v) with
                    Some i -> (false,i)
                  | None -> (true,zeroElement)

              in let v' = insertValuation v' (v,i)
            in
              if carry then inc vs v' else Some v'
    in
      inc (Name.Set.toList vars)
    ;;

let foldValuation n vars f =
      let inc = incrementValuation n vars

      in let rec fold v' acc =
            let acc = f (v',acc)
          in
            match inc v' with
              None -> acc
            | Some v' -> fold v' acc

      in let zero = zeroValuation vars
    in
      fold zero
    ;;

(* ------------------------------------------------------------------------- *)
(* A type of random finite mapping Z^n -> Z.                                 *)
(* ------------------------------------------------------------------------- *)

let cUNKNOWN = -1;;

type table =
    Forgetful_table
  | Array_table of int array;;

let newTable n arity =
    match elementListSpace {size = n} arity with
      None -> Forgetful_table
    | Some space -> Array_table (Array.make space cUNKNOWN);;


  let randomResult r = Random.int r;;
  let lookupTable n vR table elts =
      match table with
        Forgetful_table -> randomResult vR
      | Array_table a ->
          let i = elementListIndex {size = n} elts

          in let r = Array.get a i
        in
          if r <> cUNKNOWN then r
          else
              let r = randomResult vR

              in let () = Array.set a i r
            in
              r
        ;;

let updateTable n table (elts,r) =
    match table with
      Forgetful_table -> ()
    | Array_table a ->
        let i = elementListIndex {size = n} elts

        in let () = Array.set a i r
      in
        ()
      ;;

(* ------------------------------------------------------------------------- *)
(* A type of random finite mappings name * arity -> Z^arity -> Z.            *)
(* ------------------------------------------------------------------------- *)

type tables =
      {domainSize : int;
       rangeSize : int;
       tableMap : table Name_arity.Map.map ref};;

let newTables n vR =
      {domainSize = n;
       rangeSize = vR;
       tableMap = ref (Name_arity.Map.newMap ())};;

let getTables tables n_a =
      let {domainSize = n; rangeSize = _; tableMap = tm} = tables

      in let m = !tm
    in
      match Name_arity.Map.peek m n_a with
        Some t -> t
      | None ->
          let (_,a) = n_a

          in let t = newTable n a

          in let m = Name_arity.Map.insert m (n_a,t)

          in let () = tm := m
        in
          t
    ;;

let lookupTables tables (n,elts) =
      let {domainSize = vN; rangeSize = vR} = tables

      in let a = length elts

      in let table = getTables tables (n,a)
    in
      lookupTable vN vR table elts
    ;;

let updateTables tables ((n,elts),r) =
      let {domainSize = vN} = tables

      in let a = length elts

      in let table = getTables tables (n,a)
    in
      updateTable vN table (elts,r)
    ;;

(* ------------------------------------------------------------------------- *)
(* A type of random finite models.                                           *)
(* ------------------------------------------------------------------------- *)

type parameters = {sizep : int; fixed : fixed};;

type model =
      {sizem : int;
       fixedFunctions : (element list -> element option) Name_arity.Map.map;
       fixedRelations : (element list -> bool option) Name_arity.Map.map;
       randomFunctions : tables;
       randomRelations : tables};;

let newModel {sizep = vN; fixed = fixed} =
      let {functions = fns; relations = rels} = fixed

      in let fixFns = Name_arity.Map.transform (fun f -> f {size = vN}) fns
      and fixRels = Name_arity.Map.transform (fun r -> r {size = vN}) rels

      in let rndFns = newTables vN vN
      and rndRels = newTables vN 2
    in
        {sizem = vN;
         fixedFunctions = fixFns;
         fixedRelations = fixRels;
         randomFunctions = rndFns;
         randomRelations = rndRels}
    ;;

let msize ({sizem = vN}) = vN;;
let psize ({sizep = vN}) = vN;;

let peekFixedFunction vM (n,elts) =
      let {fixedFunctions = fixFns} = vM
    in
      match Name_arity.Map.peek fixFns (n, length elts) with
        None -> None
      | Some fixFn -> fixFn elts
    ;;

let isFixedFunction vM n_elts = Option.is_some (peekFixedFunction vM n_elts);;

let peekFixedRelation vM (n,elts) =
      let {fixedRelations = fixRels} = vM
    in
      match Name_arity.Map.peek fixRels (n, length elts) with
        None -> None
      | Some fixRel -> fixRel elts
    ;;

let isFixedRelation vM n_elts = Option.is_some (peekFixedRelation vM n_elts);;

(* A default model *)

let defaultSize = 8;;

let defaultFixed =
    unionListFixed
      [basicFixed;
       projectionFixed;
       modularFixed;
       setFixed;
       listFixed];;

let default = {sizep = defaultSize; fixed = defaultFixed};;

(* ------------------------------------------------------------------------- *)
(* Taking apart terms to interpret them.                                     *)
(* ------------------------------------------------------------------------- *)

let destTerm tm =
    match tm with
      Term.Var _ -> tm
    | Term.Fn f_tms ->
      match Term.stripApp tm with
        (_,[]) -> tm
      | (Term.Var _ as v, tms) -> Term.Fn (Term.appName, v :: tms)
      | (Term.Fn (f,tms), tms') -> Term.Fn (f, tms @ tms');;

(* ------------------------------------------------------------------------- *)
(* Interpreting terms and formulas in the model.                             *)
(* ------------------------------------------------------------------------- *)

let interpretFunction vM n_elts =
    match peekFixedFunction vM n_elts with
      Some r -> r
    | None ->
        let {randomFunctions = rndFns} = vM
      in
        lookupTables rndFns n_elts
      ;;

let interpretRelation vM n_elts =
    match peekFixedRelation vM n_elts with
      Some r -> r
    | None ->
        let {randomRelations = rndRels} = vM
      in
        intToBool (lookupTables rndRels n_elts)
      ;;

let interpretTerm vM vV =
      let rec interpret tm =
          match destTerm tm with
            Term.Var v -> getValuation vV v
          | Term.Fn (f,tms) -> interpretFunction vM (f, List.map interpret tms)
    in
      interpret
    ;;

let interpretAtom vM vV (r,tms) =
    interpretRelation vM (r, List.map (interpretTerm vM vV) tms);;

let interpretFormula vM =
      let vN = msize vM

      in let rec interpret vV fm =
          match fm with
            Formula.True -> true
          | Formula.False -> false
          | Formula.Atom atm -> interpretAtom vM vV atm
          | Formula.Not p -> not (interpret vV p)
          | Formula.Or (p,q) -> interpret vV p || interpret vV q
          | Formula.And (p,q) -> interpret vV p && interpret vV q
          | Formula.Imp (p,q) -> interpret vV (Formula.Or (Formula.Not p, q))
          | Formula.Iff (p,q) -> interpret vV p = interpret vV q
          | Formula.Forall (v,p) -> interpret' vV p v vN
          | Formula.Exists (v,p) ->
            interpret vV (Formula.Not (Formula.Forall (v, Formula.Not p)))

      and interpret' vV fm v i =
          i = 0 ||
            let i = i - 1
            in let vV' = insertValuation vV (v,i)
          in
            interpret vV' fm && interpret' vV fm v i

    in
      interpret
    ;;

let interpretLiteral vM vV (pol,atm) =
      let b = interpretAtom vM vV atm
    in
      if pol then b else not b
    ;;

let interpretClause vM vV cl = Literal.Set.exists (interpretLiteral vM vV) cl;;

(* ------------------------------------------------------------------------- *)
(* Check whether random groundings of a formula are true in the model.       *)
(* Note: if it's cheaper, a systematic check will be performed instead.      *)
(* ------------------------------------------------------------------------- *)

let check interpret maxChecks vM fv x =
      let vN = msize vM

      in let score (vV,(vT,vF)) =
          if interpret vM vV x then (vT + 1, vF) else (vT, vF + 1)

      in let randomCheck acc = score (randomValuation {size = vN} fv, acc)

      in let maxChecks =
          match maxChecks with
            None -> maxChecks
          | Some m ->
            match expInt vN (Name.Set.size fv) with
              Some n -> if n <= m then None else maxChecks
            | None -> maxChecks
    in
      match maxChecks with
        Some m -> funpow m randomCheck (0, 0)
      | None -> foldValuation {size = vN} fv score (0, 0)
    ;;

let checkAtom maxChecks vM atm =
    check interpretAtom maxChecks vM (Atom.freeVars atm) atm;;

let checkFormula maxChecks vM fm =
    check interpretFormula maxChecks vM (Formula.freeVars fm) fm;;

let checkLiteral maxChecks vM lit =
    check interpretLiteral maxChecks vM (Literal.freeVars lit) lit;;

let checkClause maxChecks vM cl =
    check interpretClause maxChecks vM (Literal.Set.freeVars cl) cl;;

(* ------------------------------------------------------------------------- *)
(* Updating the model.                                                       *)
(* ------------------------------------------------------------------------- *)

let updateFunction vM func_elts_elt =
      let {randomFunctions = rndFns} = vM

      in let () = updateTables rndFns func_elts_elt
    in
      ()
    ;;

let updateRelation vM (rel_elts,pol) =
      let {randomRelations = rndRels} = vM

      in let () = updateTables rndRels (rel_elts, boolToInt pol)
    in
      ()
    ;;

(* ------------------------------------------------------------------------- *)
(* A type of terms with interpretations embedded in the subterms.            *)
(* ------------------------------------------------------------------------- *)

type modelTerm =
    Model_var
  | Model_fn of Term.functionName * modelTerm list * int list;;

let modelTerm vM vV =
      let rec modelTm tm =
          match destTerm tm with
            Term.Var v -> (Model_var, getValuation vV v)
          | Term.Fn (f,tms) ->
              let (tms,xs) = unzip (List.map modelTm tms)
            in
              (Model_fn (f,tms,xs), interpretFunction vM (f,xs))
    in
      modelTm
    ;;

(* ------------------------------------------------------------------------- *)
(* Perturbing the model.                                                     *)
(* ------------------------------------------------------------------------- *)

type perturbation =
    Function_perturbation of (Term.functionName * element list) * element
  | Relation_perturbation of (Atom.relationName * element list) * bool;;

let perturb vM pert =
    match pert with
      Function_perturbation ((func,elts),elt) -> updateFunction vM ((func,elts),elt)
    | Relation_perturbation ((rel,elts),pol) -> updateRelation vM ((rel,elts),pol);;

  let rec pertTerm vM target tm acc =
      match target with [] -> acc | _ ->
      (match tm with
        Model_var -> acc
      | Model_fn (func,tms,xs) ->
          let onTarget ys = List.mem (interpretFunction vM (func,ys)) target

          in let func_xs = (func,xs)

          in let acc =
              if isFixedFunction vM func_xs then acc
              else
                  let add (y,acc) = Function_perturbation (func_xs,y) :: acc
                in
                  Mlist.foldl add acc target
        in
          pertTerms vM onTarget tms xs acc)

  and pertTerms vM onTarget =
        let vN = msize vM

        in let filterElements pred =
              let rec filt i acc = match i with
                  0 -> acc
                | _ ->
                    let i = i - 1
                    in let acc = if pred i then i :: acc else acc
                  in
                    filt i acc
            in
              filt vN []

        in let rec pert = function
            (_, [], [], acc) -> acc
          | (ys, (tm :: tms), (x :: xs), acc) ->
              let pred y =
                  y <> x && onTarget (List.rev_append ys (y :: xs))

              in let target = filterElements pred

              in let acc = pertTerm vM target tm acc
            in
              pert ((x :: ys), tms, xs, acc)
          | (_, _, _, _) -> raise (Useful.Bug "Model.pertTerms.pert")
      in
        fun x y z -> pert ([],x,y,z)
      ;;

  let pertAtom vM vV target (rel,tms) acc =
        let onTarget ys = interpretRelation vM (rel,ys) = target

        in let (tms,xs) = unzip (List.map (modelTerm vM vV) tms)

        in let rel_xs = (rel,xs)

        in let acc =
            if isFixedRelation vM rel_xs then acc
            else Relation_perturbation (rel_xs,target) :: acc
      in
        pertTerms vM onTarget tms xs acc
      ;;

  let pertLiteral vM vV ((pol,atm),acc) = pertAtom vM vV pol atm acc;;

  let pertClause vM vV cl acc = Literal.Set.foldl (pertLiteral vM vV) acc cl;;

  let pickPerturb vM perts =
      if Mlist.null perts then ()
      else perturb vM (List.nth perts (Random.int (length perts)));;

  let perturbTerm vM vV (tm,target) =
      pickPerturb vM (pertTerm vM target (fst (modelTerm vM vV tm)) []);;

  let perturbAtom vM vV (atm,target) =
      pickPerturb vM (pertAtom vM vV target atm []);;

  let perturbLiteral vM vV lit = pickPerturb vM (pertLiteral vM vV (lit,[]));;

  let perturbClause vM vV cl = pickPerturb vM (pertClause vM vV cl []);;


end


(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC TERMS              *)
(* ========================================================================= *)

module Term_net = struct

(* ------------------------------------------------------------------------- *)
(* Anonymous variables.                                                      *)
(* ------------------------------------------------------------------------- *)

let anonymousName = Name.fromString "_";;
let anonymousVar = Term.Var anonymousName;;

(* ------------------------------------------------------------------------- *)
(* Quotient terms.                                                           *)
(* ------------------------------------------------------------------------- *)

type qterm =
    Var
  | Fn of Name_arity.nameArity * qterm list;;

  let rec cmp = function
      [] -> 0
    | (((q1, q2) as q1_q2) :: qs) ->
      if q1 == q2 then cmp qs
      else
        match q1_q2 with
          (Var,Var) -> 0
        | (Var, Fn _) -> -1
        | (Fn _, Var) -> 1
        | (Fn (f1, f1'), Fn (f2, f2')) -> fnCmp (f1,f1') (f2,f2') qs

  and fnCmp (n1,q1) (n2,q2) qs =
    let c = Name_arity.compare n1 n2 in
    if c <> 0 then c else cmp (zip q1 q2 @ qs);;

  let compareQterm q1 q2 = cmp [(q1,q2)];;

  let compareFnQterm f1 f2 = fnCmp f1 f2 [];;


let equalQterm q1 q2 = compareQterm q1 q2 = 0;;

let equalFnQterm f1 f2 = compareFnQterm f1 f2 = 0;;

let rec termToQterm = function
    (Term.Var _) -> Var
  | (Term.Fn (f,l)) -> Fn ((f, length l), List.map termToQterm l);;

  let rec qm = function
      [] -> true
    | ((Var,_) :: rest) -> qm rest
    | ((Fn _, Var) :: _) -> false
    | ((Fn (f,a), Fn (g,b)) :: rest) ->
      Name_arity.equal f g && qm (zip a b @ rest);;

  let matchQtermQterm qtm qtm' = qm [(qtm,qtm')];;

  let rec qm = function
      [] -> true
    | ((Var,_) :: rest) -> qm rest
    | ((Fn _, Term.Var _) :: _) -> false
    | ((Fn ((f,n),a), Term.Fn (g,b)) :: rest) ->
      Name.equal f g && n = length b && qm (zip a b @ rest);;

  let matchQtermTerm qtm tm = qm [(qtm,tm)];;

  let rec qn qsub = function
      [] -> Some qsub
    | ((Term.Var v, qtm) :: rest) ->
      (match Name.Map.peek qsub v with
         None -> qn (Name.Map.insert qsub (v,qtm)) rest
       | Some qtm' -> if equalQterm qtm qtm' then qn qsub rest else None)
    | ((Term.Fn _, Var) :: _) -> None
    | ((Term.Fn (f,a), Fn ((g,n),b)) :: rest) ->
      if Name.equal f g && length a = n then qn qsub (zip a b @ rest)
      else None;;

  let matchTermQterm qsub tm qtm = qn qsub [(tm,qtm)];;

  let rec qv s t = match (s,t) with
      (Var, x) -> x
    | (x, Var) -> x
    | (Fn (f,a), Fn (g,b)) ->
        let _ = Name_arity.equal f g || failwith "Term_net.qv"
      in
        Fn (f, map2 qv a b)
      ;;

  let rec qu qsub = function
      [] -> qsub
    | ((Var, _) :: rest) -> qu qsub rest
    | ((qtm, Term.Var v) :: rest) ->
        let qtm =
            match Name.Map.peek qsub v with None -> qtm | Some qtm' -> qv qtm qtm'
      in
        qu (Name.Map.insert qsub (v,qtm)) rest
    | ((Fn ((f,n),a), Term.Fn (g,b)) :: rest) ->
      if Name.equal f g && n = length b then qu qsub (zip a b @ rest)
      else failwith "Term_net.qu";;

  let unifyQtermQterm qtm qtm' = Useful.total (qv qtm) qtm';;

  let unifyQtermTerm qsub qtm tm = Useful.total (qu qsub) [(qtm,tm)];;

  let rec qtermToTerm = function
      Var -> anonymousVar
    | (Fn ((f,_),l)) -> Term.Fn (f, List.map qtermToTerm l);;


(* ------------------------------------------------------------------------- *)
(* A type of term sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool};;

type 'a net =
    Result of 'a list
  | Single of qterm * 'a net
  | Multiple of 'a net option * 'a net Name_arity.Map.map;;

type 'a termNet = Net of parameters * int * (int * (int * 'a) net) option;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let newNet parm = Net (parm,0,None);;

  let rec computeSize = function
      (Result l) -> length l
    | (Single (_,n)) -> computeSize n
    | (Multiple (vs,fs)) ->
      Name_arity.Map.foldl
        (fun (_,n,acc) -> acc + computeSize n)
        (match vs with Some n -> computeSize n | None -> 0)
        fs;;

  let netSize = function
      None -> None
    | (Some n) -> Some (computeSize n, n);;


let size = function
    (Net (_,_,None)) -> 0
  | (Net (_, _, Some (i,_))) -> i;;

let null net = size net = 0;;

let singles qtms a = Mlist.foldr (fun (x, y) -> Single (x, y)) a qtms;;

  let pre = function
      None -> (0,None)
    | (Some (i,n)) -> (i, Some n);;

  let rec add a b c = match (a, b, c) with
      (Result l, [], Result l') -> Result (l @ l')
    | (a, (qtm :: qtms as input1), Single (qtm',n)) ->
      if equalQterm qtm qtm' then Single (qtm, add a qtms n)
      else add a input1 (add n [qtm'] (Multiple (None, Name_arity.Map.newMap ())))
    | (a, Var :: qtms, Multiple (vs,fs)) ->
      Multiple (Some (oadd a qtms vs), fs)
    | (a, Fn (f,l) :: qtms, Multiple (vs,fs)) ->
        let n = Name_arity.Map.peek fs f
      in
        Multiple (vs, Name_arity.Map.insert fs (f, oadd a (l @ qtms) n))
    | _ -> raise (Useful.Bug "Term_net.insert: Match")

  and oadd a qtms = function
      None -> singles qtms a
    | (Some n) -> add a qtms n;;

  let ins a qtm (i,n) = Some (i + 1, oadd (Result [a]) [qtm] n);;

  let insert (Net (p,k,n)) (tm,a) =
      try Net (p, k + 1, ins (k,a) (termToQterm tm) (pre n))
      with Failure _ -> raise (Useful.Bug "Term_net.insert: should never fail");;


let fromList parm l = Mlist.foldl (fun (tm_a,n) -> insert n tm_a) (newNet parm) l;;

let filter pred =
      let rec filt = function
          (Result l) ->
          (match List.filter (fun (_,a) -> pred a) l with
             [] -> None
           | l -> Some (Result l))
        | (Single (qtm,n)) ->
          (match filt n with
             None -> None
           | Some n -> Some (Single (qtm,n)))
        | (Multiple (vs,fs)) ->
            let vs = Option.bind vs filt

            in let fs = Name_arity.Map.mapPartial (fun (_,n) -> filt n) fs
          in
            if not (Option.is_some vs) && Name_arity.Map.null fs then None
            else Some (Multiple (vs,fs))
    in try
      function
         Net (_,_,None) as net -> net
       | Net (p, k, Some (_,n)) -> Net (p, k, netSize (filt n))
    with Failure _ -> raise (Useful.Bug "Term_net.filter: should never fail");;

let toString net = "Term_net[" ^ string_of_int (size net) ^ "]";;

(* ------------------------------------------------------------------------- *)
(* Specialized fold operations to support matching and unification.          *)
(* ------------------------------------------------------------------------- *)

  let rec norm = function
      (0 :: ks, ((_,n) as f) :: fs, qtms) ->
        let (a,qtms) = Mlist.revDivide qtms n
      in
        addQterm (Fn (f,a)) (ks,fs,qtms)
    | stack -> stack

  and addQterm qtm (ks,fs,qtms) =
        let ks = match ks with [] -> [] | k :: ks -> (k - 1) :: ks
      in
        norm (ks, fs, qtm :: qtms)

  and addFn ((_,n) as f) (ks,fs,qtms) = norm (n :: ks, f :: fs, qtms);;

  let stackEmpty = ([],[],[]);;

  let stackAddQterm = addQterm;;

  let stackAddFn = addFn;;

  let stackValue = function
      ([],[],[qtm]) -> qtm
    | _ -> raise (Useful.Bug "Term_net.stackValue");;


  let rec fold inc acc = function
      [] -> acc
    | ((0,stack,net) :: rest) ->
      fold inc (inc (stackValue stack, net, acc)) rest
    | ((n, stack, Single (qtm,net)) :: rest) ->
      fold inc acc ((n - 1, stackAddQterm qtm stack, net) :: rest)
    | ((n, stack, Multiple (v,fns)) :: rest) ->
        let n = n - 1

        in let rest =
            match v with
              None -> rest
            | Some net -> (n, stackAddQterm Var stack, net) :: rest

        in let getFns ((_,k) as f, net, x) =
            (k + n, stackAddFn f stack, net) :: x
      in
        fold inc acc (Name_arity.Map.foldr getFns rest fns)
    | _ -> raise (Useful.Bug "Term_net.foldTerms.fold");;

  let foldTerms inc acc net = fold inc acc [(1,stackEmpty,net)];;


let foldEqualTerms pat inc acc =
      let rec fold = function
          ([],net) -> inc (pat,net,acc)
        | (pat :: pats, Single (qtm,net)) ->
          if equalQterm pat qtm then fold (pats,net) else acc
        | (Var :: pats, Multiple (v,_)) ->
          (match v with None -> acc | Some net -> fold (pats,net))
        | (Fn (f,a) :: pats, Multiple (_,fns)) ->
          (match Name_arity.Map.peek fns f with
             None -> acc
           | Some net -> fold (a @ pats, net))
        | _ -> raise (Useful.Bug "Term_net.foldEqualTerms.fold")
    in
      fun net -> fold ([pat],net)
    ;;


  let rec fold inc acc = function
      [] -> acc
    | (([],stack,net) :: rest) ->
      fold inc (inc (stackValue stack, net, acc)) rest
    | ((Var :: pats, stack, net) :: rest) ->
        let harvest (qtm,n,l) = (pats, stackAddQterm qtm stack, n) :: l
      in
        fold inc acc (foldTerms harvest rest net)
    | ((pat :: pats, stack, Single (qtm,net)) :: rest) ->
      (match unifyQtermQterm pat qtm with
         None -> fold inc acc rest
       | Some qtm ->
         fold inc acc ((pats, stackAddQterm qtm stack, net) :: rest))
    | (((Fn (f,a) as pat) :: pats, stack, Multiple (v,fns)) :: rest) ->
        let rest =
            match v with
              None -> rest
            | Some net -> (pats, stackAddQterm pat stack, net) :: rest

        in let rest =
            match Name_arity.Map.peek fns f with
              None -> rest
            | Some net -> (a @ pats, stackAddFn f stack, net) :: rest
      in
        fold inc acc rest
    | _ -> raise (Useful.Bug "Term_net.foldUnifiableTerms.fold");;

  let foldUnifiableTerms pat inc acc net =
      fold inc acc [([pat],stackEmpty,net)];;

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

  let idwise (m,_) (n,_) = Useful.intCompare m n;;

  let fifoize ({fifo=fifo} : parameters) l = if fifo then List.sort idwise l else l;;

  let finally parm l = List.map snd (fifoize parm l);;


  let rec mat acc = function
      [] -> acc
    | ((Result l, []) :: rest) -> mat (l @ acc) rest
    | ((Single (qtm,n), tm :: tms) :: rest) ->
      mat acc (if matchQtermTerm qtm tm then (n,tms) :: rest else rest)
    | ((Multiple (vs,fs), tm :: tms) :: rest) ->
        let rest = match vs with None -> rest | Some n -> (n,tms) :: rest

        in let rest =
            match tm with
              Term.Var _ -> rest
            | Term.Fn (f,l) ->
              match Name_arity.Map.peek fs (f, length l) with
                None -> rest
              | Some n -> (n, l @ tms) :: rest
      in
        mat acc rest
    | _ -> raise (Useful.Bug "Term_net.match: Match");;

  let matchNet x y = match (x,y) with
      (Net (_,_,None), _) -> []
    | (Net (p, _, Some (_,n)), tm) ->
      try finally p (mat [] [(n,[tm])])
      with Failure _ -> raise (Useful.Bug "Term_net.match: should never fail");;


  let unseenInc qsub v tms (qtm,net,rest) =
      (Name.Map.insert qsub (v,qtm), net, tms) :: rest;;

  let seenInc qsub tms (_,net,rest) = (qsub,net,tms) :: rest;;

  let rec mat acc = function
      [] -> acc
    | ((_, Result l, []) :: rest) -> mat (l @ acc) rest
    | ((qsub, Single (qtm,net), tm :: tms) :: rest) ->
      (match matchTermQterm qsub tm qtm with
         None -> mat acc rest
       | Some qsub -> mat acc ((qsub,net,tms) :: rest))
    | ((qsub, (Multiple _ as net), Term.Var v :: tms) :: rest) ->
      (match Name.Map.peek qsub v with
         None -> mat acc (foldTerms (unseenInc qsub v tms) rest net)
       | Some qtm -> mat acc (foldEqualTerms qtm (seenInc qsub tms) rest net))
    | ((qsub, Multiple (_,fns), Term.Fn (f,a) :: tms) :: rest) ->
        let rest =
            match Name_arity.Map.peek fns (f, length a) with
              None -> rest
            | Some net -> (qsub, net, a @ tms) :: rest
      in
        mat acc rest
    | _ -> raise (Useful.Bug "Term_net.matched.mat");;

  let matched x tm = match x with
      (Net (_,_,None)) -> []
    | (Net (parm, _, Some (_,net))) ->
      try finally parm (mat [] [(Name.Map.newMap (), net, [tm])])
      with Failure _ -> raise (Useful.Bug "Term_net.matched: should never fail");;


  let inc qsub v tms (qtm,net,rest) =
      (Name.Map.insert qsub (v,qtm), net, tms) :: rest;;

  let rec mat acc = function
      [] -> acc
    | ((_, Result l, []) :: rest) -> mat (l @ acc) rest
    | ((qsub, Single (qtm,net), tm :: tms) :: rest) ->
      (match unifyQtermTerm qsub qtm tm with
         None -> mat acc rest
       | Some qsub -> mat acc ((qsub,net,tms) :: rest))
    | ((qsub, (Multiple _ as net), Term.Var v :: tms) :: rest) ->
      (match Name.Map.peek qsub v with
         None -> mat acc (foldTerms (inc qsub v tms) rest net)
       | Some qtm -> mat acc (foldUnifiableTerms qtm (inc qsub v tms) rest net))
    | ((qsub, Multiple (v,fns), Term.Fn (f,a) :: tms) :: rest) ->
        let rest = match v with None -> rest | Some net -> (qsub,net,tms) :: rest

        in let rest =
            match Name_arity.Map.peek fns (f, length a) with
              None -> rest
            | Some net -> (qsub, net, a @ tms) :: rest
      in
        mat acc rest
    | _ -> raise (Useful.Bug "Term_net.unify.mat");;

  let unify x tm = match x with
      (Net (_,_,None)) -> []
    | (Net (parm, _, Some (_,net))) ->
      try finally parm (mat [] [(Name.Map.newMap (), net, [tm])])
      with Failure _ -> raise (Useful.Bug "Term_net.unify: should never fail");;

end


(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC ATOMS              *)
(* ========================================================================= *)

module Atom_net = struct

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let atomToTerm atom = Term.Fn atom;;

let termToAtom = function
    (Term.Var _) -> raise (Useful.Bug "Atom_net.termToAtom")
  | (Term.Fn atom) -> atom;;

(* ------------------------------------------------------------------------- *)
(* A type of atom sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = Term_net.parameters;;

type 'a atomNet = 'a Term_net.termNet;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let newNet = Term_net.newNet;;

let size = Term_net.size;;

let insert net (atm,a) = Term_net.insert net (atomToTerm atm, a);;

let fromList parm l = Mlist.foldl (fun (atm_a,n) -> insert n atm_a) (newNet parm) l;;

let filter = Term_net.filter;;

let toString net = "Atom_net[" ^ string_of_int (size net) ^ "]";;


(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

let matchNet net atm = Term_net.matchNet net (atomToTerm atm);;

let matched net atm = Term_net.matched net (atomToTerm atm);;

let unify net atm = Term_net.unify net (atomToTerm atm);;


end


(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC LITERALS           *)
(* ========================================================================= *)

module Literal_net = struct

(* ------------------------------------------------------------------------- *)
(* A type of literal sets that can be efficiently matched and unified.       *)
(* ------------------------------------------------------------------------- *)

type parameters = Atom_net.parameters;;

type 'a literalNet =
    {positive : 'a Atom_net.atomNet;
     negative : 'a Atom_net.atomNet};;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let newNet parm = {positive = Atom_net.newNet parm; negative = Atom_net.newNet parm};;

  let pos ({positive=positive} : 'a literalNet) = Atom_net.size positive;;

  let neg ({negative=negative} : 'a literalNet) = Atom_net.size negative;;

  let size net = pos net + neg net;;

  (*let profile net = {positiveN = pos net; negativeN = neg net};;*)


let insert {positive=positive;negative=negative} = function
    ((true,atm),a) ->
    {positive = Atom_net.insert positive (atm,a); negative = negative}
  | ((false,atm),a) ->
    {positive = positive; negative = Atom_net.insert negative (atm,a)};;

let fromList parm l = Mlist.foldl (fun (lit_a,n) -> insert n lit_a) (newNet parm) l;;

let filter pred {positive=positive;negative=negative} =
    {positive = Atom_net.filter pred positive;
     negative = Atom_net.filter pred negative};;

let toString net = "Literal_net[" ^ string_of_int (size net) ^ "]";;


(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

let matchNet ({positive=positive;negative=negative} : 'a literalNet) = function
    (true,atm) ->
    Atom_net.matchNet positive atm
  | (false,atm) -> Atom_net.matchNet negative atm;;

let matched ({positive=positive;negative=negative} : 'a literalNet) = function
    (true,atm) ->
    Atom_net.matched positive atm
  | (false,atm) -> Atom_net.matched negative atm;;

let unify ({positive=positive;negative=negative} : 'a literalNet) = function
    (true,atm) ->
    Atom_net.unify positive atm
  | (false,atm) -> Atom_net.unify negative atm;;

end


(* ========================================================================= *)
(* SUBSUMPTION CHECKING FOR FIRST ORDER LOGIC CLAUSES                        *)
(* ========================================================================= *)

module Subsume = struct

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let findRest pred =
      let rec f ys = function
          [] -> None
        | (x :: xs) ->
          if pred x then Some (x, List.rev_append ys xs) else f (x :: ys) xs
    in
      f []
    ;;

  let addSym (lit,acc) =
      match Useful.total Literal.sym lit with
        None -> acc
      | Some lit -> lit :: acc
  let clauseSym lits = Mlist.foldl addSym lits lits;;


let sortClause cl =
      let lits = Literal.Set.toList cl
    in
      Mlist.sortMap Literal.typedSymbols (Useful.revCompare Useful.intCompare) lits
    ;;

let incompatible lit =
      let lits = clauseSym [lit]
    in
      fun lit' -> not (List.exists (can (Literal.unify Substitute.empty lit')) lits)
    ;;

(* ------------------------------------------------------------------------- *)
(* Clause ids and lengths.                                                   *)
(* ------------------------------------------------------------------------- *)

type clauseId = int;;

type clauseLength = int;;

  type idSet = (clauseId * clauseLength) Pset.set;;

  let idCompare (id1,len1) (id2,len2) =
      let c = Useful.intCompare len1 len2 in
      if c <> 0 then c else Useful.intCompare id1 id2;;

  let idSetEmpty : idSet = Pset.empty idCompare;;

  let idSetAdd (id_len,set) : idSet = Pset.add set id_len;;

  let idSetAddMax max ((_,len) as id_len, set) : idSet =
      if len <= max then Pset.add set id_len else set;;

  let idSetIntersect set1 set2 : idSet = Pset.intersect set1 set2;;

(* ------------------------------------------------------------------------- *)
(* A type of clause sets that supports efficient subsumption checking.       *)
(* ------------------------------------------------------------------------- *)

type 'a nonunit_t =
         {nextId : clauseId;
          clauses : (Literal.literal list * Thm.clause * 'a) Intmap.map;
          fstLits : (clauseId * clauseLength) Literal_net.literalNet;
          sndLits : (clauseId * clauseLength) Literal_net.literalNet};;

type 'a subsume =
      {empty : (Thm.clause * Substitute.subst * 'a) list;
       unitn : (Literal.literal * Thm.clause * 'a)  Literal_net.literalNet;
       nonunit : 'a nonunit_t};;

open Term_net
let newSubsume () =
      {empty = [];
       unitn = Literal_net.newNet {fifo = false};
       nonunit =
         {nextId = 0;
          clauses = Intmap.newMap ();
          fstLits = Literal_net.newNet {fifo = false};
          sndLits = Literal_net.newNet {fifo = false}}};;

let size ({empty=empty; unitn=unitn; nonunit = {clauses=clauses}}) =
    length empty + Literal_net.size unitn + Intmap.size clauses;;

let insert ({empty=empty;unitn=unitn;nonunit=nonunit}) (cl',a) =
    match sortClause cl' with
      [] ->
        let empty = (cl',Substitute.empty,a) :: empty
      in
        {empty = empty; unitn = unitn; nonunit = nonunit}
    | [lit] ->
        let unitn = Literal_net.insert unitn (lit,(lit,cl',a))
      in
        {empty = empty; unitn = unitn; nonunit = nonunit}
    | fstLit :: (sndLit :: otherLits as nonFstLits) ->
        let {nextId=nextId;clauses=clauses;fstLits=fstLits;sndLits=sndLits} = nonunit
        in let id_length = (nextId, Literal.Set.size cl')
        in let fstLits = Literal_net.insert fstLits (fstLit,id_length)
        in let (sndLit,otherLits) =
            match findRest (incompatible fstLit) nonFstLits with
              Some sndLit_otherLits -> sndLit_otherLits
            | None -> (sndLit,otherLits)
        in let sndLits = Literal_net.insert sndLits (sndLit,id_length)
        in let lits' = otherLits @ [fstLit;sndLit]
        in let clauses = Intmap.insert clauses (nextId,(lits',cl',a))
        in let nextId = nextId + 1
        in let nonunit = {nextId = nextId; clauses = clauses;
                       fstLits = fstLits; sndLits = sndLits}
      in
        {empty = empty; unitn = unitn; nonunit = nonunit}
      ;;

let filter pred ({empty=empty;unitn=unitn;nonunit=nonunit}) =
      let pred3 (_,_,x) = pred x
      in let empty = List.filter pred3 empty

      in let unitn = Literal_net.filter pred3 unitn

      in let nonunit =
            let {nextId=nextId;clauses=clauses;fstLits=fstLits;sndLits=sndLits} = nonunit
            in let clauses' = Intmap.filter (fun x -> pred3 (snd x)) clauses
          in
            if Intmap.size clauses = Intmap.size clauses' then nonunit
            else
                let predId (id,_) = Intmap.inDomain id clauses'
                in let fstLits = Literal_net.filter predId fstLits
                and sndLits = Literal_net.filter predId sndLits
              in
                {nextId = nextId; clauses = clauses';
                 fstLits = fstLits; sndLits = sndLits}
    in
      {empty = empty; unitn = unitn; nonunit = nonunit}
    ;;

let toString subsume = "Subsume{" ^ string_of_int (size subsume) ^ "}";;


(* ------------------------------------------------------------------------- *)
(* Subsumption checking.                                                     *)
(* ------------------------------------------------------------------------- *)

  let matchLit lit' (lit,acc) =
      match Useful.total (Literal.matchLiterals Substitute.empty lit') lit with
        Some sub -> sub :: acc
      | None -> acc;;

  let genClauseSubsumes pred cl' lits' cl a =
        let rec mkSubsl acc sub = function
            [] -> Some (sub, Mlist.sortMap length Useful.intCompare acc)
          | (lit' :: lits') ->
            match Mlist.foldl (matchLit lit') [] cl with
              [] -> None
            | [sub'] ->
              (match Useful.total (Substitute.union sub) sub' with
                 None -> None
               | Some sub -> mkSubsl acc sub lits')
            | subs -> mkSubsl (subs :: acc) sub lits'

        in let rec search = function
            [] -> None
          | ((sub,[]) :: others) ->
              let x = (cl',sub,a)
            in
              if pred x then Some x else search others
          | ((_, [] :: _) :: others) -> search others
          | ((sub, (sub' :: subs) :: subsl) :: others) ->
              let others = (sub, subs :: subsl) :: others
            in
              match Useful.total (Substitute.union sub) sub' with
                None -> search others
              | Some sub -> search ((sub,subsl) :: others)
      in
        match mkSubsl [] Substitute.empty lits' with
          None -> None
        | Some sub_subsl -> search [sub_subsl]
      ;;


  let emptySubsumes pred empty = Mlist.find pred empty;;

  let unitSubsumes pred unitn =
        let subLit lit =
              let subUnit (lit',cl',a) =
                  match Useful.total (Literal.matchLiterals Substitute.empty lit') lit with
                    None -> None
                  | Some sub ->
                      let x = (cl',sub,a)
                    in
                      if pred x then Some x else None
            in
              Mlist.first subUnit (Literal_net.matchNet unitn lit)
      in
        Mlist.first subLit
      ;;

  let nonunitSubsumes pred nonunit max cl =
        let addId = match max with None -> idSetAdd | Some n -> idSetAddMax n

        in let subLit lits (lit,acc) =
            Mlist.foldl addId acc (Literal_net.matchNet lits lit)

        in let {nextId = _; clauses=clauses; fstLits=fstLits; sndLits=sndLits} = nonunit

        in let subCl' (id,_) =
              let (lits',cl',a) = Intmap.get clauses id
            in
              genClauseSubsumes pred cl' lits' cl a

        in let fstCands = Mlist.foldl (subLit fstLits) idSetEmpty cl
        in let sndCands = Mlist.foldl (subLit sndLits) idSetEmpty cl
        in let cands = idSetIntersect fstCands sndCands
      in
        Pset.firstl subCl' cands
      ;;

  let genSubsumes pred ({empty=empty;unitn=unitn;nonunit=nonunit}) max cl =
      match emptySubsumes pred empty with
        (Some _) as s -> s
      | None ->
        if max = Some 0 then None
        else
            let cl = clauseSym (Literal.Set.toList cl)
          in
            match unitSubsumes pred unitn cl with
              Some _ as s -> s
            | None ->
              if max = Some 1 then None
              else nonunitSubsumes pred nonunit max cl
          ;;

  let subsumes pred subsume cl = genSubsumes pred subsume None cl;;

  let strictlySubsumes pred subsume cl =
      genSubsumes pred subsume (Some (Literal.Set.size cl)) cl;;

(*MetisTrace4
let subsumes = fun pred -> fun subsume -> fun cl ->
    let
      let ppCl = Literal.Set.pp
      let ppSub = Substitute.pp
      let () = Print.trace ppCl "Subsume.subsumes: cl" cl
      let result = subsumes pred subsume cl
      let () =
          match result with
            None -> trace "Subsume.subsumes: not subsumed\n"
          | Some (cl,sub,_) ->
            (Print.trace ppCl "Subsume.subsumes: subsuming cl" cl;;
             Print.trace ppSub "Subsume.subsumes: subsuming sub" sub)
    in
      result
    end;;

let strictlySubsumes = fun pred -> fun subsume -> fun cl ->
    let
      let ppCl = Literal.Set.pp
      let ppSub = Substitute.pp
      let () = Print.trace ppCl "Subsume.strictlySubsumes: cl" cl
      let result = strictlySubsumes pred subsume cl
      let () =
          match result with
            None -> trace "Subsume.subsumes: not subsumed\n"
          | Some (cl,sub,_) ->
            (Print.trace ppCl "Subsume.subsumes: subsuming cl" cl;;
             Print.trace ppSub "Subsume.subsumes: subsuming sub" sub)
    in
      result
    end;;
*)

let isSubsumed subs cl = Option.is_some (subsumes (K true) subs cl);;

let isStrictlySubsumed subs cl =
    Option.is_some (strictlySubsumes (K true) subs cl);;

(* ------------------------------------------------------------------------- *)
(* Single clause versions.                                                   *)
(* ------------------------------------------------------------------------- *)

let clauseSubsumes cl' cl =
      let lits' = sortClause cl'
      and lits = clauseSym (Literal.Set.toList cl)
    in
      match genClauseSubsumes (K true) cl' lits' lits () with
        Some (_,sub,()) -> Some sub
      | None -> None
    ;;

let clauseStrictlySubsumes cl' cl =
    if Literal.Set.size cl' > Literal.Set.size cl then None
    else clauseSubsumes cl' cl;;

end


(* ========================================================================= *)
(* KNUTH-BENDIX TERM ORDERING CONSTRAINTS                                    *)
(* ========================================================================= *)

module Knuth_bendix_order = struct

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let notEqualTerm (x,y) = not (Term.equal x y);;

let firstNotEqualTerm f l =
    match Mlist.find notEqualTerm l with
      Some (x,y) -> f x y
    | None -> raise (Useful.Bug "firstNotEqualTerm");;

(* ------------------------------------------------------------------------- *)
(* The weight of all constants must be at least 1, and there must be at most *)
(* one unary function with weight 0.                                         *)
(* ------------------------------------------------------------------------- *)

type kbo =
     {weight : Term.function_t -> int;
      precedence : Term.function_t -> Term.function_t -> int};;

(* Default weight = uniform *)

let uniformWeight : Term.function_t -> int = K 1;;

(* Default precedence = by arity *)

let arityPrecedence : Term.function_t -> Term.function_t -> int =
    fun (f1,n1) (f2,n2) ->
       let c = Useful.intCompare n1 n2 in
       if c <> 0 then c else Name.compare f1 f2;;

(* The default order *)

let default = {weight = uniformWeight; precedence = arityPrecedence};;

(* ------------------------------------------------------------------------- *)
(* Term weight-1 represented as a linear function of the weight-1 of the     *)
(* variables in the term (plus a constant).                                  *)
(*                                                                           *)
(* Note that the conditions on weight functions ensure that all weights are  *)
(* at least 1, so all weight-1s are at least 0.                              *)
(* ------------------------------------------------------------------------- *)

type weight = Weight of int Name.Map.map * int;;

let weightEmpty : int Name.Map.map = Name.Map.newMap ();;

let weightZero = Weight (weightEmpty,0);;

let weightIsZero (Weight (m,c)) = c = 0 && Name.Map.null m;;

let weightNeg (Weight (m,c)) = Weight (Name.Map.transform (fun x -> -x) m, -c);;

  let add ((_,n1),(_,n2)) =
        let n = n1 + n2
      in
        if n = 0 then None else Some n
      ;;
  let weightAdd (Weight (m1,c1)) (Weight (m2,c2)) =
      Weight (Name.Map.union add m1 m2, c1 + c2);;

let weightSubtract w1 w2 = weightAdd w1 (weightNeg w2);;

let weightTerm weight =
      let rec wt m c = function
          [] -> Weight (m,c)
        | (Term.Var v :: tms) ->
            let n = Option.value (Name.Map.peek m v) ~default:0
          in
            wt (Name.Map.insert m (v, n + 1)) (c + 1) tms
        | (Term.Fn (f,a) :: tms) ->
          wt m (c + weight (f, length a)) (a @ tms)
    in
      fun tm -> wt weightEmpty (-1) [tm]
    ;;

let weightLowerBound (Weight (m,c)) =
    if Name.Map.exists (fun (_,n) -> n < 0) m then None else Some c;;

(*MetisDebug
let ppWeightList =
    let
      let ppCoeff n =
          if n < 0 then Print.sequence (Print.ppString "~") (ppCoeff (~n))
          else if n = 1 then Print.skip
          else Print.ppInt n

      let pp_tm (None,n) = Print.ppInt n
        | pp_tm (Some v, n) = Print.sequence (ppCoeff n) (Name.pp v)
    in
      fun [] -> Print.ppInt 0
       | tms -> Print.ppOpList " +" pp_tm tms
    end;;

let ppWeight (Weight (m,c)) =
    let
      let l = Name.Map.toList m
      let l = List.map (fun (v,n) -> (Some v, n)) l
      let l = if c = 0 then l else l @ [(None,c)]
    in
      ppWeightList l
    end;;

let weightToString = Print.toString ppWeight;;
*)

(* ------------------------------------------------------------------------- *)
(* The Knuth-Bendix term order.                                              *)
(* ------------------------------------------------------------------------- *)

let compare {weight=weight;precedence=precedence} =
      let weightDifference tm1 tm2 =
            let w1 = weightTerm weight tm1
            and w2 = weightTerm weight tm2
          in
            weightSubtract w2 w1

      in let rec weightLess tm1 tm2 =
            let w = weightDifference tm1 tm2
          in
            if weightIsZero w then precedenceLess tm1 tm2
            else weightDiffLess w tm1 tm2

      and weightDiffLess w tm1 tm2 =
          match weightLowerBound w with
            None -> false
          | Some 0 -> precedenceLess tm1 tm2
          | Some n -> n > 0

      and precedenceLess x y = match (x,y) with
          (Term.Fn (f1,a1), Term.Fn (f2,a2)) ->
          let c = precedence (f1, length a1) (f2, length a2) in
          if c < 0 then true
          else if c = 0 then firstNotEqualTerm weightLess (zip a1 a2)
          else false
        | _ -> false

      in let weightDiffGreater w tm1 tm2 = weightDiffLess (weightNeg w) tm2 tm1

      in let rec weightCmp tm1 tm2 =
            let w = weightDifference tm1 tm2
          in
            if weightIsZero w then precedenceCmp tm1 tm2
            else if weightDiffLess w tm1 tm2 then Some (-1)
            else if weightDiffGreater w tm1 tm2 then Some 1
            else None

      and precedenceCmp x y = match (x,y) with
          (Term.Fn (f1,a1), Term.Fn (f2,a2)) ->
          let c = precedence (f1, length a1) (f2, length a2) in
          if c < 0 then Some (-1)
          else if c = 0 then firstNotEqualTerm weightCmp (zip a1 a2)
          else Some 1
        | _ -> raise (Useful.Bug "kboOrder.precendenceCmp")
    in
      fun tm1 tm2 ->
         if Term.equal tm1 tm2 then Some 0 else weightCmp tm1 tm2
    ;;

(*MetisTrace7
let compare = fun kbo -> fun tm1 tm2 ->
    let
      let () = Print.trace Term.pp "Knuth_bendix_order.compare: tm1" tm1
      let () = Print.trace Term.pp "Knuth_bendix_order.compare: tm2" tm2
      let result = compare kbo tm1 tm2
      let () =
          match result with
            None -> trace "Knuth_bendix_order.compare: result = Incomparable\n"
          | Some x ->
            Print.trace Print.ppInt "Knuth_bendix_order.compare: result" x
    in
      result
    end;;
*)

end


(* ========================================================================= *)
(* ORDERED REWRITING FOR FIRST ORDER TERMS                                   *)
(* ========================================================================= *)

module Rewrite = struct

(* ------------------------------------------------------------------------- *)
(* Orientations of equations.                                                *)
(* ------------------------------------------------------------------------- *)

type orient = Left_to_right | Right_to_left;;

let toStringOrient ort =
    match ort with
      Left_to_right -> "-->"
    | Right_to_left -> "<--";;


let toStringOrientOption orto =
    match orto with
      Some ort -> toStringOrient ort
    | None -> "<->";;


(* ------------------------------------------------------------------------- *)
(* A type of rewrite systems.                                                *)
(* ------------------------------------------------------------------------- *)

type reductionOrder = Term.term -> Term.term -> int option;;

type equationId = int;;

type equation = Rule.equation;;

type rewrite_t =
      {order : reductionOrder;
       known : (equation * orient option) Intmap.map;
       redexes : (equationId * orient) Term_net.termNet;
       subterms : (equationId * bool * Term.path) Term_net.termNet;
       waiting : Intset.set};;

type rewrite =
    Rewrite of rewrite_t;;

let updateWaiting rw waiting =
      let Rewrite {order=order; known=known; redexes=redexes; subterms=subterms; waiting = _} = rw
    in
      Rewrite
        {order = order; known = known; redexes = redexes;
         subterms = subterms; waiting = waiting}
    ;;

let deleteWaiting (Rewrite {waiting=waiting} as rw) id =
    updateWaiting rw (Intset.delete waiting id);;

(* ------------------------------------------------------------------------- *)
(* Basic operations                                                          *)
(* ------------------------------------------------------------------------- *)

open Term_net
let newRewrite order =
    Rewrite
      {order = order;
       known = Intmap.newMap ();
       redexes = Term_net.newNet {fifo = false};
       subterms = Term_net.newNet {fifo = false};
       waiting = Intset.empty};;

let peek (Rewrite {known=known}) id = Intmap.peek known id;;

let size (Rewrite {known=known}) = Intmap.size known;;

let equations (Rewrite {known=known}) =
    Intmap.foldr (fun (_,(eqn,_),eqns) -> eqn :: eqns) [] known;;


(*MetisTrace1
local
  let ppEq ((x_y,_),ort) =
      Print.ppOp2 (" " ^ toStringOrientOption ort) Term.pp Term.pp x_y;;

  let ppField f ppA a =
      Print.inconsistentBlock 2
        [Print.ppString (f ^ " ="),
         Print.break,
         ppA a];;

  let ppKnown =
      ppField "known"
        (Print.ppMap Intmap.toList
           (Print.ppList (Print.ppPair Print.ppInt ppEq)));;

  let ppRedexes =
      ppField "redexes"
        (Term_net.pp (Print.ppPair Print.ppInt ppOrient));;

  let ppSubterms =
      ppField "subterms"
        (Term_net.pp
           (Print.ppMap
              (fun (i,l,p) -> (i, (if l then 0 else 1) :: p))
              (Print.ppPair Print.ppInt Term.ppPath)));;

  let ppWaiting =
      ppField "waiting"
        (Print.ppMap (Intset.toList) (Print.ppList Print.ppInt));;
in
  let pp (Rewrite {known,redexes,subterms,waiting,...}) =
      Print.inconsistentBlock 2
        [Print.ppString "Rewrite",
         Print.break,
         Print.inconsistentBlock 1
           [Print.ppString "{",
            ppKnown known,
(*MetisTrace5
            Print.ppString ",",
            Print.break,
            ppRedexes redexes,
            Print.ppString ",",
            Print.break,
            ppSubterms subterms,
            Print.ppString ",",
            Print.break,
            ppWaiting waiting,
*)
            Print.skip],
         Print.ppString "}"]
end;;
*)


(* ------------------------------------------------------------------------- *)
(* Debug functions.                                                          *)
(* ------------------------------------------------------------------------- *)

let termReducible order known id =
      let eqnRed ((l,r),_) tm =
          match Useful.total (Substitute.matchTerms Substitute.empty l) tm with
            None -> false
          | Some sub ->
            order tm (Substitute.subst (Substitute.normalize sub) r) = Some 1

      in let knownRed tm (eqnId,(eqn,ort)) =
          eqnId <> id &&
          ((ort <> Some Right_to_left && eqnRed eqn tm) ||
           (ort <> Some Left_to_right && eqnRed (Rule.symEqn eqn) tm))

      in let rec termRed tm = Intmap.exists (knownRed tm) known || subtermRed tm
      and subtermRed = function
          (Term.Var _) -> false
        | (Term.Fn (_,tms)) -> List.exists termRed tms
    in
      termRed
    ;;

let literalReducible order known id lit =
    List.exists (termReducible order known id) (Literal.arguments lit);;

let literalsReducible order known id lits =
    Literal.Set.exists (literalReducible order known id) lits;;

let thmReducible order known id th =
    literalsReducible order known id (Thm.clause th);;

(* ------------------------------------------------------------------------- *)
(* Add equations into the system.                                            *)
(* ------------------------------------------------------------------------- *)

let orderToOrient = function
    Some 0 -> failwith "Rewrite.orient: reflexive"
  | Some c when c > 0 -> Some Left_to_right
  | Some _ -> Some Right_to_left
  | None -> None;;

  let ins redexes redex id ort = Term_net.insert redexes (redex,(id,ort));;

  let addRedexes id (((l,r),_),ort) redexes =
      match ort with
        Some Left_to_right -> ins redexes l id Left_to_right
      | Some Right_to_left -> ins redexes r id Right_to_left
      | None -> ins (ins redexes l id Left_to_right) r id Right_to_left;;


let add (Rewrite {known=known} as rw) (id,eqn) =
    if Intmap.inDomain id known then rw
    else
        let Rewrite {order=order;redexes=redexes;subterms=subterms;waiting=waiting} = rw

        in let ort = let (l,r) = fst eqn in orderToOrient (order l r)

        in let known = Intmap.insert known (id,(eqn,ort))

        in let redexes = addRedexes id (eqn,ort) redexes

        in let waiting = Intset.add waiting id

        in let rw =
            Rewrite
              {order = order; known = known; redexes = redexes;
               subterms = subterms; waiting = waiting}
(*MetisTrace5
        let () = Print.trace pp "Rewrite.add: result" rw
*)
      in
        rw
      ;;

  let uncurriedAdd (eqn,rw) = add rw eqn;;
  let addList rw = Mlist.foldl uncurriedAdd rw;;

(* ------------------------------------------------------------------------- *)
(* Rewriting (the order must be a refinement of the rewrite order).          *)
(* ------------------------------------------------------------------------- *)

  let reorder (i,_) (j,_) = Useful.intCompare j i;;
  let matchingRedexes redexes tm = List.sort reorder (Term_net.matchNet redexes tm);;


let wellOriented x y = match (x,y) with
    (None, _) -> true
  | (Some Left_to_right, Left_to_right) -> true
  | (Some Right_to_left ,Right_to_left) -> true
  | _ -> false;;

let redexResidue x y = match (x,y) with
    (Left_to_right, ((l_r,_) : equation)) -> l_r
  | (Right_to_left, ((l,r),_)) -> (r,l);;

let orientedEquation dir eqn = match dir with
    Left_to_right -> eqn
  | Right_to_left -> Rule.symEqn eqn;;

let rewrIdConv' order known redexes id tm =
      let rewr (id',lr) =
            let _ = id <> id' || failwith "same theorem"
            in let (eqn,ort) = Intmap.get known id'
            in let _ = wellOriented ort lr || failwith "orientation"
            in let (l,r) = redexResidue lr eqn
            in let sub = Substitute.normalize (Substitute.matchTerms Substitute.empty l tm)
            in let tm' = Substitute.subst sub r
            in let _ = Option.is_some ort ||
                    order tm tm' = Some 1 ||
                    failwith "order"
            in let (_,th) = orientedEquation lr eqn
          in
            (tm', Thm.subst sub th)
    in
      match Mlist.first (Useful.total rewr) (matchingRedexes redexes tm) with
        None -> failwith "Rewrite.rewrIdConv: no matching rewrites"
      | Some res -> res
    ;;

let rewriteIdConv' order known redexes id =
    if Intmap.null known then Rule.allConv
    else Rule.repeatTopDownConv (rewrIdConv' order known redexes id);;

let mkNeqConv order lit =
      let (l,r) = Literal.destNeq lit
    in
      match order l r with
        None -> failwith "incomparable"
      | Some c when c < 0 ->
          let th = Rule.symmetryRule l r
        in
          fun tm ->
             if Term.equal tm r then (l,th) else failwith "mkNeqConv: RL"
      | Some 0 -> failwith "irreflexive"
      | Some _ ->
          let th = Thm.assume lit
        in
          fun tm ->
             if Term.equal tm l then (r,th) else failwith "mkNeqConv: LR"
    ;;

type neqConvs = Neq_convs of Rule.conv Literal.Map.map;;

let neqConvsEmpty = Neq_convs (Literal.Map.newMap ());;

let neqConvsNull (Neq_convs m) = Literal.Map.null m;;

let neqConvsAdd order (Neq_convs m) lit =
    match Useful.total (mkNeqConv order) lit with
      None -> None
    | Some conv -> Some (Neq_convs (Literal.Map.insert m (lit,conv)));;

let mkNeqConvs order =
      let add (lit,(neq,lits)) =
          match neqConvsAdd order neq lit with
            Some neq -> (neq,lits)
          | None -> (neq, Literal.Set.add lits lit)
    in
      Literal.Set.foldl add (neqConvsEmpty,Literal.Set.empty)
    ;;

let neqConvsDelete (Neq_convs m) lit = Neq_convs (Literal.Map.delete m lit);;

let neqConvsToConv (Neq_convs m) =
    Rule.firstConv (Literal.Map.foldr (fun (_,c,l) -> c :: l) [] m);;

let neqConvsFoldl f b (Neq_convs m) =
    Literal.Map.foldl (fun (l,_,z) -> f (l,z)) b m;;

let neqConvsRewrIdLiterule order known redexes id neq =
    if Intmap.null known && neqConvsNull neq then Rule.allLiterule
    else
        let neq_conv = neqConvsToConv neq
        in let rewr_conv = rewrIdConv' order known redexes id
        in let conv = Rule.orelseConv neq_conv rewr_conv
        in let conv = Rule.repeatTopDownConv conv
      in
        Rule.allArgumentsLiterule conv
      ;;

let rewriteIdEqn' order known redexes id ((l_r,th) as eqn) =
      let (neq,_) = mkNeqConvs order (Thm.clause th)
      in let literule = neqConvsRewrIdLiterule order known redexes id neq
      in let (strongEqn,lit) =
          match Rule.equationLiteral eqn with
            None -> (true, Literal.mkEq l_r)
          | Some lit -> (false,lit)
      in let (lit',litTh) = literule lit
    in
      if Literal.equal lit lit' then eqn
      else
        (Literal.destEq lit',
         if strongEqn then th
         else if not (Thm.negateMember lit litTh) then litTh
         else Thm.resolve lit th litTh);;
(*MetisDebug
    handle Failure err -> failwith ("Rewrite.rewriteIdEqn':\n" ^ err);;
*)

let rewriteIdLiteralsRule' order known redexes id lits th =
      let mk_literule = neqConvsRewrIdLiterule order known redexes id

      in let rewr_neq_lit (lit, ((changed,neq,lits,th) as acc)) =
            let neq = neqConvsDelete neq lit
            in let (lit',litTh) = mk_literule neq lit
          in
            if Literal.equal lit lit' then acc
            else
                let th = if Thm.member lit th then Thm.resolve lit th litTh
                         else th
              in
                match neqConvsAdd order neq lit' with
                  Some neq -> (true,neq,lits,th)
                | None -> (changed, neq, Literal.Set.add lits lit', th)

      in let rec rewr_neq_lits neq lits th =
            let (changed,neq,lits,th) =
                neqConvsFoldl rewr_neq_lit (false,neq,lits,th) neq
          in
            if changed then rewr_neq_lits neq lits th
            else (neq,lits,th)

      in let (neq,lits) = mkNeqConvs order lits

      in let (neq,lits,th) = rewr_neq_lits neq lits th

      in let rewr_literule = mk_literule neq

      in let rewr_lit (lit,th) =
          if Thm.member lit th then Rule.literalRule rewr_literule lit th
          else th
    in
      Literal.Set.foldl rewr_lit th lits
    ;;

let rewriteIdRule' order known redexes id th =
    rewriteIdLiteralsRule' order known redexes id (Thm.clause th) th;;

(*MetisDebug
let rewriteIdRule' = fun order -> fun known -> fun redexes -> fun id -> fun th ->
    let
(*MetisTrace6
      let () = Print.trace Thm.pp "Rewrite.rewriteIdRule': th" th
*)
      let result = rewriteIdRule' order known redexes id th
(*MetisTrace6
      let () = Print.trace Thm.pp "Rewrite.rewriteIdRule': result" result
*)
      let _ = not (thmReducible order known id result) ||
              raise Useful.Bug "rewriteIdRule: should be normalized"
    in
      result
    end
    handle Failure err -> failwith ("Rewrite.rewriteIdRule:\n" ^ err);;
*)

let rewrIdConv (Rewrite {known=known;redexes=redexes}) order =
    rewrIdConv' order known redexes;;

let rewrConv rewrite order = rewrIdConv rewrite order (-1);;

let rewriteIdConv (Rewrite {known=known;redexes=redexes}) order =
    rewriteIdConv' order known redexes;;

let rewriteConv rewrite order = rewriteIdConv rewrite order (-1);;

let rewriteIdLiteralsRule (Rewrite {known=known;redexes=redexes}) order =
    rewriteIdLiteralsRule' order known redexes;;

let rewriteLiteralsRule rewrite order =
    rewriteIdLiteralsRule rewrite order (-1);;

let rewriteIdRule (Rewrite {known=known;redexes=redexes}) order =
    rewriteIdRule' order known redexes;;

let rewriteRule rewrite order = rewriteIdRule rewrite order (-1);;

(* ------------------------------------------------------------------------- *)
(* Inter-reduce the equations in the system.                                 *)
(* ------------------------------------------------------------------------- *)

let addSubterms id (((l,r),_) : equation) subterms =
      let addSubterm b ((path,tm),net) = Term_net.insert net (tm,(id,b,path))

      in let subterms = Mlist.foldl (addSubterm true) subterms (Term.subterms l)

      in let subterms = Mlist.foldl (addSubterm false) subterms (Term.subterms r)
    in
      subterms
    ;;

let sameRedexes x y z = match (x,y,z) with
    (None,_,_) -> false
  | (Some Left_to_right, (l0,_),(l,_)) -> Term.equal l0 l
  | (Some Right_to_left, (_,r0),(_,r)) -> Term.equal r0 r;;

let redexResidues x (l,r) = match x with
    None -> [(l,r,false);(r,l,false)]
  | (Some Left_to_right) -> [(l,r,true)]
  | (Some Right_to_left) -> [(r,l,true)];;

let findReducibles order known subterms id =
      let checkValidRewr (l,r,ord) id' left path =
            let (((x,y),_),_) = Intmap.get known id'
            in let tm = Term.subterm (if left then x else y) path
            in let sub = Substitute.matchTerms Substitute.empty l tm
          in
            if ord then ()
            else
                let tm' = Substitute.subst (Substitute.normalize sub) r
              in
                if order tm tm' = Some 1 then ()
                else failwith "order"

      in let addRed lr ((id',left,path),todo) =
          if id <> id' && not (Intset.member id' todo) &&
             can (checkValidRewr lr id' left) path
          then Intset.add todo id'
          else todo

      in let findRed ((l,_,_) as lr, todo) =
          Mlist.foldl (addRed lr) todo (Term_net.matched subterms l)
    in
      Mlist.foldl findRed
    ;;

let reduce1 newx id (eqn0,ort0) (rpl,spl,todo,rw,changed) =
      let (eq0,_) = eqn0
      in let Rewrite {order=order;known=known;redexes=redexes;subterms=subterms;waiting=waiting} = rw
      in let (eq,_) as eqn = rewriteIdEqn' order known redexes id eqn0
      in let identical =
            let (l0,r0) = eq0
            and (l,r) = eq
          in
            Term.equal l l0 && Term.equal r r0
      in let same_redexes = identical || sameRedexes ort0 eq0 eq
      in let rpl = if same_redexes then rpl else Intset.add rpl id
      in let spl = if newx || identical then spl else Intset.add spl id
      in let changed =
          if not newx && identical then changed else Intset.add changed id
      in let ort =
          if same_redexes then Some ort0 else let (l,r) = eq in Useful.total orderToOrient (order l r)
    in
      match ort with
        None ->
          let known = Intmap.delete known id
          in let rw =
              Rewrite
                {order = order; known = known; redexes = redexes;
                 subterms = subterms; waiting = waiting}
        in
          (rpl,spl,todo,rw,changed)
      | Some ort ->
          let todo =
              if not newx && same_redexes then todo
              else
                findReducibles
                  order known subterms id todo (redexResidues ort eq)
          in let known =
              if identical then known else Intmap.insert known (id,(eqn,ort))
          in let redexes =
              if same_redexes then redexes
              else addRedexes id (eqn,ort) redexes
          in let subterms =
              if newx || not identical then addSubterms id eqn subterms
              else subterms
          in let rw =
              Rewrite
                {order = order; known = known; redexes = redexes;
                 subterms = subterms; waiting = waiting}
        in
          (rpl,spl,todo,rw,changed)
    ;;

let pick known set =
      let oriented id =
          match Intmap.peek known id with
            Some ((_, Some _) as x) -> Some (id,x)
          | _ -> None

      in let any id =
          match Intmap.peek known id with Some x -> Some (id,x) | _ -> None
    in
      match Intset.firstl oriented set with
        Some _ as x -> x
      | None -> Intset.firstl any set
    ;;

  let cleanRedexes known redexes rpl =
      if Intset.null rpl then redexes
      else
          let filt (id,_) = not (Intset.member id rpl)

          in let addReds (id,reds) =
              match Intmap.peek known id with
                None -> reds
              | Some eqn_ort -> addRedexes id eqn_ort reds

          in let redexes = Term_net.filter filt redexes
          in let redexes = Intset.foldl addReds redexes rpl
        in
          redexes
        ;;

  let cleanSubterms known subterms spl =
      if Intset.null spl then subterms
      else
          let filt (id,_,_) = not (Intset.member id spl)

          in let addSubtms (id,subtms) =
              match Intmap.peek known id with
                None -> subtms
              | Some (eqn,_) -> addSubterms id eqn subtms

          in let subterms = Term_net.filter filt subterms
          in let subterms = Intset.foldl addSubtms subterms spl
        in
          subterms
        ;;

  let rebuild rpl spl rw =
(*MetisTrace5
        let ppPl = Print.ppMap Intset.toList (Print.ppList Print.ppInt)
        let () = Print.trace ppPl "Rewrite.rebuild: rpl" rpl
        let () = Print.trace ppPl "Rewrite.rebuild: spl" spl
*)
        let Rewrite {order=order;known=known;redexes=redexes;subterms=subterms;waiting=waiting} = rw
        in let redexes = cleanRedexes known redexes rpl
        in let subterms = cleanSubterms known subterms spl
      in
        Rewrite
          {order = order;
           known = known;
           redexes = redexes;
           subterms = subterms;
           waiting = waiting}
      ;;

let rec reduceAcc (rpl, spl, todo, (Rewrite {known=known;waiting=waiting} as rw), changed) =
    match pick known todo with
      Some (id,eqn_ort) ->
        let todo = Intset.delete todo id
      in
        reduceAcc (reduce1 false id eqn_ort (rpl,spl,todo,rw,changed))
    | None ->
      match pick known waiting with
        Some (id,eqn_ort) ->
          let rw = deleteWaiting rw id
        in
          reduceAcc (reduce1 true id eqn_ort (rpl,spl,todo,rw,changed))
      | None -> (rebuild rpl spl rw, Intset.toList changed);;

let isReduced (Rewrite {waiting=waiting}) = Intset.null waiting;;

let reduce' rw =
    if isReduced rw then (rw,[])
    else reduceAcc (Intset.empty,Intset.empty,Intset.empty,rw,Intset.empty);;

(*MetisDebug
let reduce' = fun rw ->
    let
(*MetisTrace4
      let () = Print.trace pp "Rewrite.reduce': rw" rw
*)
      let Rewrite {known,order,...} = rw
      let result as (Rewrite {known = known', ...}, _) = reduce' rw
(*MetisTrace4
      let ppResult = Print.ppPair pp (Print.ppList Print.ppInt)
      let () = Print.trace ppResult "Rewrite.reduce': result" result
*)
      let ths = List.map (fun (id,((_,th),_)) -> (id,th)) (Intmap.toList known')
      let _ =
          not (List.exists (uncurry (thmReducible order known')) ths) ||
          raise Useful.Bug "Rewrite.reduce': not fully reduced"
    in
      result
    end
    handle Failure err -> raise (Useful.Bug ("Rewrite.reduce': shouldn't fail\n" ^ err));;
*)

let reduce rw = fst (reduce' rw);;

(* ------------------------------------------------------------------------- *)
(* Rewriting as a derived rule.                                              *)
(* ------------------------------------------------------------------------- *)

  let addEqn (id_eqn,rw) = add rw id_eqn;;
  let orderedRewrite order ths =
      let rw = Mlist.foldl addEqn (newRewrite order) (Mlist.enumerate ths)
    in
      rewriteRule rw order
    ;;

  let order : reductionOrder = fun _ _ -> Some 1;;
  let rewrite = orderedRewrite order;;


end

(* ========================================================================= *)
(* A STORE FOR UNIT THEOREMS                                                 *)
(* ========================================================================= *)

module Units = struct

(* ------------------------------------------------------------------------- *)
(* A type of unit store.                                                     *)
(* ------------------------------------------------------------------------- *)

type unitThm = Literal.literal * Thm.thm;;

type units = Units of unitThm Literal_net.literalNet;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

open Term_net
let empty = Units (Literal_net.newNet {fifo = false});;

let size (Units net) = Literal_net.size net;;

let toString units = "U{" ^ string_of_int (size units) ^ "}";;

(* ------------------------------------------------------------------------- *)
(* Add units into the store.                                                 *)
(* ------------------------------------------------------------------------- *)

let add (Units net) ((lit,th) as uTh) =
      let net = Literal_net.insert net (lit,uTh)
    in
      match Useful.total Literal.sym lit with
        None -> Units net
      | Some ((pol,_) as lit') ->
          let th' = (if pol then Rule.symEq else Rule.symNeq) lit th
          in let net = Literal_net.insert net (lit',(lit',th'))
        in
          Units net
    ;;

let addList = Mlist.foldl (fun (th,u) -> add u th);;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

let matchUnits (Units net) lit =
      let check ((lit',_) as uTh) =
          match Useful.total (Literal.matchLiterals Substitute.empty lit') lit with
            None -> None
          | Some sub -> Some (uTh,sub)
    in
      Mlist.first check (Literal_net.matchNet net lit)
    ;;

(* ------------------------------------------------------------------------- *)
(* Reducing by repeated matching and resolution.                             *)
(* ------------------------------------------------------------------------- *)

let reduce units =
      let red1 (lit,news_th) =
          match Useful.total Literal.destIrrefl lit with
            Some tm ->
              let (news,th) = news_th
              in let th = Thm.resolve lit th (Thm.refl tm)
            in
              (news,th)
          | None ->
              let lit' = Literal.negate lit
            in
              match matchUnits units lit' with
                None -> news_th
              | Some ((_,rth),sub) ->
                  let (news,th) = news_th
                  in let rth = Thm.subst sub rth
                  in let th = Thm.resolve lit th rth
                  in let newLits = Literal.Set.delete (Thm.clause rth) lit'
                  in let news = Literal.Set.union newLits news
                in
                  (news,th)

      in let rec red (news,th) =
          if Literal.Set.null news then th
          else red (Literal.Set.foldl red1 (Literal.Set.empty,th) news)
    in
      fun th -> Rule.removeSym (red (Thm.clause th, th))
    ;;

end


(* ========================================================================= *)
(* CLAUSE = ID + THEOREM                                                     *)
(* ========================================================================= *)

module Clause = struct

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let newId =
      let r = ref 0

      in let newI () =
            let n = !r

            in let () = r := n + 1
          in
            n
    in
      fun () -> Useful.critical newI ()
    ;;

(* ------------------------------------------------------------------------- *)
(* A type of clause.                                                         *)
(* ------------------------------------------------------------------------- *)

type literalOrder =
    No_literal_order
  | Unsigned_literal_order
  | Positive_literal_order;;

type parameters =
     {ordering : Knuth_bendix_order.kbo;
      orderLiterals : literalOrder;
      orderTerms : bool};;

type clauseId = int;;

type clauseInfo = {parameters : parameters; id : clauseId; thm : Thm.thm};;

type clause = Clause of clauseInfo;;


(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

let toString (Clause {id=id;thm=thm}) = Thm.toString thm;;


(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let default : parameters =
    {ordering = Knuth_bendix_order.default;
     orderLiterals = Positive_literal_order;
     orderTerms = true};;

let mk info = Clause info

let dest (Clause info) = info;;

let id (Clause {id = i}) = i;;

let thm (Clause {thm = th}) = th;;

let equalThms cl cl' = Thm.equal (thm cl) (thm cl');;

let newClause parameters thm =
    Clause {parameters = parameters; id = newId (); thm = thm};;

let literals cl = Thm.clause (thm cl);;

let isTautology (Clause {thm=thm}) = Thm.isTautology thm;;

let isContradiction (Clause {thm=thm}) = Thm.isContradiction thm;;

(* ------------------------------------------------------------------------- *)
(* The term ordering is used to cut down inferences.                         *)
(* ------------------------------------------------------------------------- *)

let strictlyLess ordering x y =
    match Knuth_bendix_order.compare ordering x y with
      Some c when c < 0 -> true
    | _ -> false;;

let isLargerTerm ({ordering=ordering;orderTerms=orderTerms} : parameters) (l,r) =
    not orderTerms || not (strictlyLess ordering l r);;

  let atomToTerms atm =
      match Useful.total Atom.destEq atm with
        None -> [Term.Fn atm]
      | Some (l,r) -> [l;r];;

  let notStrictlyLess ordering (xs,ys) =
        let less x = List.exists (fun y -> strictlyLess ordering x y) ys
      in
        not (List.for_all less xs)
      ;;

  let isLargerLiteral ({ordering=ordering;orderLiterals=orderLiterals} : parameters) lits =
      match orderLiterals with
        No_literal_order -> K true
      | Unsigned_literal_order ->
          let addLit ((_,atm),acc) = atomToTerms atm @ acc

          in let tms = Literal.Set.foldl addLit [] lits
        in
          fun (_,atm') -> notStrictlyLess ordering (atomToTerms atm', tms)
      | Positive_literal_order ->
        match Literal.Set.findl (K true) lits with
          None -> K true
        | Some (pol,_) ->
            let addLit ((p,atm),acc) =
                if p = pol then atomToTerms atm @ acc else acc

            in let tms = Literal.Set.foldl addLit [] lits
          in
            fun (pol',atm') ->
               if pol <> pol' then pol
               else notStrictlyLess ordering (atomToTerms atm', tms)
          ;;


let largestLiterals (Clause {parameters=parameters;thm=thm}) =
      let litSet = Thm.clause thm
      in let isLarger = isLargerLiteral parameters litSet
      in let addLit (lit,s) = if isLarger lit then Literal.Set.add s lit else s
    in
      Literal.Set.foldr addLit Literal.Set.empty litSet
    ;;

(*MetisTrace6
let largestLiterals = fun cl ->
    let
      let ppResult = Literal.Set.pp
      let () = Print.trace pp "Clause.largestLiterals: cl" cl
      let result = largestLiterals cl
      let () = Print.trace ppResult "Clause.largestLiterals: result" result
    in
      result
    end;;
*)

let largestEquations (Clause {parameters=parameters} as cl) =
      let addEq lit ort ((l,_) as l_r) acc =
          if isLargerTerm parameters l_r then (lit,ort,l) :: acc else acc

      in let addLit (lit,acc) =
          match Useful.total Literal.destEq lit with
            None -> acc
          | Some (l,r) ->
              let acc = addEq lit Rewrite.Right_to_left (r,l) acc
              in let acc = addEq lit Rewrite.Left_to_right (l,r) acc
            in
              acc
    in
      Literal.Set.foldr addLit [] (largestLiterals cl)
    ;;

  let addLit (lit,acc) =
        let addTm ((path,tm),acc) = (lit,path,tm) :: acc
      in
        Mlist.foldl addTm acc (Literal.nonVarTypedSubterms lit)
      ;;

  let largestSubterms cl = Literal.Set.foldl addLit [] (largestLiterals cl);;

  let allSubterms cl = Literal.Set.foldl addLit [] (literals cl);;

(* ------------------------------------------------------------------------- *)
(* Subsumption.                                                              *)
(* ------------------------------------------------------------------------- *)

let subsumes (subs : clause Subsume.subsume) cl =
    Subsume.isStrictlySubsumed subs (literals cl);;

(* ------------------------------------------------------------------------- *)
(* Simplifying rules: these preserve the clause id.                          *)
(* ------------------------------------------------------------------------- *)

let freshVars (Clause {parameters=parameters;id=id;thm=thm}) =
    Clause {parameters = parameters; id = id; thm = Rule.freshVars thm};;

let simplify (Clause {parameters=parameters;id=id;thm=thm}) =
    match Rule.simplify thm with
      None -> None
    | Some thm -> Some (Clause {parameters = parameters; id = id; thm = thm});;

let reduce units (Clause {parameters=parameters;id=id;thm=thm}) =
    Clause {parameters = parameters; id = id; thm = Units.reduce units thm};;

let rewrite rewr (Clause {parameters=parameters;id=id;thm=thm}) =
      let simp th =
            let {ordering=ordering} = parameters
            in let cmp = Knuth_bendix_order.compare ordering
          in
            Rewrite.rewriteIdRule rewr cmp id th

(*MetisTrace4
      let () = Print.trace Rewrite.pp "Clause.rewrite: rewr" rewr
      let () = Print.trace Print.ppInt "Clause.rewrite: id" id
      let () = Print.trace pp "Clause.rewrite: cl" cl
*)

      in let thm =
          match Rewrite.peek rewr id with
            None -> simp thm
          | Some ((_,thm),_) -> if Rewrite.isReduced rewr then thm else simp thm

      in let result = Clause {parameters = parameters; id = id; thm = thm}

(*MetisTrace4
      let () = Print.trace pp "Clause.rewrite: result" result
*)
    in
      result;;
(*MetisDebug
    handle Failure err -> failwith "Clause.rewrite:\n" ^ err);;
*)

(* ------------------------------------------------------------------------- *)
(* Inference rules: these generate new clause ids.                           *)
(* ------------------------------------------------------------------------- *)

let factor (Clause {parameters=parameters;thm=thm} as cl) =
      let lits = largestLiterals cl

      in let apply sub = newClause parameters (Thm.subst sub thm)
    in
      List.map apply (Rule.factor' lits)
    ;;

(*MetisTrace5
let factor = fun cl ->
    let
      let () = Print.trace pp "Clause.factor: cl" cl
      let result = factor cl
      let () = Print.trace (Print.ppList pp) "Clause.factor: result" result
    in
      result
    end;;
*)

let resolve (cl1,lit1) (cl2,lit2) =
(*MetisTrace5
      let () = Print.trace pp "Clause.resolve: cl1" cl1
      let () = Print.trace Literal.pp "Clause.resolve: lit1" lit1
      let () = Print.trace pp "Clause.resolve: cl2" cl2
      let () = Print.trace Literal.pp "Clause.resolve: lit2" lit2
*)
      let Clause {parameters=parameters; thm = th1} = cl1
      and Clause {thm = th2} = cl2
      in let sub = Literal.unify Substitute.empty lit1 (Literal.negate lit2)
(*MetisTrace5
      let () = Print.trace Substitute.pp "Clause.resolve: sub" sub
*)
      in let lit1 = Literal.subst sub lit1
      in let lit2 = Literal.negate lit1
      in let th1 = Thm.subst sub th1
      and th2 = Thm.subst sub th2
      in let _ = isLargerLiteral parameters (Thm.clause th1) lit1 ||
(*MetisTrace5
              (trace "Clause.resolve: th1 violates ordering\n";; false) ||
*)
              failwith "resolve: clause1: ordering constraints"
      in let _ = isLargerLiteral parameters (Thm.clause th2) lit2 ||
(*MetisTrace5
              (trace "Clause.resolve: th2 violates ordering\n";; false) ||
*)
              failwith "resolve: clause2: ordering constraints"
      in let th = Thm.resolve lit1 th1 th2
(*MetisTrace5
      let () = Print.trace Thm.pp "Clause.resolve: th" th
*)
      in let cl = Clause {parameters = parameters; id = newId (); thm = th}
(*MetisTrace5
      let () = Print.trace pp "Clause.resolve: cl" cl
*)
    in
      cl
    ;;

let paramodulate (cl1,lit1,ort1,tm1) (cl2,lit2,path2,tm2) =
(*MetisTrace5
      let () = Print.trace pp "Clause.paramodulate: cl1" cl1
      let () = Print.trace Literal.pp "Clause.paramodulate: lit1" lit1
      let () = Print.trace Rewrite.ppOrient "Clause.paramodulate: ort1" ort1
      let () = Print.trace Term.pp "Clause.paramodulate: tm1" tm1
      let () = Print.trace pp "Clause.paramodulate: cl2" cl2
      let () = Print.trace Literal.pp "Clause.paramodulate: lit2" lit2
      let () = Print.trace Term.ppPath "Clause.paramodulate: path2" path2
      let () = Print.trace Term.pp "Clause.paramodulate: tm2" tm2
*)
      let Clause {parameters=parameters; thm = th1} = cl1
      and Clause {thm = th2} = cl2
      in let sub = Substitute.unify Substitute.empty tm1 tm2
      in let lit1 = Literal.subst sub lit1
      and lit2 = Literal.subst sub lit2
      and th1 = Thm.subst sub th1
      and th2 = Thm.subst sub th2

      in let _ = isLargerLiteral parameters (Thm.clause th1) lit1 ||
              failwith "Clause.paramodulate: with clause: ordering"
      in let _ = isLargerLiteral parameters (Thm.clause th2) lit2 ||
              failwith "Clause.paramodulate: into clause: ordering"

      in let eqn = (Literal.destEq lit1, th1)
      in let (l_r,_) as eqn =
          match ort1 with
            Rewrite.Left_to_right -> eqn
          | Rewrite.Right_to_left -> Rule.symEqn eqn
(*MetisTrace6
      let () = Print.trace Rule.ppEquation "Clause.paramodulate: eqn" eqn
*)
      in let _ = isLargerTerm parameters l_r ||
              failwith "Clause.paramodulate: equation: ordering constraints"
      in let th = Rule.rewrRule eqn lit2 path2 th2
(*MetisTrace5
      let () = Print.trace Thm.pp "Clause.paramodulate: th" th
*)
    in
      Clause {parameters = parameters; id = newId (); thm = th}
(*MetisTrace5
    handle Failure err ->
      let
        let () = trace ("Clause.paramodulate: failed: " ^ err ^ "\n")
      in
        raise Failure err
      end;;
*)


end


module Ax_cj = struct

type ax_cj_thm = {axioms_thm : Thm.thm list; conjecture_thm : Thm.thm list};;
type ax_cj_cl  = {axioms_cl : Clause.clause list; conjecture_cl : Clause.clause list};;

end

(* ========================================================================= *)
(* THE ACTIVE SET OF CLAUSES                                                 *)
(* ========================================================================= *)

module Active = struct

open Ax_cj

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

(*MetisDebug
local
  let mkRewrite ordering =
      let
        let add (cl,rw) =
            let
              let {id, thm = th, ...} = Clause.dest cl
            in
              match Useful.total Thm.destUnitEq th with
                Some l_r -> Rewrite.add rw (id,(l_r,th))
              | None -> rw
            end
      in
        Mlist.foldl add (Rewrite.new (Knuth_bendix_order.compare ordering))
      end;;

  let allFactors red =
      let
        let allClause cl =
            List.all red (cl :: Clause.factor cl) ||
            let
              let () = Print.trace Clause.pp
                         "Active.isSaturated.allFactors: cl" cl
            in
              false
            end
      in
        List.all allClause
      end;;

  let allResolutions red =
      let
        let allClause2 cl_lit cl =
            let
              let allLiteral2 lit =
                  match Useful.total (Clause.resolve cl_lit) (cl,lit) with
                    None -> true
                  | Some cl -> allFactors red [cl]
            in
              Literal.Set.all allLiteral2 (Clause.literals cl)
            end ||
            let
              let () = Print.trace Clause.pp
                         "Active.isSaturated.allResolutions: cl2" cl
            in
              false
            end

        let allClause1 allCls cl =
            let
              let cl = Clause.freshVars cl

              let allLiteral1 lit = List.all (allClause2 (cl,lit)) allCls
            in
              Literal.Set.all allLiteral1 (Clause.literals cl)
            end ||
            let
              let () = Print.trace Clause.pp
                         "Active.isSaturated.allResolutions: cl1" cl
            in
              false
            end

      in
        fun [] -> true
         | allCls as cl :: cls ->
           allClause1 allCls cl && allResolutions red cls
      end;;

  let allParamodulations red cls =
      let
        let allClause2 cl_lit_ort_tm cl =
            let
              let allLiteral2 lit =
                  let
                    let para = Clause.paramodulate cl_lit_ort_tm

                    let allSubterms (path,tm) =
                        match Useful.total para (cl,lit,path,tm) with
                          None -> true
                        | Some cl -> allFactors red [cl]
                  in
                    List.all allSubterms (Literal.nonVarTypedSubterms lit)
                  end ||
                  let
                    let () = Print.trace Literal.pp
                               "Active.isSaturated.allParamodulations: lit2" lit
                  in
                    false
                  end
            in
              Literal.Set.all allLiteral2 (Clause.literals cl)
            end ||
            let
              let () = Print.trace Clause.pp
                         "Active.isSaturated.allParamodulations: cl2" cl
              let (_,_,ort,_) = cl_lit_ort_tm
              let () = Print.trace Rewrite.ppOrient
                         "Active.isSaturated.allParamodulations: ort1" ort
            in
              false
            end

        let allClause1 cl =
            let
              let cl = Clause.freshVars cl

              let allLiteral1 lit =
                  let
                    let allCl2 x = List.all (allClause2 x) cls
                  in
                    match Useful.total Literal.destEq lit with
                      None -> true
                    | Some (l,r) ->
                      allCl2 (cl,lit,Rewrite.Left_to_right,l) &&
                      allCl2 (cl,lit,Rewrite.Right_to_left,r)
                  end ||
                  let
                    let () = Print.trace Literal.pp
                               "Active.isSaturated.allParamodulations: lit1" lit
                  in
                    false
                  end
            in
              Literal.Set.all allLiteral1 (Clause.literals cl)
            end ||
            let
              let () = Print.trace Clause.pp
                         "Active.isSaturated.allParamodulations: cl1" cl
            in
              false
            end
      in
        List.all allClause1 cls
      end;;

  let redundant {subsume,reduce,rewrite} =
      let
        let simp cl =
            match Clause.simplify cl with
              None -> true
            | Some cl ->
              Subsume.isStrictlySubsumed subsume (Clause.literals cl) ||
              let
                let cl' = cl
                let cl' = Clause.reduce reduce cl'
                let cl' = Clause.rewrite rewrite cl'
              in
                not (Clause.equalThms cl cl') &&
                (simp cl' ||
                 let
                   let () = Print.trace Clause.pp
                              "Active.isSaturated.redundant: cl'" cl'
                 in
                   false
                 end)
              end
      in
        fun cl ->
           simp cl ||
           let
             let () = Print.trace Clause.pp
                        "Active.isSaturated.redundant: cl" cl
           in
             false
           end
      end;;
in
  let isSaturated ordering subs cls =
      let
        let rd = Units.empty
        let rw = mkRewrite ordering cls
        let red = redundant {subsume = subs, reduce = rd, rewrite = rw}
      in
        (allFactors red cls &&
         allResolutions red cls &&
         allParamodulations red cls) ||
        let
          let () = Print.trace Rewrite.pp "Active.isSaturated: rw" rw
          let () = Print.trace (Print.ppList Clause.pp)
                     "Active.isSaturated: clauses" cls
        in
          false
        end
      end;;
end;;

let checkSaturated ordering subs cls =
    if isSaturated ordering subs cls then ()
    else raise (Useful.Bug "Active.checkSaturated");;
*)

(* ------------------------------------------------------------------------- *)
(* A type of active clause sets.                                             *)
(* ------------------------------------------------------------------------- *)

type simplify = {subsumes : bool; reduce : bool; rewrites : bool};;

type parameters =
     {clause : Clause.parameters;
      prefactor : simplify;
      postfactor : simplify};;

type active_t =
      {parameters : parameters;
       clauses : Clause.clause Intmap.map;
       units : Units.units;
       rewrite : Rewrite.rewrite;
       subsume : Clause.clause Subsume.subsume;
       literals : (Clause.clause * Literal.literal) Literal_net.literalNet;
       equations :
         (Clause.clause * Literal.literal * Rewrite.orient * Term.term)
         Term_net.termNet;
       subterms :
         (Clause.clause * Literal.literal * Term.path * Term.term)
         Term_net.termNet;
       allSubterms : (Clause.clause * Term.term) Term_net.termNet};;

type active =
    Active of active_t;;

let getSubsume (Active {subsume = s}) = s;;

let setRewrite active rewrite =
      let Active
            {parameters=parameters;clauses=clauses;units=units;subsume=subsume;literals=literals;equations=equations;
             subterms=subterms;allSubterms=allSubterms} = active
    in
      Active
        {parameters = parameters; clauses = clauses; units = units;
         rewrite = rewrite; subsume = subsume; literals = literals;
         equations = equations; subterms = subterms; allSubterms = allSubterms}
    ;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let maxSimplify : simplify = {subsumes = true; reduce = true; rewrites = true};;

let default : parameters =
    {clause = Clause.default;
     prefactor = maxSimplify;
     postfactor = maxSimplify};;

open Term_net
let empty parameters =
      let {clause=clause} = parameters
      in let {Clause.ordering=ordering} = clause
    in
      Active
        {parameters = parameters;
         clauses = Intmap.newMap ();
         units = Units.empty;
         rewrite = Rewrite.newRewrite (Knuth_bendix_order.compare ordering);
         subsume = Subsume.newSubsume ();
         literals = Literal_net.newNet {fifo = false};
         equations = Term_net.newNet {fifo = false};
         subterms = Term_net.newNet {fifo = false};
         allSubterms = Term_net.newNet {fifo = false}}
    ;;

let size (Active {clauses=clauses}) = Intmap.size clauses;;

let clauses (Active {clauses = cls}) =
      let add (_,cl,acc) = cl :: acc
    in
      Intmap.foldr add [] cls
    ;;

let saturation active =
      let remove (cl,(cls,subs)) =
            let lits = Clause.literals cl
          in
            if Subsume.isStrictlySubsumed subs lits then (cls,subs)
            else (cl :: cls, Subsume.insert subs (lits,()))

      in let cls = clauses active
      in let (cls,_) = Mlist.foldl remove ([], Subsume.newSubsume ()) cls
      in let (cls,subs) = Mlist.foldl remove ([], Subsume.newSubsume ()) cls

(*MetisDebug
      let Active {parameters,...} = active
      let {clause,...} = parameters
      let {ordering,...} = clause
      let () = checkSaturated ordering subs cls
*)
    in
      cls
    ;;


(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

let toString active = "Active{" ^ string_of_int (size active) ^ "}";;


(* ------------------------------------------------------------------------- *)
(* Simplify clauses.                                                         *)
(* ------------------------------------------------------------------------- *)

let simplify simp units rewr subs =
      let {subsumes = s; reduce = r; rewrites = w} = simp

      in let rec rewrite cl =
            let cl' = Clause.rewrite rewr cl
          in
            if Clause.equalThms cl cl' then Some cl
            else
              match Clause.simplify cl' with
                None -> None
              | Some cl'' ->
                (*                                                         *)
                (* Post-rewrite simplification can enable more rewrites:   *)
                (*                                                         *)
                (*  ~(X = f(X)) \/ ~(g(Y) = f(X)) \/ ~(c = f(X))           *)
                (* ---------------------------------------------- rewrite  *)
                (*  ~(X = f(X)) \/ ~(g(Y) = X) \/ ~(c = X)                 *)
                (* ---------------------------------------------- simplify *)
                (*  ~(g(Y) = f(g(Y))) \/ ~(c = g(Y))                       *)
                (* ---------------------------------------------- rewrite  *)
                (*  ~(c = f(c)) \/ ~(c = g(Y))                             *)
                (*                                                         *)
                (* This was first observed in a bug discovered by Martin   *)
                (* Desharnais and Jasmin Blanchett                         *)
                (*                                                         *)
                if Clause.equalThms cl' cl'' then Some cl' else rewrite cl''
    in
      fun cl ->
         match Clause.simplify cl with
           None -> None
         | Some cl ->
           match (if w then rewrite cl else Some cl) with
             None -> None
           | Some cl ->
               let cl = if r then Clause.reduce units cl else cl
             in
               if s && Clause.subsumes subs cl then None else Some cl
    ;;

(*MetisDebug
let simplify = fun simp -> fun units -> fun rewr -> fun subs -> fun cl ->
    let
      let traceCl s = Print.trace Clause.pp ("Active.simplify: " ^ s)
(*MetisTrace4
      let ppClOpt = Print.ppOption Clause.pp
      let () = traceCl "cl" cl
*)
      let cl' = simplify simp units rewr subs cl
(*MetisTrace4
      let () = Print.trace ppClOpt "Active.simplify: cl'" cl'
*)
      let () =
          match cl' with
            None -> ()
          | Some cl' ->
            case
              (match simplify simp units rewr subs cl' with
                 None -> Some ("away", K ())
               | Some cl'' ->
                 if Clause.equalThms cl' cl'' then None
                 else Some ("further", fun () -> traceCl "cl''" cl'')) of
              None -> ()
            | Some (e,f) ->
              let
                let () = traceCl "cl" cl
                let () = traceCl "cl'" cl'
                let () = f ()
              in
                raise
                  Useful.Bug
                    ("Active.simplify: clause should have been simplified "^e)
              end
    in
      cl'
    end;;
*)

let simplifyActive simp active =
      let Active {units=units;rewrite=rewrite;subsume=subsume} = active
    in
      simplify simp units rewrite subsume
    ;;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set.                                         *)
(* ------------------------------------------------------------------------- *)

let addUnit units cl =
      let th = Clause.thm cl
    in
      match Useful.total Thm.destUnit th with
        Some lit -> Units.add units (lit,th)
      | None -> units
    ;;

let addRewrite rewrite cl =
      let th = Clause.thm cl
    in
      match Useful.total Thm.destUnitEq th with
        Some l_r -> Rewrite.add rewrite (Clause.id cl, (l_r,th))
      | None -> rewrite
    ;;

let addSubsume subsume cl = Subsume.insert subsume (Clause.literals cl, cl);;

let addLiterals literals cl =
      let add ((_,atm) as lit, literals) =
          if Atom.isEq atm then literals
          else Literal_net.insert literals (lit,(cl,lit))
    in
      Literal.Set.foldl add literals (Clause.largestLiterals cl)
    ;;

let addEquations equations cl =
      let add ((lit,ort,tm),equations) =
          Term_net.insert equations (tm,(cl,lit,ort,tm))
    in
      Mlist.foldl add equations (Clause.largestEquations cl)
    ;;

let addSubterms subterms cl =
      let add ((lit,path,tm),subterms) =
          Term_net.insert subterms (tm,(cl,lit,path,tm))
    in
      Mlist.foldl add subterms (Clause.largestSubterms cl)
    ;;

let addAllSubterms allSubterms cl =
      let add ((_,_,tm),allSubterms) =
          Term_net.insert allSubterms (tm,(cl,tm))
    in
      Mlist.foldl add allSubterms (Clause.allSubterms cl)
    ;;

let addClause active cl =
      let Active
            {parameters=parameters;clauses=clauses;units=units;rewrite=rewrite;subsume=subsume;literals=literals;
             equations=equations;subterms=subterms;allSubterms=allSubterms} = active
      in let clauses = Intmap.insert clauses (Clause.id cl, cl)
      and subsume = addSubsume subsume cl
      and literals = addLiterals literals cl
      and equations = addEquations equations cl
      and subterms = addSubterms subterms cl
      and allSubterms = addAllSubterms allSubterms cl
    in
      Active
        {parameters = parameters; clauses = clauses; units = units;
         rewrite = rewrite; subsume = subsume; literals = literals;
         equations = equations; subterms = subterms;
         allSubterms = allSubterms}
    ;;

let addFactorClause active cl =
      let Active
            {parameters=parameters;clauses=clauses;units=units;rewrite=rewrite;subsume=subsume;literals=literals;
             equations=equations;subterms=subterms;allSubterms=allSubterms} = active
      in let units = addUnit units cl
      and rewrite = addRewrite rewrite cl
    in
      Active
        {parameters = parameters; clauses = clauses; units = units;
         rewrite = rewrite; subsume = subsume; literals = literals;
         equations = equations; subterms = subterms; allSubterms = allSubterms}
    ;;

(* ------------------------------------------------------------------------- *)
(* Derive (unfactored) consequences of a clause.                             *)
(* ------------------------------------------------------------------------- *)

let deduceResolution literals cl ((_,atm) as lit, acc) =
      let resolve (cl_lit,acc) =
          (*let (cl1, lit1) = cl_lit in
          print_endline ("cl1 = " ^ Clause.toString cl1);
          print_endline ("lit1 = " ^ Literal.toString lit1);
          print_endline ("cl = " ^ Clause.toString cl);
          print_endline ("lit = " ^ Literal.toString lit);*)
          match Useful.total (Clause.resolve cl_lit) (cl,lit) with
            Some cl' -> cl' :: acc
          | None -> acc
(*MetisTrace4
      let () = Print.trace Literal.pp "Active.deduceResolution: lit" lit
*)
    in
      if Atom.isEq atm then acc
      else
        Mlist.foldl resolve acc (Literal_net.unify literals (Literal.negate lit))
    ;;

let deduceParamodulationWith subterms cl ((lit,ort,tm),acc) =
      let para (cl_lit_path_tm,acc) =
          match Useful.total (Clause.paramodulate (cl,lit,ort,tm)) cl_lit_path_tm with
            Some cl' -> cl' :: acc
          | None -> acc
    in
      Mlist.foldl para acc (Term_net.unify subterms tm)
    ;;

let deduceParamodulationInto equations cl ((lit,path,tm),acc) =
      let para (cl_lit_ort_tm,acc) =
          match Useful.total (Clause.paramodulate cl_lit_ort_tm) (cl,lit,path,tm) with
            Some cl' -> cl' :: acc
          | None -> acc
    in
      Mlist.foldl para acc (Term_net.unify equations tm)
    ;;

let deduce active cl =
      let Active {parameters=parameters;literals=literals;equations=equations;subterms=subterms} = active

      in let lits = Clause.largestLiterals cl
      in let eqns = Clause.largestEquations cl
      in let subtms =
          if Term_net.null equations then [] else Clause.largestSubterms cl
(*MetisTrace5
      let () = Print.trace Literal.Set.pp "Active.deduce: lits" lits
      let () = Print.trace
                 (Print.ppList
                    (Print.ppMap (fun (lit,ort,_) -> (lit,ort))
                      (Print.ppPair Literal.pp Rewrite.ppOrient)))
                 "Active.deduce: eqns" eqns
      let () = Print.trace
                 (Print.ppList
                    (Print.ppTriple Literal.pp Term.ppPath Term.pp))
                 "Active.deduce: subtms" subtms
*)

      in let acc = []
      in let acc = Literal.Set.foldl (deduceResolution literals cl) acc lits
      in let acc = Mlist.foldl (deduceParamodulationWith subterms cl) acc eqns
      in let acc = Mlist.foldl (deduceParamodulationInto equations cl) acc subtms
      in let acc = List.rev acc

(*MetisTrace5
      let () = Print.trace (Print.ppList Clause.pp) "Active.deduce: acc" acc
*)
    in
      acc
    ;;

(* ------------------------------------------------------------------------- *)
(* Extract clauses from the active set that can be simplified.               *)
(* ------------------------------------------------------------------------- *)

  let clause_rewritables active =
        let Active {clauses=clauses;rewrite=rewrite} = active

        in let rewr (id,cl,ids) =
              let cl' = Clause.rewrite rewrite cl
            in
              if Clause.equalThms cl cl' then ids else Intset.add ids id
      in
        Intmap.foldr rewr Intset.empty clauses
      ;;

  let orderedRedexResidues (((l,r),_),ort) =
      match ort with
        None -> []
      | Some Rewrite.Left_to_right -> [(l,r,true)]
      | Some Rewrite.Right_to_left -> [(r,l,true)];;

  let unorderedRedexResidues (((l,r),_),ort) =
      match ort with
        None -> [(l,r,false);(r,l,false)]
      | Some _ -> [];;

  let rewrite_rewritables active rewr_ids =
        let Active {parameters=parameters;rewrite=rewrite;clauses=clauses;allSubterms=allSubterms} = active
        in let {clause = {Clause.ordering=ordering}} = parameters
        in let order = Knuth_bendix_order.compare ordering

        in let addRewr (id,acc) =
            if Intmap.inDomain id clauses then Intset.add acc id else acc

        in let addReduce ((l,r,ord),acc) =
              let isValidRewr tm =
                  match Useful.total (Substitute.matchTerms Substitute.empty l) tm with
                    None -> false
                  | Some sub ->
                    ord ||
                      let tm' = Substitute.subst (Substitute.normalize sub) r
                    in
                      order tm tm' = Some 1

              in let addRed ((cl,tm),acc) =
(*MetisTrace5
                    let () = Print.trace Clause.pp "Active.addRed: cl" cl
                    let () = Print.trace Term.pp "Active.addRed: tm" tm
*)
                    let id = Clause.id cl
                  in
                    if Intset.member id acc then acc
                    else if not (isValidRewr tm) then acc
                    else Intset.add acc id

(*MetisTrace5
              let () = Print.trace Term.pp "Active.addReduce: l" l
              let () = Print.trace Term.pp "Active.addReduce: r" r
              let () = Print.trace Print.ppBool "Active.addReduce: ord" ord
*)
            in
              Mlist.foldl addRed acc (Term_net.matched allSubterms l)

        in let addEquation redexResidues (id,acc) =
            match Rewrite.peek rewrite id with
              None -> acc
            | Some eqn_ort -> Mlist.foldl addReduce acc (redexResidues eqn_ort)

        in let addOrdered = addEquation orderedRedexResidues

        in let addUnordered = addEquation unorderedRedexResidues

        in let ids = Intset.empty
        in let ids = Mlist.foldl addRewr ids rewr_ids
        in let ids = Mlist.foldl addOrdered ids rewr_ids
        in let ids = Mlist.foldl addUnordered ids rewr_ids
      in
        ids
      ;;

  let choose_clause_rewritables active ids = size active <= length ids

  let rewritables active ids =
      if choose_clause_rewritables active ids then clause_rewritables active
      else rewrite_rewritables active ids;;

(*MetisDebug
  let rewritables = fun active -> fun ids ->
      let
        let clause_ids = clause_rewritables active
        let rewrite_ids = rewrite_rewritables active ids

        let () =
            if Intset.equal rewrite_ids clause_ids then ()
            else
              let
                let ppIdl = Print.ppList Print.ppInt
                let ppIds = Print.ppMap Intset.toList ppIdl
                let () = Print.trace pp "Active.rewritables: active" active
                let () = Print.trace ppIdl "Active.rewritables: ids" ids
                let () = Print.trace ppIds
                           "Active.rewritables: clause_ids" clause_ids
                let () = Print.trace ppIds
                           "Active.rewritables: rewrite_ids" rewrite_ids
              in
                raise Useful.Bug "Active.rewritables: ~(rewrite_ids SUBSET clause_ids)"
              end
      in
        if choose_clause_rewritables active ids then clause_ids else rewrite_ids
      end;;
*)

  let delete active ids =
      if Intset.null ids then active
      else
          let idPred id = not (Intset.member id ids)

          in let clausePred cl = idPred (Clause.id cl)

          in let Active
                {parameters=parameters;
                 clauses=clauses;
                 units=units;
                 rewrite=rewrite;
                 subsume=subsume;
                 literals=literals;
                 equations=equations;
                 subterms=subterms;
                 allSubterms=allSubterms} = active

          in let cP1 (x,_) = clausePred x
          in let cP1_4 (x,_,_,_) = clausePred x
          in let clauses = Intmap.filter (fun x -> idPred (fst x)) clauses
          and subsume = Subsume.filter clausePred subsume
          and literals = Literal_net.filter cP1 literals
          and equations = Term_net.filter cP1_4 equations
          and subterms = Term_net.filter cP1_4 subterms
          and allSubterms = Term_net.filter cP1 allSubterms
        in
          Active
            {parameters = parameters;
             clauses = clauses;
             units = units;
             rewrite = rewrite;
             subsume = subsume;
             literals = literals;
             equations = equations;
             subterms = subterms;
             allSubterms = allSubterms}
        ;;

  let extract_rewritables (Active {clauses=clauses;rewrite=rewrite} as active) =
      if Rewrite.isReduced rewrite then (active,[])
      else
(*MetisTrace3
          let () = trace "Active.extract_rewritables: inter-reducing\n"
*)
          let (rewrite,ids) = Rewrite.reduce' rewrite
          in let active = setRewrite active rewrite
          in let ids = rewritables active ids
          in let cls = Intset.transform (Intmap.get clauses) ids
(*MetisTrace3
          let ppCls = Print.ppList Clause.pp
          let () = Print.trace ppCls "Active.extract_rewritables: cls" cls
*)
        in
          (delete active ids, cls)
(*MetisDebug
        handle Failure err ->
          raise (Useful.Bug ("Active.extract_rewritables: shouldn't fail\n" ^ err));;
*)
;;

(* ------------------------------------------------------------------------- *)
(* Factor clauses.                                                           *)
(* ------------------------------------------------------------------------- *)

  let prefactor_simplify active subsume =
        let Active {parameters=parameters;units=units;rewrite=rewrite} = active
        in let {prefactor=prefactor} = parameters
      in
        simplify prefactor units rewrite subsume
      ;;

  let postfactor_simplify active subsume =
        let Active {parameters=parameters;units=units;rewrite=rewrite} = active
        in let {postfactor=postfactor} = parameters
      in
        simplify postfactor units rewrite subsume
      ;;

  let sort_utilitywise =
        let utility cl =
            match Literal.Set.size (Clause.literals cl) with
              0 -> -1
            | 1 -> if Thm.isUnitEq (Clause.thm cl) then 0 else 1
            | n -> n
      in
        Mlist.sortMap utility Useful.intCompare
      ;;

  let rec post_factor (cl, ((active,subsume,acc) as active_subsume_acc)) =
      match postfactor_simplify active subsume cl with
        None -> active_subsume_acc
      | Some cl' ->
          if Clause.equalThms cl' cl then
            let active = addFactorClause active cl
            and subsume = addSubsume subsume cl
            and acc = cl :: acc
            in (active,subsume,acc)
          else
            (* If the clause was changed in the post-factor simplification *)
            (* step, then it may have altered the set of largest literals *)
            (* in the clause. The safest thing to do is to factor again. *)
            factor1 (cl', active_subsume_acc)

  and factor1 (cl, active_subsume_acc) =
      let cls = sort_utilitywise (cl :: Clause.factor cl)
      in Mlist.foldl post_factor active_subsume_acc cls
      ;;

  let pre_factor (cl, ((active,subsume,_) as active_subsume_acc)) =
      match prefactor_simplify active subsume cl with
        None -> active_subsume_acc
      | Some cl -> factor1 (cl, active_subsume_acc)
      ;;

  let rec factor' active acc = function
      [] -> (active, List.rev acc)
    | cls ->
        let cls = sort_utilitywise cls
        in let subsume = getSubsume active
        in let (active,_,acc) = Mlist.foldl pre_factor (active,subsume,acc) cls
        in let (active,cls) = extract_rewritables active
      in
        factor' active acc cls
      ;;

  let factor active cls = factor' active [] cls;;

(*let factor active cls =
  let str cl = String.concat "\n" (List.map Clause.toString cl) in
  print_endline ("Active.factor: cls:\n" ^ str cls);
  let (active,cls') = factor active cls in
  print_endline ("Active.factor: cls':\n" ^ str cls');
  (active, cls');;
*)

(*MetisTrace4
let factor = fun active -> fun cls ->
    let
      let ppCls = Print.ppList Clause.pp
      let () = Print.trace ppCls "Active.factor: cls" cls
      let (active,cls') = factor active cls
      let () = Print.trace ppCls "Active.factor: cls'" cls'
    in
      (active,cls')
    end;;
*)

(* ------------------------------------------------------------------------- *)
(* Create a new active clause set and initialize clauses.                    *)
(* ------------------------------------------------------------------------- *)

let mk_clause params th =
  Clause.mk {Clause.parameters = params; Clause.id = Clause.newId (); Clause.thm = th};;

let newActive parameters {axioms_thm=axioms_thm;conjecture_thm=conjecture_thm} =
      let {clause=clause} = parameters

      in let mk_clause = mk_clause clause
      in let active = empty parameters
      in let (active,axioms) = factor active (List.map mk_clause axioms_thm)
      in let (active,conjecture) = factor active (List.map mk_clause conjecture_thm)
    in
      (active, {axioms_cl = axioms; conjecture_cl = conjecture})
    ;;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set and deduce all consequences.             *)
(* ------------------------------------------------------------------------- *)

let add active cl =
    match simplifyActive maxSimplify active cl with
      None -> (active,[])
    | Some cl' ->
      if Clause.isContradiction cl' then (active,[cl'])
      else if not (Clause.equalThms cl cl') then factor active [cl']
      else
(*MetisTrace2
          let () = Print.trace Clause.pp "Active.add: cl" cl
*)
          let active = addClause active cl
          in let cl = Clause.freshVars cl
          in let cls = deduce active cl
          in let (active,cls) = factor active cls
(*MetisTrace2
          let ppCls = Print.ppList Clause.pp
          let () = Print.trace ppCls "Active.add: cls" cls
*)
        in
          (active,cls)
        ;;

end


(* ========================================================================= *)
(* THE WAITING SET OF CLAUSES                                                *)
(* ========================================================================= *)

module Waiting = struct

open Ax_cj

(* ------------------------------------------------------------------------- *)
(* A type of waiting sets of clauses.                                        *)
(* ------------------------------------------------------------------------- *)

type weight = float;;

type modelParameters =
     {model : Model.parameters;
      initialPerturbations : int;
      maxChecks : int option;
      perturbations : int;
      weight : weight}

type parameters =
     {symbolsWeight : weight;
      variablesWeight : weight;
      literalsWeight : weight;
      modelsP : modelParameters list};;

type distance = float;;

type waiting_t =
      {parameters : parameters;
       clauses : (weight * (distance * Clause.clause)) Heap.heap;
       models : Model.model list};;

type waiting =
    Waiting of waiting_t;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let defaultModels : modelParameters list =
    [{model = Model.default;
      initialPerturbations = 100;
      maxChecks = Some 20;
      perturbations = 0;
      weight = 1.0}];;

let default : parameters =
     {symbolsWeight = 1.0;
      literalsWeight = 1.0;
      variablesWeight = 1.0;
      modelsP = defaultModels};;

let size (Waiting {clauses=clauses}) = Heap.size clauses;;

let toString w = "Waiting{" ^ string_of_int (size w) ^ "}";;

(*let toString (Waiting {clauses}) = "\n" ^
  String.concat "\n" (List.map (fun (w, (d, c)) -> Clause.toString c) (Heap.toList clauses));;*)


(*MetisDebug
let pp =
    Print.ppMap
      (fun Waiting {clauses,...} ->
          List.map (fun (w,(_,cl)) -> (w, Clause.id cl, cl)) (Heap.toList clauses))
      (Print.ppList (Print.ppTriple Print.ppReal Print.ppInt Clause.pp));;
*)

(* ------------------------------------------------------------------------- *)
(* Perturbing the models.                                                    *)
(* ------------------------------------------------------------------------- *)

type modelClause = Name.Set.set * Thm.clause;;

let mkModelClause cl =
      let lits = Clause.literals cl
      in let fvs = Literal.Set.freeVars lits
    in
      (fvs,lits)
    ;;

let mkModelClauses = List.map mkModelClause;;

let perturbModel vM cls =
    if Mlist.null cls then K ()
    else
        let vN = {Model.size = Model.msize vM}

        in let perturbClause (fv,cl) =
              let vV = Model.randomValuation vN fv
            in
              if Model.interpretClause vM vV cl then ()
              else Model.perturbClause vM vV cl

        in let perturbClauses () = List.iter perturbClause cls
      in
        fun n -> funpow n perturbClauses ()
      ;;

let initialModel axioms conjecture parm =
      let {model=model;initialPerturbations=initialPerturbations}  = parm
      in let m = Model.newModel model
      in let () = perturbModel m conjecture initialPerturbations
      in let () = perturbModel m axioms initialPerturbations
    in
      m
    ;;

let checkModels parms models (fv,cl) =
      let check ((parm,model),z) =
            let {maxChecks=maxChecks;weight=weight} = parm
            in let n = maxChecks
            in let (vT,vF) = Model.check Model.interpretClause n model fv cl
          in
            (1.0 +. float_of_int vT /. float_of_int (vT + vF) ** weight) *. z
    in
      Mlist.foldl check 1.0 (zip parms models)
    ;;

let perturbModels parms models cls =
      let perturb (parm,model) =
            let {perturbations=perturbations} = parm
          in
            perturbModel model cls perturbations
    in
      List.iter perturb (zip parms models)
    ;;

(* ------------------------------------------------------------------------- *)
(* Clause weights.                                                           *)
(* ------------------------------------------------------------------------- *)

  let clauseSymbols cl = float_of_int (Literal.Set.typedSymbols cl);;

  let clauseVariables cl =
      float_of_int (Name.Set.size (Literal.Set.freeVars cl) + 1);;

  let clauseLiterals cl = float_of_int (Literal.Set.size cl);;

  let clausePriority cl = 1e-12 *. float_of_int (Clause.id cl);;

  let clauseWeight (parm : parameters) mods dist mcl cl =
(*MetisTrace3
        let () = Print.trace Clause.pp "Waiting.clauseWeight: cl" cl
*)
        let {symbolsWeight=symbolsWeight;variablesWeight=variablesWeight;literalsWeight=literalsWeight;modelsP=modelsP} = parm
        in let lits = Clause.literals cl
        in let symbolsW = clauseSymbols lits ** symbolsWeight
        in let variablesW = clauseVariables lits ** variablesWeight
        in let literalsW = clauseLiterals lits ** literalsWeight
        in let modelsW = checkModels modelsP mods mcl
(*MetisTrace4
        let () = trace ("Waiting.clauseWeight: dist = " ^
                        string_of_float dist ^ "\n")
        let () = trace ("Waiting.clauseWeight: symbolsW = " ^
                        string_of_float symbolsW ^ "\n")
        let () = trace ("Waiting.clauseWeight: variablesW = " ^
                        string_of_float variablesW ^ "\n")
        let () = trace ("Waiting.clauseWeight: literalsW = " ^
                        string_of_float literalsW ^ "\n")
        let () = trace ("Waiting.clauseWeight: modelsW = " ^
                        string_of_float modelsW ^ "\n")
*)
        in let weight = dist *. symbolsW *. variablesW *. literalsW *. modelsW
        in let weight = weight +. clausePriority cl
(*MetisTrace3
        let () = trace ("Waiting.clauseWeight: weight = " ^
                        string_of_float weight ^ "\n")
*)
      in
        weight
      ;;

(* ------------------------------------------------------------------------- *)
(* Adding new clauses.                                                       *)
(* ------------------------------------------------------------------------- *)

let add' waiting dist mcls cls =
      let Waiting {parameters=parameters;clauses=clauses;models=models} = waiting
      in let {modelsP = modelParameters} = parameters

(*MetisDebug
      let _ = not (Mlist.null cls) ||
              raise Useful.Bug "Waiting.add': null"

      let _ = length mcls = length cls ||
              raise Useful.Bug "Waiting.add': different lengths"
*)

      in let dist = dist +. log (float_of_int (length cls))

      in let addCl ((mcl,cl),acc) =
            let weight = clauseWeight parameters models dist mcl cl
          in
            Heap.add acc (weight,(dist,cl))

      in let clauses = Mlist.foldl addCl clauses (zip mcls cls)

      in let () = perturbModels modelParameters models mcls
    in
      Waiting {parameters = parameters; clauses = clauses; models = models}
    ;;

let add waiting (dist,cls) =
    if Mlist.null cls then waiting
    else
(*MetisTrace3
        let () = Print.trace pp "Waiting.add: waiting" waiting
        let () = Print.trace (Print.ppList Clause.pp) "Waiting.add: cls" cls
*)

        let waiting = add' waiting dist (mkModelClauses cls) cls

(*MetisTrace3
        let () = Print.trace pp "Waiting.add: waiting" waiting
*)
      in
        waiting
      ;;

  let cmp ((w1 : float),_) (w2,_) = compare w1 w2;;

  let empty parameters axioms conjecture =
        let {modelsP = modelParameters} = parameters
        in let clauses = Heap.newHeap cmp
        and models = List.map (initialModel axioms conjecture) modelParameters
      in
        Waiting {parameters = parameters; clauses = clauses; models = models}
      ;;

  let newWaiting parameters {axioms_cl=axioms_cl;conjecture_cl=conjecture_cl} =
        let mAxioms = mkModelClauses axioms_cl
        and mConjecture = mkModelClauses conjecture_cl

        in let waiting = empty parameters mAxioms mConjecture
      in
        if Mlist.null axioms_cl && Mlist.null conjecture_cl then waiting
        else add' waiting 0.0 (mAxioms @ mConjecture) (axioms_cl @ conjecture_cl)
(*MetisDebug
      handle e ->
        let
          let () = Print.trace Print.ppException "Waiting.new: exception" e
        in
          raise e
        end;;
*)

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause.                                             *)
(* ------------------------------------------------------------------------- *)

let remove (Waiting {parameters=parameters;clauses=clauses;models=models}) =
    if Heap.null clauses then None
    else
        let ((_,dcl),clauses) = Heap.remove clauses

        in let waiting =
            Waiting
              {parameters = parameters;
               clauses = clauses;
               models = models}
      in
        Some (dcl,waiting)
      ;;

end


(* ========================================================================= *)
(* THE RESOLUTION PROOF PROCEDURE                                            *)
(* ========================================================================= *)

module Resolution = struct

(* ------------------------------------------------------------------------- *)
(* A type of resolution proof procedures.                                    *)
(* ------------------------------------------------------------------------- *)

type parameters =
     {activeP : Active.parameters;
      waitingP : Waiting.parameters};;

type resolution_t =
      {parameters : parameters;
       active : Active.active;
       waiting : Waiting.waiting};;

type resolution =
    Resolution of resolution_t;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let default : parameters =
    {activeP = Active.default;
     waitingP = Waiting.default};;

let newResolution parameters ths =
      let {activeP = activeParm; waitingP = waitingParm} = parameters

      in let (active,cls) = Active.newActive activeParm ths  (* cls = factored ths *)

      in let waiting = Waiting.newWaiting waitingParm cls
    in
      Resolution {parameters = parameters; active = active; waiting = waiting};;
(*MetisDebug
    handle e ->
      let
        let () = Print.trace Print.ppException "Resolution.new: exception" e
      in
        raise e
      end;;
*)

let active (Resolution {active = a}) = a;;

let waiting (Resolution {waiting = w}) = w;;


(* ------------------------------------------------------------------------- *)
(* The main proof loop.                                                      *)
(* ------------------------------------------------------------------------- *)

type decision =
    Contradiction of Thm.thm
  | Satisfiable of Thm.thm list;;

type state =
    Decided of decision
  | Undecided of resolution;;

let iterate res =
      let Resolution {parameters=parameters;active=active;waiting=waiting} = res

(*MetisTrace2
      let () = Print.trace Active.pp "Resolution.iterate: active" active
      let () = Print.trace Waiting.pp "Resolution.iterate: waiting" waiting
*)
    in
      (*
      print_endline ("Resolution.iterate:active: " ^ Active.toString active);
      print_endline ("Resolution.iterate:waiting: " ^ Waiting.toString waiting);
      *)
      match Waiting.remove waiting with
        None ->
          let sat = Satisfiable (List.map Clause.thm (Active.saturation active))
        in
          Decided sat
      | Some ((d,cl),waiting) ->
        if Clause.isContradiction cl then
          Decided (Contradiction (Clause.thm cl))
        else
(*MetisTrace1
            let () = Print.trace Clause.pp "Resolution.iterate: cl" cl
*)
            (*
            let () = print_endline ("Resolution.iterate: cl " ^ (Clause.toString cl)) in
            *)
            let (active,cls) = Active.add active cl

            in let waiting = Waiting.add waiting (d,cls)

            in let res =
                Resolution
                  {parameters = parameters;
                   active = active;
                   waiting = waiting}
          in
            Undecided res
    ;;

let rec loop res =
    match iterate res with
      Decided dec -> dec
    | Undecided res -> loop res;;


end

(* ========================================================================= *)
(* The basic Metis loop.                                                     *)
(* ========================================================================= *)

module Loop =
struct

let rec loop res =
  match Resolution.iterate res with
    Resolution.Decided dec -> Some dec
  | Resolution.Undecided res -> loop res

open Ax_cj

let run rules =
  let ths = {axioms_thm = rules; conjecture_thm = []} in
  let res = Resolution.newResolution Resolution.default ths in
  match loop res with
    None -> failwith "metis: timeout"
  | Some (Resolution.Contradiction thm) -> thm
  | Some (Resolution.Satisfiable _) ->
      failwith "metis: found satisfiable assignment"

end

end


module Metis_debug = struct

(* Taken from: https://sourceforge.net/p/hol/mailman/message/35201767/ *)
let print_varandtype fmt tm =
   let hop,args = strip_comb tm in
   let s = name_of hop
   and ty = type_of hop in
   if is_var hop && args = [] then
    (pp_print_string fmt "(";
     pp_print_string fmt s;
     pp_print_string fmt ":";
     pp_print_type fmt ty;
     pp_print_string fmt ")")
   else fail() ;;

let show_types,hide_types =
   (fun () -> install_user_printer ("Show Types",print_varandtype)),
   (fun () -> try delete_user_printer "Show Types"
              with Failure _ -> failwith ("hide_types: "^
                                          "Types are already hidden."));;

end


module Preterm = struct

let mk_negp pt = Combp (preterm_of_term `~`, pt)
let mk_eqp (ps, pt) = Combp (Combp (Constp ("=", dpty), ps), pt)
let mk_conjp (ps, pt) = Combp (Combp (preterm_of_term `/\`, ps), pt)
let mk_disjp (ps, pt) = Combp (Combp (preterm_of_term `\/`, ps), pt)

let list_mk_combp (h, t) = rev_itlist (fun x acc -> Combp (acc, x)) t h

assert
  (
    list_mk_combp (Varp ("1", dpty), [Varp ("2", dpty); Varp ("3", dpty)])
  =
    Combp (Combp (Varp ("1", Ptycon ("", [])), Varp ("2", Ptycon ("", []))),
      Varp ("3", Ptycon ("", [])))
  );;

let list_mk_disjp = function
    [] -> preterm_of_term `F`
  | h::t -> itlist (curry mk_disjp) t h

(* typechecking a preterm with constants fails,
   therefore we convert constants to variables before type checking
   type checking converts the variables back to the corresponding constants
*)
let rec unconst_preterm = function
    Varp (s, pty) -> Varp (s, pty)
  | Constp (s, pty) -> Varp (s, pty)
  | Combp (l, r) -> Combp (unconst_preterm l, unconst_preterm r)
  | Typing (ptm, pty) -> Typing (unconst_preterm ptm, pty)
  | _ -> failwith "unconst_preterm"

let rec env_of_preterm = function
    Varp (s, pty) -> [(s, pty)]
  | Constp (s, pty) -> []
  | Combp (l, r) -> env_of_preterm l @ env_of_preterm r
  | Typing (ptm, pty) -> env_of_preterm ptm
  | _ -> failwith "env_of_preterm"

let env_of_th = env_of_preterm o preterm_of_term o concl
let env_of_ths = List.concat o List.map env_of_th

end


module Metis_mapping = struct

open Metis_prover

  let reset_consts,fol_of_const,hol_of_const =
    Meson.reset_consts,Meson.fol_of_const,Meson.hol_of_const

let preterm_of_const = preterm_of_term o hol_of_const o int_of_string

let prefix s = "__" ^ s

let rec preterm_of_fol_term = function
    Term.Var x -> Varp (prefix x, dpty)
  | Term.Fn (f, args) ->
      let pf = preterm_of_const f in
      let pargs = List.map preterm_of_fol_term args in
      Preterm.list_mk_combp (pf, pargs)

let preterm_of_predicate = function
    "=" -> Constp ("=", dpty)
  | p -> preterm_of_const p

let preterm_of_atom (p, args) =
  let pp = preterm_of_predicate p in
  let pargs = List.map preterm_of_fol_term args in
  Typing (Preterm.list_mk_combp (pp, pargs), pretype_of_type bool_ty)

let preterm_of_literal (pol, fat) =
  let pat = preterm_of_atom fat in
  if pol then pat else Preterm.mk_negp pat

let preterm_of_eq (s, t) =
  Preterm.mk_eqp (preterm_of_fol_term s, preterm_of_fol_term t)


let typecheck env = term_of_preterm o retypecheck env o Preterm.unconst_preterm
let typecheckl env = function
    [] -> []
  | xs -> Preterm.list_mk_disjp xs |> typecheck env |> disjuncts


let hol_of_term env = typecheck env o preterm_of_fol_term

let hol_of_atom env = typecheck env o preterm_of_atom

let hol_of_literal env = typecheck env o preterm_of_literal

let hol_of_clause env = typecheck env o Preterm.list_mk_disjp o map preterm_of_literal

let hol_of_substitution env = map dest_eq o typecheckl env o map preterm_of_eq

end


module Metis_path = struct

open Metis_prover

(* The term `f 1 2 3` is encoded in HOL Light as follows:

         @
        / \
       @  3
      / \
     @  2
    / \
   f  1

*)

let rec hol_of_term_path tm path = match tm, path with
    (tm, []) -> tm, ""
  | Term.Fn (f, args), i :: is ->
      let arity = length args in
      assert (i < arity);
      let (tm', path') = hol_of_term_path (List.nth args i) is in
      (tm', String.make (arity - i - 1) 'l' ^ "r" ^ path')
  | _ -> failwith "hol_of_term_path"

let hol_of_atom_path (p, args) = hol_of_term_path (Term.Fn (p, args))

let hol_of_literal_path (pol, atom) path =
  let s, path = hol_of_atom_path atom path in
  s, if pol then path else "r" ^ path

end


module Metis_unify = struct

open Metis_prover

let verb = ref false

exception Unify

let rec unify_fo_ho_term vars fat tm m =
  if !verb then Format.printf "unify_fo_ho_term: fat = %s, tm = %s\n%!"
    (Term.toString fat) (string_of_term tm);
  match fat with
    Term.Var v when List.mem_assoc v m ->
      if !verb then Format.printf "var_assoc\n%!";
      let tm' = List.assoc v m in
      if tm = tm' then m else raise Unify
  | Term.Var v ->
      if !verb then Format.printf "var\n%!";
      if is_var tm && not (List.mem tm vars) then (v, tm) :: m
      else (if !verb then Format.printf "Unify!\n%!"; raise Unify)
  | Term.Fn (f, args) ->
      if !verb then Format.printf "fn\n%!";
      let hf, hargs = try strip_comb tm with Failure _ -> raise Unify in
      if !verb then begin
        Format.printf "hf = %s\n%!" (string_of_term hf);
        Format.printf "is_var: %s\n%!" (if is_var hf then "true" else "false")
      end;
      assert (is_const hf || is_var hf);
      if hf = Metis_mapping.hol_of_const (int_of_string f)
      then itlist2 (unify_fo_ho_term vars) args hargs m
      else raise Unify

let unify_fo_ho_atom vars (p, args) htm m =
  if p = "="
  then try let hl, hr = dest_eq htm in itlist2 (unify_fo_ho_term vars) args [hl; hr] m
       with Failure _ -> raise Unify
  else unify_fo_ho_term vars (Term.Fn (p, args)) htm m

let unify_fo_ho_literal vars (pol, atom) htm m =
  let htm' = if pol then htm else try dest_neg htm with Failure _ -> raise Unify in
  unify_fo_ho_atom vars atom htm' m

end


module Metis_rules = struct

(* move a literal in the proof of a disjunction to the first position
   may not preserve the order of the other literals *)
let FRONT lit thm =
  let conc = concl thm in
  let disj = disjuncts (concl thm) in
  let rest = match partition (fun l -> l = lit) disj with
      ([], _) -> failwith "FRONT: literal not in disjunction"
    | (_ , r) -> r in
  let disj' = lit :: rest in
  let conc' = list_mk_disj disj' in
  let eq = DISJ_ACI_RULE (mk_eq (conc, conc')) in
  (PURE_ONCE_REWRITE_RULE [eq] thm, rest)

(* resolve two clauses, where atom has to appear at the first position of
   both clauses: positive in the first and negative in the second clause *)
let RESOLVE_N =
  let RESOLVE_1  = TAUT `!a. a ==> ~a ==> F`
  and RESOLVE_2L = TAUT `!a b. a \/ b ==> ~a ==> b`
  and RESOLVE_2R = TAUT `!a c. a ==> ~a \/ c ==> c`
  and RESOLVE_3  = TAUT `!a b c. a \/ b ==> ~a \/ c ==> b \/ c` in
  fun atom -> function
  ([], []) -> SPEC atom RESOLVE_1
| (r1, []) -> SPECL [atom; list_mk_disj r1] RESOLVE_2L
| ([], r2) -> SPECL [atom; list_mk_disj r2] RESOLVE_2R
| (r1, r2) -> SPECL [atom; list_mk_disj r1; list_mk_disj r2] RESOLVE_3

(* resolve two clauses th1 and th2, where atom appears somewhere
   positive in th1 and negative in th2 *)
let RESOLVE atom th1 th2 =
  (*print_endline ("Atom: " ^ string_of_term atom);
  print_endline ("th1 : " ^ string_of_term (concl th1));
  print_endline ("th2 : " ^ string_of_term (concl th2));*)
  try let (th1', r1) = FRONT atom th1
  and (th2', r2) = FRONT (mk_neg atom) th2 in
  let res = RESOLVE_N atom (r1, r2) in
  MP (MP res th1') th2'
  with Failure _ -> failwith "resolve"

(* given A,  tm |- C, prove A |- ~tm \/ C or
   given A, ~tm |- C, prove A |-  tm \/ C *)
let DISCH_DISJ =
  let IMPL_NOT_L = TAUT `!a b. ~a ==> b <=>  a \/ b`
  and IMPL_NOT_R = TAUT `!a b.  a ==> b <=> ~a \/ b` in
  fun tm th ->
    let impl = DISCH tm th
    and (tm', IMPL_NOT) =
      try dest_neg tm, IMPL_NOT_L
      with Failure _ ->    tm, IMPL_NOT_R in
    let eq = SPECL [tm'; concl th] IMPL_NOT in
    PURE_ONCE_REWRITE_RULE [eq] impl

(* given A, tm1, .., tmn |- th, prove A |- ~tm1 \/ .. \/ ~tmn \/ th *)
let DISCH_DISJS tms th = List.fold_right DISCH_DISJ tms th

end


module Metis_reconstruct2 = struct

open Metis_prover

let term_eq_mod_type t1 t2 tyinsts =
  try
    let _,tminsts,tyinsts = term_type_unify t1 t2 ([], [], tyinsts) in
    if !metisverb then
    begin
      Format.printf "unified with |tminsts| = %d!\n%!" (List.length tminsts);
      List.iter (fun t1, t2 -> Format.printf "%s <- %s\n%!" (string_of_term t1) (string_of_term t2)) tminsts
    end;
    if tminsts = [] then Some tyinsts else None
  with Failure _ -> None

let rec match_elems f m = function
    ([], []) -> [m]
  | ([],  _) -> []
  | (x :: xs, ys) -> List.map (fun y -> match f x y m with
        Some m' -> match_elems f m' (xs, List.filter ((!=) y) ys)
      | None -> []) ys |> List.concat

let match_fo_ho_clause vars = match_elems
  (fun ft ht m -> try Some (Metis_unify.unify_fo_ho_literal vars ft ht m) with Metis_unify.Unify -> None)
  []


let string_of_tminst = String.concat ", " o
  map (fun (tm, v) -> string_of_term tm ^ " <- " ^ string_of_term v)

let string_of_tyinst = String.concat ", " o
  map (fun (ty, v) -> string_of_type ty ^ " <- " ^ string_of_type v)

let string_of_instantiation (it, tminst, tyinst) =
  "([" ^ string_of_tminst tminst ^ "], [" ^ string_of_tyinst tyinst ^ "])"

let reorient_tysubst vars sub =
  let sub' = map (fun (ty, v) ->
    if List.mem v vars && is_vartype ty then v, ty else ty, v) sub in
  map (fun (ty, v) -> tysubst sub' ty, v) sub'

let rec hol_of_thm axioms fth =
  if !metisverb then Format.printf "hol_of_thm: %s\n%!" (Thm.toString fth);
  let env = Preterm.env_of_ths axioms in
  let hth = match Proof.thmToInference fth with
    Proof.Axiom clause ->
      let clausel = Literal.Set.toList clause in
      let maxs = Utils.List.concat_map (fun ax ->
        (*if !metisverb then Format.printf "ax: %s\n%!" (string_of_thm ax);*)
        let disjs = concl ax |> striplist dest_disj in
        (*if !metisverb then Format.printf "before matching\n%!";*)
        let tmvars = freesl (hyp ax) in
        let ms = match_fo_ho_clause tmvars (clausel, disjs) in
        (*if !metisverb then Format.printf "after matching\n%!";*)
        map (fun m -> m, ax) ms) axioms in
      assert (List.length maxs > 0);
      let tminst = List.map (fun v, tm -> mk_var (Metis_mapping.prefix v, type_of tm), tm) in
      if !metisverb then Format.printf "length maxs = %d\n%!" (List.length maxs);
      if !metisverb then List.iter (fun (m, ax) -> Format.printf "max: %s with m = %s\n%!" (string_of_thm ax) (string_of_tminst (tminst m))) maxs;
      let (m, ax) = List.hd maxs in
      INST (tminst m) ax
  (* Caution: the substitution can contain elements such as "x -> f(x)" *)
  | Proof.Subst (fsub, fth1) ->
      let th1 = hol_of_thm axioms fth1 in
      if !metisverb then Format.printf "subst with th1 = %s\n%!" (string_of_thm th1);

      let fsubl = Substitute.toList fsub in
      if !metisverb then Format.printf "before substitution lifting\n%!";
      let hsub = map (fun (v, t) -> t, Term.Var v) fsubl |>
        Metis_mapping.hol_of_substitution env in
      if !metisverb then Format.printf "subst: %s\n%!" (string_of_tminst hsub);
      let tyinst = itlist (fun (t, v) m ->
        let v' = find (fun v' -> name_of v' = name_of v) (frees (concl th1)) in
        type_unify (type_of v) (type_of v') m) hsub [] in
      let tminst = map (fun (t, v) -> inst tyinst t, inst tyinst v) hsub in

      if !metisverb then
        Format.printf "before instantiate of th1 = %s with %s\n%!"
          (string_of_thm th1) (string_of_instantiation ([], tminst, tyinst));

      INSTANTIATE ([], tminst, tyinst) th1
  | Proof.Resolve (atom, fth1, fth2) ->
      let th1 = hol_of_thm axioms fth1
      and th2 = hol_of_thm axioms fth2 in
      let env = Preterm.env_of_ths [th1; th2] @ env in
      if !metisverb then List.iter (fun (s, pty) -> Format.printf "%s <- %s\n%!" s (string_of_type (type_of_pretype pty))) env;
      if !metisverb then Format.printf "before resolving\n%!";
      if !metisverb then Format.printf "th1 = %s\n%!" (string_of_thm th1);
      if !metisverb then Format.printf "th2 = %s\n%!" (string_of_thm th2);
      let tm1 = striplist dest_disj (concl th1) |> List.filter (not o is_neg)
      and tm2 = striplist dest_disj (concl th2) |> List.filter is_neg |> List.map dest_neg in
      if !metisverb then List.iter (Format.printf "tm1: %s\n%!" o string_of_term) tm1;
      if !metisverb then List.iter (Format.printf "tm2: %s\n%!" o string_of_term) tm2;
      let hatom = Metis_mapping.hol_of_atom env atom in
      if !metisverb then Format.printf "hatom: %s\n%!" (string_of_term hatom);
      let cands = Utils.List.concat_map (fun x ->
        match term_eq_mod_type hatom x [] with
          None -> []
        | Some m -> Utils.List.filter_map (fun y -> term_eq_mod_type hatom y m) tm2) tm1 in
      if !metisverb then Format.printf "%d candidates available\n%!" (List.length cands);
      assert (List.length cands > 0);
      assert (let h = List.hd cands in List.for_all ((=) h) cands);
      let tyinsts = List.hd cands in
      let tyvars = map hyp axioms |> List.concat |>
        map type_vars_in_term |> List.concat in
      if !metisverb then Format.printf "Reorienting type substitution ...\n%!";
      let tyinsts = reorient_tysubst tyvars tyinsts in

      if !metisverb then Format.printf "Resolving ...\n%!";

      Metis_rules.RESOLVE (inst tyinsts hatom)
        (INST_TYPE tyinsts th1) (INST_TYPE tyinsts th2)
  | Proof.Refl term -> REFL (Metis_mapping.hol_of_term env term)
  | Proof.Assume atom -> SPEC (Metis_mapping.hol_of_atom env atom) EXCLUDED_MIDDLE
  | Proof.Equality (flit, fpath, ft) ->
      let hlit = Metis_mapping.hol_of_literal env flit in
      let fs, hpath = Metis_path.hol_of_literal_path flit fpath in
      let hs = follow_path hpath hlit in
      let ht = Metis_mapping.hol_of_term env ft in
      let m = type_unify (type_of ht) (type_of hs) [] in
      let hlit, hs, ht = inst m hlit, inst m hs, inst m ht in

      if !metisverb then begin
        Format.printf "Trying to replace %s : %s with %s : %s\n%!"
          (string_of_term hs) (string_of_type (type_of hs))
          (string_of_term ht) (string_of_type (type_of ht));
        Format.printf "In %s\n%!" (string_of_term hlit)
      end;

      let heq = mk_eq (hs, ht) in
      let conv = PATH_CONV hpath (PURE_ONCE_REWRITE_CONV [ASSUME heq]) in
      let hlit' = CONV_RULE conv (ASSUME hlit) in
      if !metisverb then Format.printf "hlit = %s, hlit' = %s\n%!"
        (string_of_term hlit) (string_of_thm hlit');

      if hs <> ht then assert (concl hlit' <> hlit);
      (try Metis_rules.DISCH_DISJS [heq; hlit] hlit'
      with Failure _ -> failwith "equality")
  in
    (* eliminate duplicates in clause *)
    let hth = CONV_RULE DISJ_CANON_CONV hth in
    if !metisverb then begin
      Format.printf "hol_of_thm finished\n%!";
      let hth' = Thm.clause fth |> Literal.Set.toList |> Metis_mapping.hol_of_clause env in
      Format.printf "hol_of_thm returned:\n%s\n for\n%s\n%!"
        (string_of_term (concl hth)) (string_of_term hth')
    end;
    hth

end

(* ========================================================================= *)
(* Conversion of HOL to Metis FOL.                                           *)
(* ========================================================================= *)

module Metis_generate = struct

open Metis_prover

let metis_name = string_of_int

let rec metis_of_term env consts tm =
  if is_var tm && not (List.mem tm consts) then
    (Term.Var(metis_name (Meson.fol_of_var tm)))
  else (
    let f,args = strip_comb tm in
    if List.mem f env then failwith "metis_of_term: higher order" else
    let ff = Meson.fol_of_const f in
    Term.Fn (metis_name ff, map (metis_of_term env consts) args))

let metis_of_atom env consts tm =
  try let (l, r) = dest_eq tm in
      let l' = metis_of_term env consts l
      and r' = metis_of_term env consts r in
      Atom.mkEq (l', r')
  with Failure _ ->
      let f,args = strip_comb tm in
      if List.mem f env then failwith "metis_of_atom: higher order" else
      let ff = Meson.fol_of_const f in
      (metis_name ff, map (metis_of_term env consts) args)

let metis_of_literal env consts tm =
  let (pol, tm') = try (false, dest_neg tm)
     with Failure _ -> (true,           tm)
  in (pol, metis_of_atom env consts tm')

let metis_of_clause th =
  let lconsts = freesl (hyp th) in
  let tm = concl th in
  let hlits = disjuncts tm in
  let flits = map (metis_of_literal [] lconsts) hlits in
  let set = Literal.Set.fromList flits in
  Thm.axiom set

let metis_of_clauses = map metis_of_clause

end


(* ========================================================================= *)
(* Main Metis module.                                                        *)
(* ========================================================================= *)

module Metis = struct

open Metis_prover

(* ------------------------------------------------------------------------- *)
(* Some parameters controlling Metis behaviour.                              *)
(* ------------------------------------------------------------------------- *)

let split_limit = ref 0;; (* Limit of case splits before Metis proper  *)

(* ----------------------------------------------------------------------- *)
(* Basic HOL Metis procedure.                                              *)
(* ----------------------------------------------------------------------- *)

(* Debugging tactic. *)
let PRINT_TAC g = print_goal g; ALL_TAC g
let PRINT_ID_TAC s g = print_endline s; PRINT_TAC g

(* Slightly modified tactic from meson.ml. *)
let FOL_PREPARE_TAC ths =
  (* We start with a single goal: P. *)

  REFUTE_THEN ASSUME_TAC THEN
  (*PRINT_ID_TAC "refuted" THEN*)
  (*   0 [`~P`]

     `F`
   *)

  Meson.POLY_ASSUME_TAC (map GEN_ALL ths) THEN
  (*PRINT_ID_TAC "poly_assumed" THEN*)
  (*   0 [`~P`]
       1 [th1]
       ...
       n [thn]

     `F`
  *)

  W(MAP_EVERY(UNDISCH_TAC o concl o snd) o fst) THEN
  (* `~P ==> th1 ==> ... ==> thn ==> F` *)

  SELECT_ELIM_TAC THEN
  (* eliminate "select terms", e.g. Hilbert operators *)

  W(fun (asl,w) -> MAP_EVERY (fun v -> SPEC_TAC(v,v)) (frees w)) THEN
  (*PRINT_ID_TAC "all-quantified" THEN*)
  (* MAP_EVERY is mapM for tactics
     I believe that this all-quantifies all free variables in the goal *)

  CONV_TAC(PRESIMP_CONV THENC
           TOP_DEPTH_CONV BETA_CONV THENC
           LAMBDA_ELIM_CONV THENC
           CONDS_CELIM_CONV THENC
           Meson.QUANT_BOOL_CONV) THEN
  (*PRINT_ID_TAC "converted" THEN*)

  REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  (* remove outermost all-quantifiers (GEN_TAC) and implications (DISCH_TAC),
     moving them into assumptions *)

  REFUTE_THEN ASSUME_TAC THEN
  (* move conclusion negated into assumptions, replace goal by `F`*)

  RULE_ASSUM_TAC(CONV_RULE(NNF_CONV THENC SKOLEM_CONV)) THEN
  (* transform assumptions to NNF and skolemize *)

  REPEAT (FIRST_X_ASSUM CHOOSE_TAC) THEN
  (* remove existentials at the front *)

  ASM_FOL_TAC THEN
  (* fix function arities, e.g. f(x) and f(x,y) become I f x and I (I f x) y *)

  Meson.SPLIT_TAC (!split_limit) THEN
  RULE_ASSUM_TAC(CONV_RULE(PRENEX_CONV THENC WEAK_CNF_CONV)) THEN

  RULE_ASSUM_TAC(repeat
   (fun th -> SPEC(genvar(type_of(fst(dest_forall(concl th))))) th)) THEN
  (* destroy all-quantifiers and replace quantified variables by fresh ones *)

  REPEAT (FIRST_X_ASSUM (Meson.CONJUNCTS_THEN' ASSUME_TAC)) THEN
  (* make every conjunction a separate assumption *)

  RULE_ASSUM_TAC(CONV_RULE(ASSOC_CONV DISJ_ASSOC))
  (* associate disjunctions to the right *)

  (*THEN PRINT_ID_TAC "before Metis"*)


let without_warnings f =
  let tiv = !type_invention_warning in
  let reset () = type_invention_warning := tiv in
  type_invention_warning := false;
  try let y = f () in reset (); y
  with e -> (reset(); raise e)


let SIMPLE_METIS_REFUTE ths =
  Meson.clear_contrapos_cache();
  (* TODO: Metis currently uses randomness to search for proof --
     we should make that deterministic for proof reconstruction! *)
  Random.init 0;
  let rules = Metis_generate.metis_of_clauses ths in
  if !metisverb then
  begin
    Format.printf "Original ths:\n%!";
    List.iter (Format.printf "%s\n%!" o string_of_thm) ths
  end;
  let res = Loop.run rules in
  if !metisverb then Thm.print_proof res;
  let ths = map (CONV_RULE DISJ_CANON_CONV) ths in
  let proof = without_warnings (fun () -> Metis_reconstruct2.hol_of_thm ths res) in
  if !metisverb then
  begin
    Format.printf "ths:\n%!";
    List.iter (fun t -> print_thm t; Format.printf "\n%!") ths;
    Format.printf "Metis theorem:\n%!";
    print_thm proof;
    Format.printf "Metis end.\n%!";
  end;
  let allhyps = List.concat (List.map hyp ths) in
  assert (forall (fun h -> List.mem h allhyps) (hyp proof));
  assert (concl proof = `F`);
  proof

let PURE_METIS_TAC g =
  Meson.reset_vars(); Meson.reset_consts();
  (FIRST_ASSUM CONTR_TAC ORELSE
   W(ACCEPT_TAC o SIMPLE_METIS_REFUTE o map snd o fst)) g

let GEN_METIS_TAC ths =
  FOL_PREPARE_TAC ths THEN PURE_METIS_TAC

end
;;

(* ========================================================================= *)
(* Basic Metis refutation procedure and parametrized tactic.                 *)
(* ========================================================================= *)

let ASM_METIS_TAC = Metis.GEN_METIS_TAC;;

let METIS_TAC ths = POP_ASSUM_LIST(K ALL_TAC) THEN ASM_METIS_TAC ths;;

let METIS ths tm = prove(tm,METIS_TAC ths);;
