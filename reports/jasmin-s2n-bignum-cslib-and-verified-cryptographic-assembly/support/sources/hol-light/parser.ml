(* ========================================================================= *)
(* Lexical analyzer, type and preterm parsers.                               *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*     (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018              *)
(* ========================================================================= *)

needs "preterm.ml";;

(* ------------------------------------------------------------------------- *)
(* Need to have this now for set enums, since "," isn't a reserved word.     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix (",",(14,"right"));;

(* ------------------------------------------------------------------------- *)
(* Basic parser combinators.                                                 *)
(* ------------------------------------------------------------------------- *)

exception Noparse;;

let (|||) parser1 parser2 input =
  try parser1 input
  with Noparse -> parser2 input;;

let (++) parser1 parser2 input =
  let result1,rest1 = parser1 input in
  let result2,rest2 = parser2 rest1 in
  (result1,result2),rest2;;

let rec many prs input =
  try let result,next = prs input in
      let results,rest = many prs next in
      (result::results),rest
  with Noparse -> [],input;;

let (>>) prs treatment input =
  let result,rest = prs input in
  treatment(result),rest;;

let fix err prs input =
  try prs input
  with Noparse -> failwith (err ^ " expected");;

let rec listof prs sep err =
  prs ++ many (sep ++ fix err prs >> snd) >> (fun (h,t) -> h::t);;

let nothing input = [],input;;

let elistof prs sep err =
  listof prs sep err ||| nothing;;

let leftbin prs sep cons err =
  prs ++ many (sep ++ fix err prs) >>
  (fun (x,opxs) -> let ops,xs = unzip opxs in
                   itlist2 (fun op y x -> cons op x y) (rev ops) (rev xs) x);;

let rightbin prs sep cons err =
  prs ++ many (sep ++ fix err prs) >>
  (fun (x,opxs) -> if opxs = [] then x else
                   let ops,xs = unzip opxs in
                   itlist2 cons ops (x::butlast xs) (last xs));;

let possibly prs input =
  try let x,rest = prs input in [x],rest
  with Noparse -> [],input;;

let some p =
  function
      [] -> raise Noparse
    | (h::t) -> if p h then (h,t) else raise Noparse;;

let a tok = some (fun item -> item = tok);;

let rec atleast n prs i =
  (if n <= 0 then many prs
   else prs ++ atleast (n - 1) prs >> (fun (h,t) -> h::t)) i;;

let finished input =
  if input = [] then 0,input else failwith "Unparsed input";;

(* ------------------------------------------------------------------------- *)
(* The basic lexical classes: identifiers, strings and reserved words.       *)
(* ------------------------------------------------------------------------- *)

type lexcode = Ident of string
             | Resword of string;;

(* ------------------------------------------------------------------------- *)
(* Lexical analyzer. Apart from some special bracket symbols, each           *)
(* identifier is made up of the longest string of alphanumerics or           *)
(* the longest string of symbolics.                                          *)
(* ------------------------------------------------------------------------- *)

reserve_words ["//"];;

let comment_token = ref (Resword "//");;

let lex =
  let collect (h,t) = end_itlist (^) (h::t) in
  let reserve =
    function
        (Ident n as tok) ->
            if is_reserved_word n then Resword(n) else tok
      | t -> t in
  let stringof p = atleast 1 p >> end_itlist (^) in
  let simple_ident = stringof(some isalnum) ||| stringof(some issymb) in
  let undertail = stringof (a "_") ++ possibly simple_ident >> collect in
  let ident = (undertail ||| simple_ident) ++ many undertail >> collect in
  let septok = stringof(some issep) in
  let escapecode i =
    match i with
      "\\"::rst -> "\\",rst
    | "\""::rst -> "\"",rst
    | "\'"::rst -> "\'",rst
    | "n"::rst -> "\n",rst
    | "r"::rst -> "\r",rst
    | "t"::rst -> "\t",rst
    | "b"::rst -> "\b",rst
    | " "::rst -> " ",rst
    | "x"::h::l::rst ->
         String.make 1 (Char.chr(int_of_string("0x"^h^l))),rst
    | a::b::c::rst when forall isnum [a;b;c] ->
         String.make 1 (Char.chr(int_of_string(a^b^c))),rst
    | _ -> failwith "lex:unrecognized OCaml-style escape in string" in
  let stringchar =
      some (fun i -> i <> "\\" && i <> "\"")
  ||| (a "\\" ++ escapecode >> snd) in
  let string = a "\"" ++ many stringchar ++ a "\"" >>
        (fun ((_,s),_) -> "\""^implode s^"\"") in
  let rawtoken = (string ||| some isbra ||| septok ||| ident) >>
    (fun x -> Ident x) in
  let simptoken = many (some isspace) ++ rawtoken >> (reserve o snd) in
  let rec tokens i =
    try let (t,rst) = simptoken i in
        if t = !comment_token then
          (many (fun i -> if i <> [] && hd i <> "\n" then 1,tl i
                          else raise Noparse) ++ tokens >> snd) rst
        else
          let toks,rst1 = tokens rst in t::toks,rst1
    with Noparse -> [],i in
  fst o (tokens ++ many (some isspace) ++ finished >> (fst o fst));;

(* ------------------------------------------------------------------------- *)
(* Parser for pretypes. Concrete syntax:                                     *)
(*                                                                           *)
(* TYPE        :: SUMTYPE -> TYPE                                            *)
(*              | SUMTYPE                                                    *)
(*                                                                           *)
(* SUMTYPE     :: PRODTYPE + SUMTYPE                                         *)
(*              | PRODTYPE                                                   *)
(*                                                                           *)
(* PRODTYPE    :: POWTYPE # PRODTYPE                                         *)
(*              | POWTYPE                                                    *)
(*                                                                           *)
(* POWTYPE     :: APPTYPE ^ POWTYPE                                          *)
(*              | APPTYPE                                                    *)
(*                                                                           *)
(* APPTYPE     :: ATOMICTYPES type-constructor  [Provided arity matches]     *)
(*              | ATOMICTYPES                   [Provided only 1 ATOMICTYPE] *)
(*                                                                           *)
(* ATOMICTYPES :: type-constructor              [Provided arity zero]        *)
(*              | type-variable                                              *)
(*              | ( TYPE )                                                   *)
(*              | ( TYPE LIST )                                              *)
(*                                                                           *)
(* TYPELIST    :: TYPE , TYPELIST                                            *)
(*              | TYPE                                                       *)
(*                                                                           *)
(* Two features make this different from previous HOL type syntax:           *)
(*                                                                           *)
(*  o Any identifier not in use as a type constant will be parsed as a       *)
(*    type variable; a ' is not needed and a * is not allowed.               *)
(*                                                                           *)
(*  o Antiquotation is not supported.                                        *)
(* ------------------------------------------------------------------------- *)

let parse_pretype =
  let mk_prefinty:num->pretype =
    let rec prefinty n =
      if n =/ num_1 then Ptycon("1",[]) else
      let c = if Num.mod_num n num_2 =/ num_0 then "tybit0" else "tybit1" in
      Ptycon(c,[prefinty(Num.quo_num n num_2)]) in
    fun n ->
      if not(is_integer_num n) || n </ num_1 then failwith "mk_prefinty" else
      prefinty n in
  let btyop n n' x y = Ptycon(n,[x;y])
  and mk_apptype =
    function
        ([s],[]) -> s
      | (tys,[c]) -> Ptycon(c,tys)
      | _ -> failwith "Bad type construction"
  and type_atom input =
    match input with
      (Ident s)::rest ->
          (try pretype_of_type(assoc s (type_abbrevs())) with Failure _ ->
           try mk_prefinty (num_of_string s) with Failure _ ->
           if try get_type_arity s = 0 with Failure _ -> false
           then Ptycon(s,[]) else Utv(s)),rest
    | _ -> raise Noparse
  and type_constructor input =
    match input with
      (Ident s)::rest -> if try get_type_arity s > 0 with Failure _ -> false
                         then s,rest else raise Noparse
    | _ -> raise Noparse in
  let rec pretype i =
    rightbin sumtype (a (Resword "->")) (btyop "fun") "proper use of type operator (->)" i
  and sumtype i = rightbin prodtype (a (Ident "+")) (btyop "sum") "proper use of type operator (+)" i
  and prodtype i = rightbin carttype (a (Ident "#")) (btyop "prod") "proper use of type operator (#)" i
  and carttype i = leftbin apptype (a (Ident "^")) (btyop "cart") "proper use of type operator (^)" i
  and apptype i = (atomictypes ++ (type_constructor >> (fun x -> [x])
                                ||| nothing) >> mk_apptype) i
  and atomictypes i =
        (((a (Resword "(")) ++ typelist ++ a (Resword ")") >> (snd o fst))
      ||| (type_atom >> (fun x -> [x]))) i
  and typelist i = listof pretype (a (Ident ",")) "comma separated list for type constructor" i in
  pretype;;

(* ------------------------------------------------------------------------- *)
(* Hook to allow installation of user parsers.                               *)
(* ------------------------------------------------------------------------- *)

let install_parser,delete_parser,installed_parsers,try_user_parser =
  let rec try_parsers ps i =
    if ps = [] then raise Noparse else
    try snd(hd ps) i with Noparse -> try_parsers (tl ps) i in
  let parser_list =
    ref([]:(string*(lexcode list -> preterm * lexcode list))list) in
  (fun dat -> parser_list := dat::(!parser_list)),
  (fun key -> try parser_list := snd (remove (fun (key',_) -> key = key')
                                                 (!parser_list))
                  with Failure _ -> ()),
  (fun () -> !parser_list),
  (fun i -> try_parsers (!parser_list) i);;

(* ------------------------------------------------------------------------- *)
(* Initial preterm parsing. This uses binder and precedence/associativity/   *)
(* prefix status to guide parsing and preterm construction, but treats all   *)
(* identifiers as variables.                                                 *)
(*                                                                           *)
(* PRETERM            :: APPL_PRETERM binop APPL_PRETERM                     *)
(*                     | APPL_PRETERM                                        *)
(*                                                                           *)
(* APPL_PRETERM       :: APPL_PRETERM : type                                 *)
(*                     | APPL_PRETERM BINDER_PRETERM                         *)
(*                     | BINDER_PRETERM                                      *)
(*                                                                           *)
(* BINDER_PRETERM     :: binder VARSTRUCT_PRETERMS . PRETERM                 *)
(*                     | let PRETERM and ... and PRETERM in PRETERM          *)
(*                     | ATOMIC_PRETERM                                      *)
(*                                                                           *)
(* VARSTRUCT_PRETERMS :: TYPED_PRETERM VARSTRUCT_PRETERMS                    *)
(*                     | TYPED_PRETERM                                       *)
(*                                                                           *)
(* TYPED_PRETERM      :: TYPED_PRETERM : type                                *)
(*                     | ATOMIC_PRETERM                                      *)
(*                                                                           *)
(* ATOMIC_PRETERM     :: ( PRETERM )                                         *)
(*                     | if PRETERM then PRETERM else PRETERM                *)
(*                     | [ PRETERM; .. ; PRETERM ]                           *)
(*                     | { PRETERM, .. , PRETERM }                           *)
(*                     | { PRETERM | PRETERM }                               *)
(*                     | identifier                                          *)
(*                                                                           *)
(* Note that arbitrary preterms are allowed as varstructs. This allows       *)
(* more general forms of matching and considerably regularizes the syntax.   *)
(* ------------------------------------------------------------------------- *)

let parse_preterm =
  let rec pairwise r l =
    match l with
      [] -> true
    | h::t -> forall (r h) t && pairwise r t in
  let rec pfrees ptm =
    match ptm with
      Varp(v,pty) ->
        if v = "" && pty = dpty then []
        else if can get_const_type v || can num_of_string v
                || exists (fun (w,_) -> v = w) (!the_interface) then []
        else [ptm]
    | Constp(_,_) -> []
    | Combp(p1,p2) -> union (pfrees p1) (pfrees p2)
    | Absp(p1,p2) -> subtract (pfrees p2) (pfrees p1)
    | Typing(p,_) -> pfrees p in
  let pdest_eq (Combp(Combp(Varp(("="|"<=>"),_),l),r)) = l,r in
  let pmk_let (letbindings,body) =
    let vars,tms = unzip (map pdest_eq letbindings) in
    let _ = warn(not
     (pairwise (fun s t -> intersect(pfrees s) (pfrees t) = []) vars))
     "duplicate names on left of let-binding: latest is used" in
    let lend = Combp(Varp("LET_END",dpty),body) in
    let abs = itlist (fun v t -> Absp(v,t)) vars lend in
    let labs = Combp(Varp("LET",dpty),abs) in
    rev_itlist (fun x f -> Combp(f,x)) tms labs in
  let pmk_vbinder(n,v,bod) =
    if n = "\\" then Absp(v,bod)
    else Combp(Varp(n,dpty),Absp(v,bod)) in
  let pmk_binder(n,vs,bod) =
    itlist (fun v b -> pmk_vbinder(n,v,b)) vs bod in
  let pmk_set_enum ptms =
    itlist (fun x t -> Combp(Combp(Varp("INSERT",dpty),x),t)) ptms
           (Varp("EMPTY",dpty)) in
  let pgenvar =
    let gcounter = ref 0 in
    fun () -> let count = !gcounter in
              (gcounter := count + 1;
               Varp("GEN%PVAR%"^(string_of_int count),dpty)) in
  let pmk_exists(v,ptm) = Combp(Varp("?",dpty),Absp(v,ptm)) in
  let pmk_list els =
    itlist (fun x y -> Combp(Combp(Varp("CONS",dpty),x),y))
           els (Varp("NIL",dpty)) in
  let pmk_bool =
    let tt = Varp("T",dpty) and ff = Varp("F",dpty) in
    fun b -> if b then tt else ff in
  let pmk_char c =
    let lis = map (fun i -> pmk_bool((c / (1 lsl i)) mod 2 = 1)) (0--7) in
    itlist (fun x y -> Combp(y,x)) lis (Varp("ASCII",dpty)) in
  let pmk_string s =
    let ns = map (fun i -> Char.code(String.get s i))
                 (0--(String.length s - 1)) in
    pmk_list(map pmk_char ns) in
  let pmk_setcompr (fabs,bvs,babs) =
    let v = pgenvar() in
    let bod = itlist (curry pmk_exists) bvs
                     (Combp(Combp(Combp(Varp("SETSPEC",dpty),v),babs),fabs)) in
    Combp(Varp("GSPEC",dpty),Absp(v,bod)) in
  let pmk_setabs (fabs,babs) =
    let evs =
      let fvs = pfrees fabs
      and bvs = pfrees babs in
      if length fvs <= 1 || bvs = [] then fvs
      else intersect fvs bvs in
    pmk_setcompr (fabs,evs,babs) in
  let rec mk_precedence infxs prs inp =
    match infxs with
      (s,(p,at))::_ ->
          let topins,rest = partition (fun (s',pat') -> pat' = (p,at)) infxs in
          (if at = "right" then rightbin else leftbin)
          (mk_precedence rest prs)
          (end_itlist (|||) (map (fun (s,_) -> a (Ident s)) topins))
          (fun (Ident op) x y -> Combp(Combp(Varp(op,dpty),x),y))
          ("term after binary operator")
          inp
    | _ -> prs inp in
  let pmk_geq s t = Combp(Combp(Varp("GEQ",dpty),s),t) in
  let pmk_pattern ((pat,guards),res) =
    let x = pgenvar() and y = pgenvar() in
    let vs = pfrees pat
    and bod =
     if guards = [] then
       Combp(Combp(Varp("_UNGUARDED_PATTERN",dpty),pmk_geq pat x),
             pmk_geq res y)
     else
       Combp(Combp(Combp(Varp("_GUARDED_PATTERN",dpty),pmk_geq pat x),
                   hd guards),
             pmk_geq res y) in
    Absp(x,Absp(y,itlist (curry pmk_exists) vs bod)) in
  let pretype = parse_pretype
  and string inp =
    match inp with
      Ident s::rst when String.length s >= 2 &&
                        String.sub s 0 1 = "\"" &&
                        String.sub s (String.length s - 1) 1 = "\""
       -> String.sub s 1 (String.length s - 2),rst
    | _ -> raise Noparse
  and singleton1 x = [x]
  and lmk_ite (((((_,b),_),l),_),r) =
          Combp(Combp(Combp(Varp("COND",dpty),b),l),r)
  and lmk_typed =
    function (p,[]) -> p | (p,[ty]) -> Typing(p,ty) | _ -> fail()
  and lmk_let (((_,bnds),_),ptm) = pmk_let (bnds,ptm)
  and lmk_binder ((((s,h),t),_),p) = pmk_binder(s,h::t,p)
  and lmk_setenum(l,_) = pmk_set_enum l
  and lmk_setabs(((l,_),r),_) = pmk_setabs(l,r)
  and lmk_setcompr(((((f,_),vs),_),b),_) =
     pmk_setcompr(f,pfrees vs,b)
  and lmk_decimal ((_,l0),ropt) =
    let l,r = if ropt = [] then l0,"1" else
              let r0 = hd ropt in
              let n_l = num_of_string l0
              and n_r = num_of_string r0 in
              let n_d = power_num (num 10) (num (String.length r0)) in
              let n_n = n_l */ n_d +/ n_r in
              string_of_num n_n,string_of_num n_d in
     Combp(Combp(Varp("DECIMAL",dpty),Varp(l,dpty)),Varp(r,dpty))
  and lmk_univ((_,pty),_) =
    Typing(Varp("UNIV",dpty),Ptycon("fun",[pty;Ptycon("bool",[])]))
  and any_identifier =
    function
        ((Ident s):: rest) -> s,rest
      | _ -> raise Noparse
  and identifier =
    function
       ((Ident s):: rest) ->
        if can get_infix_status s || is_prefix s || parses_as_binder s
        then raise Noparse else s,rest
      | _ -> raise Noparse
  and binder =
    function
        ((Ident s):: rest) ->
        if parses_as_binder s then s,rest else raise Noparse
      | _ -> raise Noparse
  and pre_fix =
    function
        ((Ident s):: rest) ->
        if is_prefix s then s,rest else raise Noparse
      | _ -> raise Noparse in
  let rec preterm i =
    mk_precedence (infixes()) typed_appl_preterm i
  and nocommapreterm i =
    let infs = filter (fun (s,_) -> s <> ",") (infixes()) in
    mk_precedence infs typed_appl_preterm i
  and typed_appl_preterm i =
    (appl_preterm ++
     possibly (a (Resword ":") ++ pretype >> snd)
    >> lmk_typed) i
  and appl_preterm i =
    (pre_fix ++ appl_preterm
    >> (fun (x,y) -> Combp(Varp(x,dpty),y))
  ||| (binder_preterm ++ many binder_preterm >>
        (fun (h,t) -> itlist (fun x y -> Combp(y,x)) (rev t) h))) i
  and binder_preterm i =
   ((a (Resword "let") ++
     leftbin (preterm >> singleton1) (a (Resword "and")) (K (@)) "binding" ++
     a (Resword "in") ++
     preterm
    >> lmk_let)
  ||| (binder ++
       typed_apreterm ++
       many typed_apreterm ++
       a (Resword ".") ++
       preterm
       >> lmk_binder)
  ||| atomic_preterm) i
  and typed_apreterm i =
    (atomic_preterm ++
     possibly (a (Resword ":") ++ pretype >> snd)
    >> lmk_typed) i
  and atomic_preterm i =
    (try_user_parser
  ||| ((a (Resword "(") ++ a (Resword ":")) ++ pretype ++ a (Resword ")")
       >> lmk_univ)
  ||| ((a (Resword "(") ++ a (Resword ":")) ++ pretype
       >> (fun _ -> failwith "closing right parenthesis on universe expected"))
  ||| ((a (Resword "(") ++ a (Resword ":"))
       >> (fun _ -> failwith "type in universe construction expected"))
  ||| (string >> pmk_string)
  ||| (a (Resword "(") ++
       (any_identifier >> (fun s -> Varp(s,dpty))) ++
       a (Resword ")")
       >> (snd o fst))
  ||| (a (Resword "(") ++
       preterm ++
       a (Resword ")")
      >> (snd o fst))
  ||| (a (Resword "if") ++
       preterm ++
       a (Resword "then") ++
       preterm ++
       a (Resword "else") ++
       preterm
       >> lmk_ite)
  ||| ((a (Resword "if") ) ++ preterm ++ a (Resword "then") ++ preterm ++ a (Resword "else")
      >> (fun _ -> failwith "malformed else clause"))
  ||| ((a (Resword "if") ) ++ preterm ++ a (Resword "then") ++ preterm
      >> (fun _ -> failwith "missing else following then clause"))
  ||| ((a (Resword "if") ) ++ preterm ++ a (Resword "then")
      >> (fun _ -> failwith "malformed then clause in if-then-else statement"))
  ||| ((a (Resword "if") ) ++ preterm
      >> (fun _ -> failwith "missing 'then' reserved word in if-then-else statement"))
  ||| ((a (Resword "if") )
      >> (fun _ -> failwith "malformed if-then-else"))
  ||| (a (Resword "[") ++
       elistof preterm (a (Resword ";")) "semicolon separated list of terms" ++
       a (Resword "]")
       >> (pmk_list o snd o fst))
  ||| (a (Resword "[") ++
       elistof preterm (a (Resword ";")) "semicolon separated list of terms"
        >> (fun _ -> failwith "closing square bracket of list expected"))
  ||| (a (Resword "{") ++
       (elistof nocommapreterm (a (Ident ",")) "comma separated list of terms" ++  a (Resword "}")
              >> lmk_setenum
        ||| (preterm ++ a (Resword "|") ++ preterm ++ a (Resword "}")
              >> lmk_setabs)
        ||| (preterm ++ a (Resword "|") ++ preterm ++
             a (Resword "|") ++ preterm ++ a (Resword "}")
             >> lmk_setcompr))
      >> snd)
  ||| (a (Resword "{") >> (fun _ -> failwith "malformed set {}"))
  ||| (a (Resword "match") ++ preterm ++ a (Resword "with") ++ clauses
       >> (fun (((_,e),_),c) -> Combp(Combp(Varp("_MATCH",dpty),e),c)))
  ||| (a (Resword "match")  >> (fun _ -> failwith "malformed match-with statement"))
  ||| (a (Resword "function") ++ clauses
       >> (fun (_,c) -> Combp(Varp("_FUNCTION",dpty),c)))
  ||| (a (Resword "function")  >> (fun _ -> failwith "malformed function and pattern clauses"))
  ||| (a (Ident "#") ++ identifier ++
       possibly (a (Resword ".") ++ identifier >> snd)
       >> lmk_decimal)
  ||| (a (Ident "#")  >> (fun _ -> failwith "malformed numerical # identifier"))
  ||| (identifier >> (fun s -> Varp(s,dpty)))) i
  and pattern i =
    (preterm ++ possibly (a (Resword "when") ++ preterm >> snd)) i
  and clause i =
   ((pattern ++ (a (Resword "->") ++ preterm >> snd)) >> pmk_pattern) i
  and clauses i =
   ((possibly (a (Resword "|")) ++
     listof clause (a (Resword "|")) "pattern-match clause" >> snd)
    >> end_itlist (fun s t -> Combp(Combp(Varp("_SEQPATTERN",dpty),s),t))) i in
  (fun inp ->
    match inp with
      [Ident s] when
        not(String.length s >= 2 &&
            String.sub s 0 1 = "\"" &&
            String.sub s (String.length s - 1) 1 = "\"")
      -> Varp(s,dpty),[]
    | _ -> preterm inp);;

(* ------------------------------------------------------------------------- *)
(* Type and term parsers.                                                    *)
(* ------------------------------------------------------------------------- *)

let parse_type s =
  let pty,l = (parse_pretype o lex o explode) s in
  if l = [] then type_of_pretype pty
  else failwith "Unparsed input following type";;

let parse_term s =
  let ptm,l = (parse_preterm o lex o explode) s in
  if l = [] then
   (term_of_preterm o (retypecheck [])) ptm
  else failwith "Unparsed input following term";;
