(* ------------------------------------------------------------------------- *)
(* Load in the bignum library.                                               *)
(* ------------------------------------------------------------------------- *)

(* A wrapper of Zarith that has an interface of Num.
   However, this is different from the real Num library because it supports
   infinity and undef. If exception happens, Failure with the name of the
   exception is raised. *)
module Num = struct
  type num = Q.t

  let num_of_int (n:int):num = Q.of_int n

  let int_of_num (n:num):int =
    try Q.to_int n
    with Z.Overflow -> failwith "Z.Overflow"

  let float_of_num (n:num):float = Q.to_float n


  let add_num = Q.add

  let abs_num = Q.abs

  let ceiling_num (c:num) =
    try Q.of_bigint (Z.cdiv c.num c.den)
    with Division_by_zero -> failwith "Division_by_zero"

  let compare_num = Q.compare

  let div_num = Q.div

  let eq_num = Q.equal

  let floor_num (c:num) =
    try Q.of_bigint (Z.fdiv c.num c.den)
    with Division_by_zero -> failwith "Division_by_zero"

  let ge_num = Q.geq

  let gt_num = Q.gt

  let le_num = Q.leq

  let lt_num = Q.lt

  let max_num = Q.max

  let minus_num = Q.neg

  let min_num = Q.min

  let mod_num = fun x y ->
    Q.of_bigint (Z.erem (Q.to_bigint x) (Q.to_bigint y))

  let mult_num = Q.mul

  (* 1/2 -> 1, -1/2 -> -1 *)
  let round_num =
    let half = Q.make (Z.of_int 1) (Z.of_int 2) in
    let one = Q.make (Z.of_int 1) (Z.of_int 1) in
    fun x ->
      let s = Q.sign x in
      if s = 0 then x
      else
        let v = Q.abs x in
        let vint = floor_num v in
        let vfrac = Q.sub v vint in
        let absres =
          if Q.leq half vfrac
          then Q.add vint one
          else vint in
        Q.mul (Q.of_int s) absres

  let sign_num = Q.sign

  let sub_num = Q.sub

  let quo_num = fun x y ->
    Q.of_bigint (Z.ediv (Q.to_bigint x) (Q.to_bigint y))

  let is_integer_num (n:num) =
    Q.equal n (floor_num n)

  let succ_num = fun n ->
    Q.of_bigint (Z.succ (Q.to_bigint n))

  let string_of_num (n:num) = Q.to_string n

  (* Num's num_of_string only accepts integers. *)
  let num_of_string (s:string) =
    try Q.of_bigint (Z.of_string s)
    with _ -> failwith "num_of_string"

  let big_int_of_num = Q.to_bigint

  let num_of_big_int = Q.of_bigint

  let rec pow (base:num) (exponent:int):num =
    if exponent < 0 then
      (if exponent = (-1 lsl 62) then
        let half = pow base (-1 lsl 61) in
        mult_num half half
       else div_num (num_of_int 1) (pow base (-exponent)))
    else if exponent = 0 then num_of_int 1
    else if exponent = 1 then base
    else
      let half = pow base (exponent / 2) in
      let almostfull = mult_num half half in
      if exponent mod 2 = 1 then mult_num almostfull base
      else almostfull

  (* exponent must fit in the range of OCaml int type *)
  let power_num (base:num) (exponent:num):num = pow base (int_of_num exponent)

end;;

module Big_int = struct
  include Big_int_Z
end;;

let (=/) x y = Num.eq_num x y;;

let (<>/) x y = not (x =/ y);;

let (+/) x y = Num.add_num x y;;

let (-/) x y = Num.sub_num x y;;

let (//) x y = Num.div_num x y;;

let ( */) x y = Num.mult_num x y;;

let (</) x y = Num.lt_num x y;;

let (>/) x y = Num.gt_num x y;;

let (<=/) x y = Num.le_num x y;;

let (>=/) x y = Num.ge_num x y;;

let ( **/) x y = Num.power_num x y;;

let pp_print_num fmt (n:Num.num) =
  Format.pp_open_hbox fmt ();
  Format.pp_print_string fmt (Num.string_of_num n);
  Format.pp_close_box fmt ();;

let print_num = pp_print_num Format.std_formatter;;


include Num;;

let num = Num.num_of_int;;


module NumExt = struct
  let numdom (r:num):num * num =
    Q.of_bigint r.num, Q.of_bigint r.den

  let gcd_num =
      fun x y -> Q.of_bigint (Z.gcd (Q.to_bigint x) (Q.to_bigint y))

end;;

include NumExt;;
