(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2015-present Institut National de Recherche en Informatique et *)
(* en Automatique, ARM Ltd and the authors. All rights reserved.            *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

(** Simplified Arch64, for generators *)
open Printf

let arch = Archs.aarch64
let endian = Endian.Little
let base_type = CType.Base "int"


(*************)
(* Registers *)
(*************)

module PSTATE = struct
  type t =
    | N
    | Z
    | C
    | V
    | SM
    | ZA

  let to_string = function
    | N -> "N"
    | Z -> "Z"
    | C -> "C"
    | V -> "V"
    | SM -> "SM"
    | ZA -> "ZA"

  let pp p = "PSTATE." ^ (to_string p)

  let all = [N; Z; C; V]
end

type gpr =
  | R0  | R1  | R2  | R3
  | R4  | R5  | R6  | R7
  | R8  | R9  | R10 | R11
  | R12 | R13 | R14 | R15
  | R16 | R17 | R18 | R19
  | R20 | R21 | R22 | R23
  | R24 | R25 | R26 | R27
  | R28 | R29 | R30

type vec_reg =
  | V0  | V1  | V2  | V3
  | V4  | V5  | V6  | V7
  | V8  | V9  | V10 | V11
  | V12 | V13 | V14 | V15
  | V16 | V17 | V18 | V19
  | V20 | V21 | V22 | V23
  | V24 | V25 | V26 | V27
  | V28 | V29 | V30 | V31

type pred_reg =
  | P0  | P1  | P2  | P3
  | P4  | P5  | P6  | P7
  | P8  | P9  | P10 | P11
  | P12 | P13 | P14 | P15


type pred_mode =
  | Zero | Merge

let arrange_specifier =
[
  (1,64),".1D"  ; (1,128),".1Q" ;
  (2,16),".2H"  ; (2,32),".2S" ; (2,64),".2D";
  (4,8),".4B"   ; (4,16),".4H" ; (4,32),".4S";
  (8,8),".8B"   ; (8,16),".8H" ;
  (16, 8),".16B";
  (0,8),".B"    ; (0,16),".H"  ; (0,32),".S" ; (0,64),".D";
]

let sve_arrange_specifier =
[
  0,"";8,".B"; 16,".H"; 32,".S"; 64,".D"; 128,".Q";
]

let sve_pred_modifier =
[
  Zero,"/Z"; Merge,"/M";
]

type za_direction =
  | Vertical | Horizontal

let za_arrange_specifier =
[
  8,".B"; 16,".H"; 32,".S"; 64,".D"; 128,".Q";
]

let za_direction_specifier =
[
  Vertical,"V"; Horizontal,"H";
]

(********************)
(* System registers *)
(*  (Some of...)    *)
(********************)

type sysreg =
  CTR_EL0 | DCIZ_EL0 |
  MDCCSR_EL0 | DBGDTR_EL0 |
  DBGDTRRX_EL0 | DBGDTRTX_EL0 |
  ELR_EL1 | ESR_EL1 | SYS_NZCV |
  TFSR_ELx | VNCR_EL2
  | PAR_EL1
  | GCSPR_EL1

let sysregs = [
    CTR_EL0, "CTR_EL0";
    DCIZ_EL0, "DCIZ_EL0";
    MDCCSR_EL0, "MDCCSR_EL0";
    DBGDTR_EL0, "DBGDTR_EL0";
    DBGDTRRX_EL0, "DBGDTRRX_EL0";
    DBGDTRTX_EL0, "DBGDTRTX_EL0";
    ELR_EL1, "ELR_EL1";
    ESR_EL1, "ESR_EL1";
    SYS_NZCV, "NZCV";
    TFSR_ELx, "TFSR_ELx";
    VNCR_EL2, "VNCR_EL2";
    PAR_EL1, "PAR_EL1";
    GCSPR_EL1, "GCSPR_EL1";
  ]

let sysregs_map = [
    VNCR_EL2, 0xB0;
    ESR_EL1, 0x138;
    ELR_EL1, 0x230;
  ]

let sysreg_nv2off sreg = List.assoc_opt sreg sysregs_map

type reg =
  | ZR
  | Ireg of gpr
  | Tag of gpr
  | Vreg of (vec_reg * (int * int))
  | SIMDreg of vec_reg
  | Zreg of (vec_reg * int)
  | Preg of (pred_reg * int)
  | PMreg of (pred_reg * pred_mode)
  | ZAreg of (int * za_direction option * int)
  | Symbolic_reg of string
  | Internal of int
  | PState of PSTATE.t
  | SP
  | PC
  | ResAddr
  | SysReg of sysreg

(*************)
(* Utilities *)
(*************)

type variant = V32 | V64 | V128

type rev_variant = RV16 of variant | RV32 | RV64 of variant

let memo_of_rev = function
  | RV16 _ -> "REV16"
  | RV32 -> "REV32"
  | RV64 _ -> "REV"

let variant_of_rev = function
  | RV16 v|RV64 v -> v
  | RV32 -> V64

type 'k kr = K of 'k | RV of variant * reg
let k0 = K 0


let pp_label =
  let open BranchTarget in
  function
  | Lbl lbl -> Label.pp lbl
  | Offset o -> "." ^ BranchTarget.pp_offset o

open PPMode

let pp_hash m = match m with
| Ascii | Dot -> "#"
| Latex -> "\\#"
| DotFig -> "\\\\#"

let pp_k m v = pp_hash m ^ string_of_int v

(*
 * The boolean `compat` specifies backward comparibility.
 * Backward compatibility is important for preserving hashes.
 *)
type 'k basic_pp =
  { compat : bool; pp_k : 'k -> string;
    zerop : 'k -> bool; onep : 'k -> bool;
    k0 : 'k kr }

let gprs =
[
  R0 ; R1 ; R2 ; R3 ;
  R4 ; R5 ; R6 ; R7 ;
  R8 ; R9 ; R10; R11 ;
  R12; R13; R14; R15 ;
  R16; R17; R18; R19 ;
  R20; R21; R22; R23 ;
  R24; R25; R26; R27 ;
  R28; R29; R30;
]

let nzcv_regs = List.map (fun r -> PState r) PSTATE.all

let vec_regs =
[
  V0 ; V1 ; V2 ; V3 ;
  V4 ; V5 ; V6 ; V7 ;
  V8 ; V9 ; V10; V11;
  V12; V13; V14; V15;
  V16; V17; V18; V19;
  V20; V21; V22; V23;
  V24; V25; V26; V27;
  V28; V29; V30; V31;
]

let vregs = List.map (fun v -> Vreg (v,(4,32))) vec_regs

let zregs = List.map (fun z -> Zreg (z,32)) vec_regs

let pred_regs =
[
  P0 ;  P1; P2 ;  P3;
  P4 ;  P5; P6 ;  P7;
  P8 ;  P9; P10; P11;
  P12; P13; P14; P15;
]

let pregs = List.map (fun p -> Preg (p,32)) pred_regs

let zaslices =
  let tiles = List.init 4 (fun tile -> ZAreg (tile,None,32)) in
  let slices = List.init 4 Fun.id in
  List.concat (List.map (fun s -> List.map(fun r -> s,r) tiles ) slices)

let linkreg = Ireg R30
let elr_el1 = SysReg ELR_EL1
let esr_el1 = SysReg ESR_EL1
let tfsr = SysReg TFSR_ELx
let par_el1 = SysReg PAR_EL1
let gcspr_el1 = SysReg GCSPR_EL1

let cgprs =
[
 R0,"C0"  ; R1,"C1"  ; R2,"C2"  ; R3,"C3" ;
 R4,"C4"  ; R5,"C5"  ; R6,"C6"  ; R7,"C7" ;
 R8,"C8"  ; R9,"C9"  ; R10,"C10" ; R11,"C11" ;
 R12,"C12" ; R13,"C13" ; R14,"C14" ; R15,"C15" ;
 R16,"C16" ; R17,"C17" ; R18,"C18" ; R19,"C19" ;
 R20,"C20" ; R21,"C21" ; R22,"C22" ; R23,"C23" ;
 R24,"C24" ; R25,"C25" ; R26,"C26" ; R27,"C27" ;
 R28,"C28" ; R29,"C29" ; R30,"C30" ;
]

let cregs = (ZR,"CZR")::List.map (fun (r,s) -> Ireg r,s) cgprs

let xgprs =
[
 R0,"X0"  ; R1,"X1"  ; R2,"X2"  ; R3,"X3" ;
 R4,"X4"  ; R5,"X5"  ; R6,"X6"  ; R7,"X7" ;
 R8,"X8"  ; R9,"X9"  ; R10,"X10" ; R11,"X11" ;
 R12,"X12" ; R13,"X13" ; R14,"X14" ; R15,"X15" ;
 R16,"X16" ; R17,"X17" ; R18,"X18" ; R19,"X19" ;
 R20,"X20" ; R21,"X21" ; R22,"X22" ; R23,"X23" ;
 R24,"X24" ; R25,"X25" ; R26,"X26" ; R27,"X27" ;
 R28,"X28" ; R29,"X29" ; R30,"X30" ;
]

let xregs = (ZR,"XZR")::(SP,"SP")::List.map (fun (r,s) -> Ireg r,s) xgprs

let regs = xregs

let wgprs =
[
 R0,"W0"  ; R1,"W1"  ; R2,"W2"  ; R3,"W3" ;
 R4,"W4"  ; R5,"W5"  ; R6,"W6"  ; R7,"W7" ;
 R8,"W8"  ; R9,"W9"  ; R10,"W10" ; R11,"W11" ;
 R12,"W12" ; R13,"W13" ; R14,"W14" ; R15,"W15" ;
 R16,"W16" ; R17,"W17" ; R18,"W18" ; R19,"W19" ;
 R20,"W20" ; R21,"W21" ; R22,"W22" ; R23,"W23" ;
 R24,"W24" ; R25,"W25" ; R26,"W26" ; R27,"W27" ;
 R28,"W28" ; R29,"W29" ; R30,"W30" ;
]

let wregs =
  (ZR,"WZR")::List.map (fun (r,s) -> Ireg r,s) wgprs

let vvrs =
[
 V0,"V0"  ; V1,"V1"  ; V2,"V2"  ; V3,"V3" ;
 V4,"V4"  ; V5,"V5"  ; V6,"V6"  ; V7,"V7" ;
 V8,"V8"  ; V9,"V9"  ; V10,"V10" ; V11,"V11" ;
 V12,"V12" ; V13,"V13" ; V14,"V14" ; V15,"V15" ;
 V16,"V16" ; V17,"V17" ; V18,"V18" ; V19,"V19" ;
 V20,"V20" ; V21,"V21" ; V22,"V22" ; V23,"V23" ;
 V24,"V24" ; V25,"V25" ; V26,"V26" ; V27,"V27" ;
 V28,"V28" ; V29,"V29" ; V30,"V30" ; V31, "V31";
]

let bvrs =
[
 V0,"B0"  ; V1,"B1"  ; V2,"B2"  ; V3,"B3" ;
 V4,"B4"  ; V5,"B5"  ; V6,"B6"  ; V7,"B7" ;
 V8,"B8"  ; V9,"B9"  ; V10,"B10" ; V11,"B11" ;
 V12,"B12" ; V13,"B13" ; V14,"B14" ; V15,"B15" ;
 V16,"B16" ; V17,"B17" ; V18,"B18" ; V19,"B19" ;
 V20,"B20" ; V21,"B21" ; V22,"B22" ; V23,"B23" ;
 V24,"B24" ; V25,"B25" ; V26,"B26" ; V27,"B27" ;
 V28,"B28" ; V29,"B29" ; V30,"B30" ; V31, "B31";
]

let hvrs =
[
  V0,"H0"  ; V1,"H1"  ; V2,"H2"  ; V3,"H3" ;
  V4,"H4"  ; V5,"H5"  ; V6,"H6"  ; V7,"H7" ;
  V8,"H8"  ; V9,"H9"  ; V10,"H10" ; V11,"H11" ;
  V12,"H12" ; V13,"H13" ; V14,"H14" ; V15,"H15" ;
  V16,"H16" ; V17,"H17" ; V18,"H18" ; V19,"H19" ;
  V20,"H20" ; V21,"H21" ; V22,"H22" ; V23,"H23" ;
  V24,"H24" ; V25,"H25" ; V26,"H26" ; V27,"H27" ;
  V28,"H28" ; V29,"H29" ; V30,"H30" ; V31, "H31";
]

let svrs =
[
 V0,"S0"  ; V1,"S1"  ; V2,"S2"  ; V3,"S3" ;
 V4,"S4"  ; V5,"S5"  ; V6,"S6"  ; V7,"S7" ;
 V8,"S8"  ; V9,"S9"  ; V10,"S10" ; V11,"S11" ;
 V12,"S12" ; V13,"S13" ; V14,"S14" ; V15,"S15" ;
 V16,"S16" ; V17,"S17" ; V18,"S18" ; V19,"S19" ;
 V20,"S20" ; V21,"S21" ; V22,"S22" ; V23,"S23" ;
 V24,"S24" ; V25,"S25" ; V26,"S26" ; V27,"S27" ;
 V28,"S28" ; V29,"S29" ; V30,"S30" ; V31, "S31";
]

let dvrs =
[
 V0,"D0"  ; V1,"D1"  ; V2,"D2"  ; V3,"D3" ;
 V4,"D4"  ; V5,"D5"  ; V6,"D6"  ; V7,"D7" ;
 V8,"D8"  ; V9,"D9"  ; V10,"D10" ; V11,"D11" ;
 V12,"D12" ; V13,"D13" ; V14,"D14" ; V15,"D15" ;
 V16,"D16" ; V17,"D17" ; V18,"D18" ; V19,"D19" ;
 V20,"D20" ; V21,"D21" ; V22,"D22" ; V23,"D23" ;
 V24,"D24" ; V25,"D25" ; V26,"D26" ; V27,"D27" ;
 V28,"D28" ; V29,"D29" ; V30,"D30" ; V31, "D31";
]

let qvrs =
[
 V0,"Q0"  ; V1,"Q1"  ; V2,"Q2"  ; V3,"Q3" ;
 V4,"Q4"  ; V5,"Q5"  ; V6,"Q6"  ; V7,"Q7" ;
 V8,"Q8"  ; V9,"Q9"  ; V10,"Q10" ; V11,"Q11" ;
 V12,"Q12" ; V13,"Q13" ; V14,"Q14" ; V15,"Q15" ;
 V16,"Q16" ; V17,"Q17" ; V18,"Q18" ; V19,"Q19" ;
 V20,"Q20" ; V21,"Q21" ; V22,"Q22" ; V23,"Q23" ;
 V24,"Q24" ; V25,"Q25" ; V26,"Q26" ; V27,"Q27" ;
 V28,"Q28" ; V29,"Q29" ; V30,"Q30" ; V31, "Q31";
]

let zvrs =
[
  V0 ,"Z0";  V1 ,"Z1";  V2 ,"Z2";  V3 ,"Z3";
  V4 ,"Z4";  V5 ,"Z5";  V6 ,"Z6";  V7 ,"Z7";
  V8 ,"Z8";  V9 ,"Z9";  V10,"Z10"; V11,"Z11";
  V12,"Z12"; V13,"Z13"; V14,"Z14"; V15,"Z15";
  V16,"Z16"; V17,"Z17"; V18,"Z18"; V19,"Z19";
  V20,"Z20"; V21,"Z21"; V22,"Z22"; V23,"Z23";
  V24,"Z24"; V25,"Z25"; V26,"Z26"; V27,"Z27";
  V28,"Z28"; V29,"Z29"; V30,"Z30"; V31,"Z31";
]

let pvrs =
[
  P0 ,"P0";  P1 ,"P1";  P2 ,"P2";  P3 ,"P3";
  P4 ,"P4";  P5 ,"P5";  P6 ,"P6";  P7 ,"P7";
  P8 ,"P8";  P9 ,"P9";  P10,"P10"; P11,"P11";
  P12,"P12"; P13,"P13"; P14,"P14"; P15,"P15";
]

let simd_regs =
  let rs = bvrs @ hvrs @ svrs @ dvrs @ qvrs in
  List.map (fun (r,s) -> s,SIMDreg r) rs

let parse_list rs = List.map (fun (r,s) -> s,r) rs

let parse_some plist s =
  try
    let plist = List.map (fun (n,r) -> Misc.uppercase n,r) plist in
    let s = Misc.uppercase s in
    Some (List.assoc s plist)
  with Not_found -> None

let make_parser rs =
  let plist =  parse_list rs in
  parse_some plist

let parse_sysreg = make_parser sysregs

let parse_creg = make_parser cregs

let parse_xreg =
  let plist = ("LR",Ireg R30)::parse_list regs in
  parse_some plist

let parse_wreg = make_parser wregs

let parse_vreg =
  let vplist = parse_list vvrs
  and arplist = parse_list arrange_specifier in
  fun s ->
    try let (g1, g2) =
      ignore (Str.search_forward (Str.regexp "\\(V[0-9]+\\)\\(\\.[0-9]*[B,D,Q,H,S]\\)") (Misc.uppercase s) 0);
      (Str.matched_group 1 s, Str.matched_group 2 s);
      in Some (Vreg (List.assoc g1 vplist, List.assoc g2 arplist))
    with Not_found -> None

let parse_simd_reg = parse_some simd_regs

let parse_zreg =
  let zplist = parse_list zvrs
  and arplist = parse_list sve_arrange_specifier in
  fun s ->
    try let (g1, g2) =
        ignore (Str.search_forward (Str.regexp "\\(Z[0-9]+\\)\\(\\.[B,D,Q,H,S]\\)") (Misc.uppercase s) 0);
        (Str.matched_group 1 s, Str.matched_group 2 s);
      in Some (Zreg (List.assoc g1 zplist, List.assoc g2 arplist))
    with Not_found -> None

let parse_preg =
  let pplist = parse_list pvrs
  and splist = parse_list sve_arrange_specifier in
  fun s ->
    try let (g1, g2) =
          ignore (Str.search_forward (Str.regexp "\\(P[0-9]+\\)\\(\\.[B,D,Q,H,S]\\)?") (Misc.uppercase s) 0);
          let suffix = try Str.matched_group 2 s with Not_found -> "" in
          (Str.matched_group 1 s, suffix);
        in Some (Preg (List.assoc g1 pplist, List.assoc g2 splist))
      with Not_found -> None

let parse_pmreg =
  let pplist = parse_list pvrs
  and mplist = parse_list sve_pred_modifier in
  fun s ->
  try let (g1, g2) =
          ignore (Str.search_forward (Str.regexp "\\(P[0-9]+\\)\\(\\/[Z,M]\\)") (Misc.uppercase s) 0);
          (Str.matched_group 1 s, Str.matched_group 2 s);
        in Some (PMreg (List.assoc g1 pplist, List.assoc g2 mplist))
      with Not_found -> None

let parse_zareg =
  let arplist = parse_list za_arrange_specifier
  and dirplist = parse_list za_direction_specifier in
  fun s ->
    try let (g1,g2,g3) =
        ignore (Str.search_forward (Str.regexp "ZA\\([0-9]+\\)\\([V,H]\\)?\\(\\.[B,D,Q,H,S]\\)") (Misc.uppercase s) 0);
        let dir = try Some (Str.matched_group 2 s) with Not_found -> None in
        (Str.matched_group 1 s, dir, Str.matched_group 3 s);
      in let dir = match g2 with
      | Some d -> Some (List.assoc d dirplist)
      | None -> None in
      Some (ZAreg (int_of_string g1, dir, List.assoc g3 arplist))
    with Not_found -> None

let parse_reg s = match parse_vreg s with
| Some v -> Some v
| None ->
  begin match parse_xreg s with
    | Some v -> Some v
    | None -> Option.map (fun r -> (SysReg r)) (parse_sysreg s)
  end

let pp_sysreg r = try List.assoc r sysregs with Not_found -> assert false

let pp_creg r = match r with
| Symbolic_reg r -> "C%" ^ r
| Internal i -> Printf.sprintf "i%i" i
| PState p -> PSTATE.pp p
| ResAddr -> "Res"
| _ -> try List.assoc r cregs with Not_found -> assert false

let pp_xreg r = match r with
| Symbolic_reg r -> "X%" ^ r
| Internal i -> Printf.sprintf "i%i" i
| PState p -> PSTATE.pp p
| ResAddr -> "Res"
| PC -> "PC"
| SysReg sreg -> pp_sysreg sreg
| _ -> try List.assoc r regs with Not_found -> assert false

let pp_simd_vector_reg r = match r with
| Vreg (r',s) ->
  (try List.assoc r' vvrs with Not_found -> assert false) ^
  (try List.assoc s arrange_specifier with Not_found -> assert false)
| _ -> assert false

let pp_simd_scalar_reg rl r = match r with
| SIMDreg r -> (try List.assoc r rl with Not_found -> assert false)
| _ -> assert false

let pp_sm = function
  | PState p -> PSTATE.to_string p
  | _ -> assert false

let pp_sve_arrange_specifier s =
  try List.assoc s sve_arrange_specifier with Not_found -> assert false

let pp_zreg r = match r with
| Zreg (r',s) ->
  (try List.assoc r' zvrs with Not_found -> assert false) ^
  pp_sve_arrange_specifier s
| _ -> assert false

let pp_preg_simple r = match r with
| Preg (r',_)
| PMreg (r',_) ->
  (try List.assoc r' pvrs with Not_found -> assert false)
| _ -> assert false

let pp_sve_pred_modifier m =
  try List.assoc m sve_pred_modifier with Not_found -> assert false

let pp_preg r = match r with
| Preg (r',s) ->
  (try List.assoc r' pvrs with Not_found -> assert false) ^
  pp_sve_arrange_specifier s
| PMreg (r',m) ->
  (try List.assoc r' pvrs with Not_found -> assert false) ^
  pp_sve_pred_modifier m
| _ -> assert false


let pp_reg r = match r with
| Vreg _ -> pp_simd_vector_reg r
| SIMDreg _ -> pp_simd_scalar_reg vvrs r
| Zreg _ -> pp_zreg r
| Preg _ | PMreg _ -> pp_preg r
| ZAreg _ -> "ZA"
| _ -> pp_xreg r
let pp_i n = match n with
  | 1 -> "instr:\"NOP\""
  | 0 -> "instr:\"B .+12\""
  | _ -> Warn.fatal "instruction currently not supported"
let pp_wreg r = match r with
| Symbolic_reg r -> "W%" ^ r
| Internal i -> Printf.sprintf "i%i" i
| PState p -> PSTATE.pp p
| ResAddr -> "Res"
| _ -> try List.assoc r wregs with Not_found -> assert false


let pp_vreg v r = match v with
| V32 -> pp_wreg r
| V64 -> pp_xreg r
| V128 -> pp_creg r

let pp_za_arrange_specifier s =
  try List.assoc s za_arrange_specifier with Not_found -> assert false

let pp_za_dirrection_specifier s =
  try List.assoc s za_direction_specifier with Not_found -> assert false

let pp_zareg r = match r with
| ZAreg (tile,dir,s) ->
  let dir = match dir with
  | Some d -> pp_za_dirrection_specifier d
  | None -> "" in
  "ZA" ^ (string_of_int tile) ^ dir ^ pp_za_arrange_specifier s
| _ -> assert false

let reg_compare r1 r2 =
  let strip_reg r = match r with
  | Vreg (v,_) -> SIMDreg v
  | Zreg (v,_) -> SIMDreg v
  | Preg (v,_) -> Preg (v,0)
  | PMreg (v,_) -> Preg (v,0)
  | ZAreg _ -> ZAreg (0,None,0)
  | _ -> r in
  compare (strip_reg r1) (strip_reg r2)

let symb_reg_name = function
  | Symbolic_reg r -> Some r
  | _ -> None

let symb_reg r =  Symbolic_reg r

let type_reg r =
  let open CType in
  match r with
  | Vreg  (_,(n_elt,sz)) -> Array (TestType.tr_nbits sz,n_elt)
  | _ -> Base "int"

(************)
(* Barriers *)
(************)

type mBReqDomain = NSH | ISH | OSH | SY
let mBReqDomain_list = [SY; OSH; ISH; NSH]

let fold_domain f k =
  let k = f SY k in
  let k = f OSH k in
  let k = f ISH k in
  let k = f NSH k in
  k

let pp_domain = function
  | NSH -> "NSH"
  | ISH -> "ISH"
  | OSH -> "OSH"
  | SY -> "SY"

type mBReqTypes = LD | ST | FULL

let fold_type f k =
  let k = f FULL k in
  let k = f ST k in
  let k = f LD k in
  k

let pp_type = function
  | LD -> "LD"
  | ST -> "ST"
  | FULL -> ""


type barrier =
  | DMB of mBReqDomain*mBReqTypes
  | DSB of mBReqDomain*mBReqTypes
  | ISB
  | GCSB

type syncType =
  | DC_CVAU
  | IC_IVAU
type dirloc =
  | Next
  | Prev
let fold_barrier_option f k =
    fold_domain
      (fun d k ->
        fold_type (fun t k -> f d t k) k)
      k

let do_fold_dmb_dsb f k =
  fold_barrier_option
    (fun d t k -> f (DMB (d,t)) (f (DSB (d,t)) k))
    k

let fold_barrier f k =
  let k = do_fold_dmb_dsb f k in
  let k = f ISB k in
  let k = f GCSB k in
  k

let pp_option d t = match d,t with
| SY,FULL    -> pp_domain d
| SY,(LD|ST) -> pp_type t
| _,_ -> pp_domain d ^ pp_type t

let do_pp_barrier tag b = match b with
  | DMB (d,t) -> "DMB" ^ tag ^ pp_option d t
  | DSB (d,t) -> "DSB" ^ tag ^ pp_option d t
  | ISB -> "ISB"
  | GCSB -> "GCSB" ^ tag ^  "DSYNC"

let pp_barrier b = do_pp_barrier " " b
let pp_barrier_dot b = do_pp_barrier "." b

let barrier_compare = compare

(*********************)
(* Cache maintenance *)
(*********************)

module IC = struct
  type funct = I
  let pp_funct = function I -> "I"
  let fold_funct f k = f I k

  type typ = ALL | VA
  let pp_typ = function | ALL -> "ALL" | VA -> "VA"
  let fold_typ f k = k |> f ALL |> f VA

  type point = U
  let pp_point = function U -> "U"
  let fold_point f k = f U k

  type domain = IS | NO
  let pp_domain = function IS -> "IS" | NO -> ""
  let fold_domain f k = k |> f IS |> f NO

  type op = { funct:funct; typ:typ; point:point; domain:domain; }
  let ivau = { funct=I; typ=VA; point=U; domain=NO; }
  let iallu = { funct=I; typ=ALL; point=U; domain=NO; }

  let fold_op f k =
    fold_funct
      (fun funct k ->
        fold_typ
          (fun typ k ->
            fold_point
              (fun point k ->
                fold_domain
                  (fun domain k -> f {funct; typ; point; domain; } k)
                  k)
              k)
          k)
      k

  let pp_op op =
    pp_funct op.funct ^
    pp_typ op.typ ^
    pp_point op.point ^
    pp_domain op.domain

  let do_pp tag op = "IC" ^ tag ^ (pp_op op)
  let pp = do_pp " "
  let pp_dot = do_pp "."

  let all op = match op.typ with | VA -> false | ALL -> true

  let equal = ( = )
end

module DC = struct
  type funct = I | C | CI | Z
  let pp_funct = function
    | I -> "I"
    | C -> "C"
    | CI -> "CI"
    | Z -> "Z"
  let fold_funct f k = k |> f I |> f C |> f CI |> f Z

  type typ = VA | SW
  let pp_typ = function VA -> "VA" | SW -> "SW"
  let fold_typ f k = k |> f VA |> f SW

  type point = CO | U
  let pp_point = function CO -> "C" | U -> "U"
  let fold_point f k = k |> f CO |> f U

  type op = { funct:funct; typ:typ; point:point; }

  let cvau = { funct=C; typ=VA; point=U; }
  let civac = { funct=CI; typ=VA; point=CO; }

  let pp_op op =
    pp_funct op.funct ^
    pp_typ op.typ ^
    pp_point op.point

  let do_pp tag op = "DC" ^ tag ^ (pp_op op)
  let pp = do_pp " "
  let pp_dot = do_pp "."

  let sw op = match op.typ with | SW -> true | _ -> false
  let ci op = match op.funct with | CI -> true | _ -> false
  let c op = match op.funct with | C -> true | _ -> false
  let i op = match op.funct with | I -> true | _ -> false

  let fold_op f k =
    fold_funct
      (fun funct k ->
        fold_typ
          (fun typ k ->
            fold_point
              (fun point k -> f {funct; typ; point; } k)
              k)
          k)
      k

  let equal = ( = )
end

type level = |E0 |E1 |E2 |E3

let levels  = [E0;E1;E2;E3;]

let pp_level = function
    | E0 -> "E0"
    | E1 -> "E1"
    | E2 -> "E2"
    | E3 -> "E3"

let fold_EL f k =
  let k = f E0 k in
  let k = f E1 k in
  let k = f E2 k in
  let k = f E3 k in
  k

module TLBI = struct

  type typ =
    | ALL (*all translations at level *)
    | VMALL (*all stage 1 translations, current VMID *)
    | VMALLS12 (*all stage 1 & 2 translations, current VMID *)
    | ASID (*translations matching ASID *)
    | VA (*translations matching VA and ASID *)
    | VAL (*last-level translations matching VA and ASID *)
    | VAA (*translations matching VA, all ASIDs *)
    | VAAL (*last-level translations matching VA, all ASIDs *)
    | IPAS2 (*stage 2 translations matching IPA, current VMID *)
    | IPAS2L (*last-level stage 2 translations matching IPA, current VMID *)

  let pp_typ = function
    | ALL -> "ALL"
    | VMALL -> "VMALL"
    | VMALLS12 -> "VMALLS12"
    | ASID -> "ASID"
    | VA -> "VA"
    | VAL -> "VAL"
    | VAA -> "VAA"
    | VAAL -> "VAAL"
    | IPAS2 -> "IPAS2"
    | IPAS2L -> "IPAS2L"

  let fold_typ f k =
    let k = f ALL k in
    let k = f VMALL k in
    let k = f VMALLS12 k in
    let k = f ASID k in
    let k = f VA k in
    let k = f VAL k in
    let k = f VAA k in
    let k = f IPAS2 k in
    let k = f IPAS2L k
    in k

  type domain = | IS | No

  let pp_domain = function
    | IS -> "IS"
    | No -> ""

  let fold_domain f k =
    let k = f IS k in
    let k = f No k
    in k

  type op = { typ:typ; level:level; domain:domain; nXS:bool }

  let alle1is = { typ=ALL; level=E1; domain=IS; nXS=false; }
  let alle2is = { typ=ALL; level=E2; domain=IS; nXS=false; }

  let level_list = [ E0; E1; E2; E3 ]

  let typ_list = [ ALL; VMALL; VMALLS12; ASID; VA; VAL; VAA; VAAL; IPAS2; IPAS2L ]

  let domain_list = [ IS; No ]

  let rec fold_from_list xs f k = match xs with
  | [] -> k
  | x::xs -> fold_from_list xs f (f x k)

  let full_fold_op f k =
    fold_from_list
      typ_list
      (fun typ k ->
        fold_from_list level_list
          (fun level k ->
            fold_from_list domain_list
              (fun domain k ->
                 fold_from_list [ false; true ]
                   (fun nXS k -> f {typ; level; domain; nXS; } k )
                   k)
              k)
          k)
      k

  let fold_op f k =
    let k = f  {typ=VMALL; level=E1; domain=IS; nXS=false } k in
    f {typ=VAA; level=E1; domain=IS; nXS=false } k

  let pp_op { typ; level; domain; nXS; } =
    sprintf "%s%s%s%s" (pp_typ typ) (pp_level level) (pp_domain domain)
      (if nXS then "NXS" else "")

  let short_pp_op = function
    | {typ=VMALL; level=E1; domain=IS; nXS=false } -> "VMALL"
    | {typ=VAA; level=E1; domain=IS; nXS=false } -> ""
    | op -> pp_op op

  let is_at_level lvl op =  op.level = lvl

  let inv_all op = match op.typ with
    | ALL
    | VMALL
    | VMALLS12
        -> true
    | ASID
    | VA
    | VAL
    | VAA
    | VAAL
    | IPAS2
    | IPAS2L
      -> false

  let sets = [("TLBIIS", fun op->op.domain=IS); ("TLBInXS", (fun op -> op.nXS))]
end

module AT = struct

  type stages =
    | S1
    | S12

  let pp_stages = function
    | S1 -> "S1"
    | S12 -> "S12"

  type rw =
    | R
    | W

  let pp_rw = function
    | R -> "R"
    | W -> "W"

  type op = { stages:stages; level:level; rw:rw }

  let pp_op { stages; level; rw; } =
    sprintf "%s%s%s" (pp_stages stages) (pp_level level) (pp_rw rw)

end

(****************)
(* Instructions *)
(****************)

type lbl = BranchTarget.t

(* At type of writing, condition codes are specified in the ARM ARM, section C1.2.4, table C1-1 *)
type condition =
  | EQ (** Equal *)
  | NE (** Non Equal *)
  | CS (** Carry Set or unsigned higher or same, or HS *)
  | CC (** Carry Clear or unsigned lower, or LO *)
  | MI (** Negative, MInus *)
  | PL (** Positive or zero, PLus *)
  | VS (** V Set, signed overflow *)
  | VC (** V Clear, no signed overflow *)
  | HI (** Unsigned HIgher *)
  | LS (** Unsigned Lower or Same *)
  | GE (** Signed Greater or Equal *)
  | LT (** Signed Less Than *)
  | GT (** Signed Greater Than *)
  | LE (** Signed Less or Equal *)
  | AL (** Always executed *)
  (* | NV (** Always executed *) *)

let inverse_cond = function
  | NE -> EQ
  | EQ -> NE
  | LE -> GT
  | LT -> GE
  | GE -> GT
  | GT -> LE
  | CS -> CC
  | CC -> CS
  | MI -> PL
  | PL -> MI
  | VS -> VC
  | VC -> VS
  | HI -> LS
  | LS -> HI
  | AL -> AL

(* Pattern specifier for scalable vector instructions *)
type pattern =
  | POW2
  | VL1
  | VL2
  | VL3
  | VL4
  | VL5
  | VL6
  | VL7
  | VL8
  | VL16
  | VL32
  | VL64
  | VL128
  | VL256
  | MUL4
  | MUL3
  | ALL

type cnt_inc_op = CNT | INC

type op =
  | ADD | ADDS | SUB | SUBS | AND | ANDS | ORR | ORN
  | EOR | EON | ASR | LSR | LSL | ROR | BICS | BIC

type gc = CFHI | GCFLGS | GCPERM | GCSEAL | GCTAG | GCTYPE | GCVALUE
type sc = CLRPERM | CTHI | SCFLGS | SCTAG | SCVALUE
type simd_variant = VSIMD8 | VSIMD16 | VSIMD32 | VSIMD64 | VSIMD128
type cnt_inc_op_variant = cnt_inc_op * simd_variant
type adda_op_variant = za_direction

module CTERM = struct
  type cond = EQ|NE

  let pp = function
    | EQ -> "CTERMEQ"
    | NE -> "CTERMNE"
end

module Ext = struct (* Arguments of extended ADD and SUB operations *)

  type op = ADD|ADDS|SUB|SUBS

  let pp_op =  function
    | ADD -> "ADD"
    | ADDS -> "ADDS"
    | SUB -> "SUB"
    | SUBS -> "SUBS"

  type sext =
    | UXTB
    | UXTH
    | UXTW
    | UXTX
    | SXTB
    | SXTH
    | SXTW
    | SXTX

  let v2sext = function
    | V32 -> SXTW
    | V64 -> SXTX
    | V128 -> assert false

  let no_ext = UXTX,None

  type 'k ext = sext * 'k option

  let pp_sext = function
    | UXTB -> "UXTB"
    | UXTH -> "UXTH"
    | UXTW -> "UXTW"
    | UXTX -> "UXTX"
    | SXTB -> "SXTB"
    | SXTH -> "SXTH"
    | SXTW -> "SXTW"
    | SXTX -> "SXTX"

  let pp_ext m (e,ko) =
    sprintf "%s%s" (pp_sext e)
      (match ko with None -> "" | Some k -> " "^m.pp_k k)

end

type idx_mode = Idx | PreIdx | PostIdx
type 'k idx = 'k * idx_mode


module MemExt = struct (* Extensions for memory accesses *)

  (*********************)
  (* Register argument *)
  (*********************)

  type rext =
    | UXTW
    | LSL
    | SXTW
    | SXTX

  let v2sext = function
    | V32 -> SXTW
    | V64|V128 -> LSL

  let pp_sext = function
    | UXTW ->"UXTW"
    | LSL ->"LSL"
    | SXTW ->"SXTW"
    | SXTX ->"SXTX"

  type 'k ext =
    | Imm of 'k idx
    | Reg of variant * reg * rext * 'k
    | ZReg of reg * rext * 'k

  let v2idx_reg v r =
    match v with
    | V32 -> Reg (v,r,SXTW,0)
    | V64 -> Reg (v,r,LSL,0)
    | _ -> assert false

  let k2idx k = Imm (k,Idx)
  let zero = k2idx 0

end

module OpExt = struct (* Third argumen tabnd extension of operations *)

  type 'k shift =
    | LSL of 'k
    | LSR of 'k
    | ASR of 'k
    | ROR of 'k

  let no_shift = LSL 0

  let map_shift f = function
    | LSL k -> LSL (f k)
    | LSR k -> LSR (f k)
    | ASR k ->  ASR (f k)
    | ROR k ->  ROR (f k)

  let is_no_shift = function
    | LSL 0
    | LSR 0
    | ASR 0
    | ROR 0
      -> true
    | LSL _
    | LSR _
    | ASR _
    | ROR _
      -> false

  let pp_shift m = function
    | LSL k | LSR k | ASR k | ROR k
         when m.zerop k ->
       ""
    | LSL k -> sprintf ",LSL %s" (m.pp_k k)
    | LSR k ->  sprintf ",LSR %s" (m.pp_k k)
    | ASR k ->  sprintf ",ASR %s" (m.pp_k k)
    | ROR k ->  sprintf ",ROR %s" (m.pp_k k)

  type 'k ext =
    | Imm of 'k * 'k (* second 'k is (left) shift *)
    | Reg of reg * 'k shift

  let zero = Imm (0,0)

  let pp_ext m v = function
    | Imm (k,s) when m.zerop s ->
       m.pp_k k
    | Imm (k,s) ->
       sprintf "%s,LSL %s" (m.pp_k k) (m.pp_k s)
    | Reg (r,s) ->
       sprintf "%s%s" (pp_vreg v r) (pp_shift m s)
end

module  MOPLExt = struct

  type s = Signed|Unsigned

  type op = ADD | SUB

  type sop = s * op

  let memo sop = match sop with
    | Signed,ADD -> "SMADDL"
    | Signed,SUB -> "SMSUBL"
    | Unsigned,ADD -> "UMADDL"
    | Unsigned,SUB -> "UMSUBL"

  let memo_z sop = match sop with
    | Signed,ADD -> "SMULL"
    | Signed,SUB -> "SMNEGL"
    | Unsigned,ADD -> "UMULL"
    | Unsigned,SUB -> "UMNEGL"

end

module MOPExt = struct

  type op = ADD | SUB

  let memo op = match op with
    | ADD -> "MADD"
    | SUB -> "MSUB"

  let memo_z op = match op with
    | ADD -> "MUL"
    | SUB -> "MNEG"

end

let pp_variant = function
  | V32 -> "V32"
  | V64 -> "V64"
  | V128 -> "V128"

let tr_variant = function
  | V32 -> MachSize.Word
  | V64 -> MachSize.Quad
  | V128 -> MachSize.S128

let container_size = function
  | RV16 _ -> MachSize.Short
  | RV32 -> MachSize.Word
  | RV64 v -> tr_variant v


let tr_simd_variant = function
  | VSIMD8 -> MachSize.Byte
  | VSIMD16 -> MachSize.Short
  | VSIMD32 -> MachSize.Word
  | VSIMD64 -> MachSize.Quad
  | VSIMD128 -> MachSize.S128

let simd_variant_nbytes v = tr_simd_variant v |> MachSize.nbytes

type temporal = TT | NT
type ld_pair_opt = [`Pa | `PaN | `PaIQ | `PaA]
type st_pair_opt = [`Pa | `PaN | `PaIL | `PaL]

let ld_pair_opt_eq (a: ld_pair_opt) (b: ld_pair_opt) : bool =
  match (a, b) with
  | (`Pa, `Pa)
  | (`PaN, `PaN)
  | (`PaIQ, `PaIQ)
  | (`PaA, `PaA) -> true
  | _ -> false

let st_pair_opt_eq (a: st_pair_opt) (b: st_pair_opt) : bool =
  match (a, b) with
  | (`Pa, `Pa)
  | (`PaN, `PaN)
  | (`PaIL, `PaIL) 
  | (`PaL, `PaL) -> true
  | _ -> false

type ld_type = AA | XX | AX | AQ

let ldr_memo = function
  | AA -> "LDAR"
  | XX -> "LDXR"
  | AX -> "LDAXR"
  | AQ -> "LDAPR"

type ldxp_type = XP|AXP

let ldxp_memo = function
  | XP -> "LDXP"
  | AXP -> "LDAXP"

let ldp_memo = function
  | `Pa -> "LDP"
  | `PaN -> "LDNP"
  | `PaIQ -> "LDIAPP"
  | `PaA -> "LDAP"

let stp_memo = function
  | `Pa -> "STP"
  | `PaN -> "STNP"
  | `PaIL -> "STILP"
  | `PaL -> "STLP"

type st_type = YY | LY

let str_memo = function
  | YY -> "STXR"
  | LY -> "STLXR"

let stxp_memo = function
  | YY -> "STXP"
  | LY -> "STLXP"

type rmw_type = RMW_P | RMW_A | RMW_L | RMW_AL

type w_type = W_P | W_L

let rmw_to_w = function
  | RMW_P -> W_P
  | RMW_L -> W_L
  | RMW_A|RMW_AL -> assert false

let w_to_rmw = function
  | W_P -> RMW_P
  | W_L -> RMW_L

let rmw_memo = function
  | RMW_P -> ""
  | RMW_A -> "A"
  | RMW_L -> "L"
  | RMW_AL -> "AL"

let w_memo = function
  | W_P -> ""
  | W_L -> "L"

let cas_memo rmw = sprintf "CAS%s" (rmw_memo rmw)
let casp_memo rmw = sprintf "CASP%s" (rmw_memo rmw)
and swp_memo rmw = sprintf "SWP%s" (rmw_memo rmw)

type atomic_op =
  | A_ADD | A_EOR | A_SET | A_CLR
  | A_SMAX | A_SMIN | A_UMAX | A_UMIN

let atomic_op_equal = (=)

let pp_aop = function
  | A_ADD -> "ADD"
  | A_EOR -> "EOR"
  | A_SET -> "SET"
  | A_CLR -> "CLR"
  | A_SMAX -> "SMAX"
  | A_SMIN -> "SMIN"
  | A_UMAX -> "UMAX"
  | A_UMIN -> "UMIN"

let ldop_memo op rmw = sprintf "LD%s%s" (pp_aop op) (rmw_memo rmw)
and stop_memo op w = sprintf "ST%s%s" (pp_aop op) (w_memo w)

type bh = B | H (* Byte or Halfword *)

let pp_bh = function
  | B -> "B"
  | H -> "H"

let ldrs_memo bh = "LDRS" ^ pp_bh bh

let bh_to_sz = function
  | B -> MachSize.Byte
  | H -> MachSize.Short

let casbh_memo bh rmw = sprintf "%s%s" (cas_memo rmw) (pp_bh bh)
and swpbh_memo bh rmw = sprintf "%s%s" (swp_memo rmw) (pp_bh bh)
and ldopbh_memo op bh rmw = sprintf "%s%s" (ldop_memo op rmw) (pp_bh bh)
and stopbh_memo op bh  rmw = sprintf "%s%s" (stop_memo op rmw) (pp_bh bh)
and ldrbh_memo bh t =  sprintf "%s%s" (ldr_memo t) (pp_bh bh)
and strbh_memo bh t =  sprintf "%s%s" (str_memo t) (pp_bh bh)

type opsel = Cpy | Inc | Inv | Neg

let sel_memo = function
  | Cpy -> "CSEL"
  | Inc -> "CSINC"
  | Inv -> "CSINV"
  | Neg -> "CSNEG"

(* Inline barrel shift and extenders - need to add all variants *)
type 'k s
  = S_LSL of 'k
  | S_LSR of 'k
  | S_ASR of 'k
  | S_MSL of 'k
  | S_NOEXT

let pp_barrel_shift sep s pp_k = match s with
  | S_LSL(k) -> sep ^ "LSL "  ^ (pp_k k)
  | S_LSR(k) -> sep ^ "LSR "  ^ (pp_k k)
  | S_ASR(k) -> sep ^ "ASR "  ^ (pp_k k)
  | S_MSL(k) -> sep ^ "MSL "  ^ (pp_k k)
  | S_NOEXT  -> ""

let pp_imm n = "#" ^ string_of_int n

type 'k kinstruction =
  | I_NOP
(* Branches *)
  | I_B of lbl | I_BR of reg
  | I_BC of condition * lbl
  | I_CBZ of variant * reg * lbl
  | I_CBNZ of variant * reg * lbl
  | I_TBNZ of variant * reg * 'k * lbl
  | I_TBZ of variant * reg * 'k * lbl
  | I_BL of lbl | I_BLR of reg
  | I_RET of reg option
  | I_ERET
  | I_SVC of 'k
(* Load and Store *)
  | I_LDR of variant * reg * reg * 'k MemExt.ext
  | I_LDRSW of reg * reg * 'k MemExt.ext
  | I_LDUR of variant * reg * reg * 'k
(* Neon Extension Load and Store*)
  | I_LD1 of reg list * int * reg * 'k kr
  | I_LDAP1 of reg list * int * reg * 'k kr
  | I_LD1M of reg list * reg * 'k kr
  | I_LD1R of reg list * reg * 'k kr
  | I_LD2 of reg list * int * reg * 'k kr
  | I_LD2M of reg list * reg * 'k kr
  | I_LD2R of reg list * reg * 'k kr
  | I_LD3 of reg list * int * reg * 'k kr
  | I_LD3M of reg list * reg * 'k kr
  | I_LD3R of reg list * reg * 'k kr
  | I_LD4 of reg list * int * reg * 'k kr
  | I_LD4M of reg list * reg * 'k kr
  | I_LD4R of reg list * reg * 'k kr
  | I_ST1 of reg list * int * reg * 'k kr
  | I_STL1 of reg list * int * reg * 'k kr
  | I_ST1M of reg list * reg * 'k kr
  | I_ST2 of reg list * int * reg * 'k kr
  | I_ST2M of reg list * reg * 'k kr
  | I_ST3 of reg list * int * reg * 'k kr
  | I_ST3M of reg list * reg * 'k kr
  | I_ST4 of reg list * int * reg * 'k kr
  | I_ST4M of reg list * reg * 'k kr
  | I_LDP_SIMD of temporal * simd_variant * reg * reg * reg * 'k idx
  | I_STP_SIMD of temporal * simd_variant * reg * reg * reg * 'k idx
  | I_LDR_SIMD of simd_variant * reg * reg * 'k MemExt.ext
  | I_STR_SIMD of simd_variant * reg * reg * 'k MemExt.ext
  | I_LDUR_SIMD of simd_variant * reg * reg * 'k
  | I_LDAPUR_SIMD of simd_variant * reg * reg * 'k
  | I_STUR_SIMD of simd_variant * reg * reg * 'k
  | I_STLUR_SIMD of simd_variant * reg * reg * 'k
  | I_ADDV of simd_variant * reg * reg
  | I_DUP of reg * variant * reg
  | I_FMOV_TG of variant * reg * simd_variant * reg
  | I_MOV_VE of reg * int * reg * int
  | I_MOV_V of reg * reg
  | I_MOV_TG of variant * reg * reg * int
  | I_MOV_FG of reg * int * variant * reg
  | I_MOV_S of simd_variant * reg * reg * int
  | I_MOVI_V of reg * 'k * 'k s
  | I_MOVI_S of simd_variant * reg * 'k
  | I_OP3_SIMD of op * reg * reg * reg
  | I_ADD_SIMD of reg * reg * reg
  | I_ADD_SIMD_S of reg * reg * reg
  (* More loads *)
  | I_LDP of ld_pair_opt * variant * reg * reg * reg * 'k idx
  | I_LDPSW of reg * reg * reg * 'k idx
  | I_LDAR of variant * ld_type * reg * reg
  | I_LDXP of variant * ldxp_type * reg * reg * reg
  (* Stores *)
  | I_STR of variant * reg * reg * 'k MemExt.ext
  | I_STP of st_pair_opt * variant * reg * reg * reg * 'k idx
  | I_STLR of variant * reg * reg
  | I_STXR of variant * st_type * reg * reg * reg
  | I_STXP of variant * st_type * reg * reg * reg * reg
(* Scalable Vector Extension*)
  (* PTRUE <Pd>.<T>{, <pattern>} *)
  | I_PTRUE of reg * pattern
  (* WHILEL{LT,LE,LO,LS} <Pd>.<T>, <R><n>, <R><m> *)
  | I_WHILELT of reg * variant * reg * reg
  | I_WHILELE of reg * variant * reg * reg
  | I_WHILELO of reg * variant * reg * reg
  | I_WHILELS of reg * variant * reg * reg
  (* UADDV <Dd>, <Pg>, <Zn>.<T> *)
  | I_UADDV of simd_variant * reg * reg * reg
  (*
   * LD1{B,H,W,D} (scalar plus scalar, single register)
   *
   * LD1B { <Zt>.<T> }, <Pg>/Z, [<Xn|SP>, <Xm>] for T in  D,S,H,B
   * LD1H { <Zt>.<T> }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #1] for T in D,S,H
   * LD1W { <Zt>.<T> }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #2] for T in D,S
   * LD1D { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #3]
   *
   * LD1{B,H,W,D} (scalar plus immediate, single register)
   *
   * LD1B { <Zt>.<T> }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}] for T in  D,S,H,B
   * LD1H { <Zt>.<T> }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}] for T in D,S,H
   * LD1W { <Zt>.S }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}] for T in D,S
   * LD1D { <Zt>.D }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   *
   * LD1{B,H,W,D} (scalar plus vector)
   *
   * LD1B { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D, <mod>]
   * LD1B { <Zt>.S }, <Pg>/Z, [<Xn|SP>, <Zm>.S, <mod>]
   * LD1B { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D]
   * LD1H { <Zt>.S }, <Pg>/Z, [<Xn|SP>, <Zm>.S, <mod> #1]
   * LD1H { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D, <mod> #1]
   * LD1H { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D, <mod>]
   * LD1H { <Zt>.S }, <Pg>/Z, [<Xn|SP>, <Zm>.S, <mod>]
   * LD1H { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D, LSL #1]
   * LD1H { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D]
   * LD1W { <Zt>.S }, <Pg>/Z, [<Xn|SP>, <Zm>.S, <mod> #2]
   * LD1W { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D, <mod> #2]
   * LD1W { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D, <mod>]
   * LD1W { <Zt>.S }, <Pg>/Z, [<Xn|SP>, <Zm>.S, <mod>]
   * LD1W { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D, LSL #2]
   * LD1W { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D]
   * LD1D { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D, <mod> #3]
   * LD1D { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D, <mod>]
   * LD1D { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D, LSL #3]
   * LD1D { <Zt>.D }, <Pg>/Z, [<Xn|SP>, <Zm>.D]
   *)
   | I_LD1SP of simd_variant * reg list * reg * reg * 'k MemExt.ext
  (*
   * LD2{B,H,W,D} (scalar plus scalar)
   *
   * LD2B { <Zt1>.B, <Zt2>.B }, <Pg>/Z, [<Xn|SP>, <Xm>]
   * LD2H { <Zt1>.H, <Zt2>.H }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #1]
   * LD2W { <Zt1>.S, <Zt2>.S }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #2]
   * LD2D { <Zt1>.D, <Zt2>.D }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #3]
   *
   * LD2{B,H,W,D} (scalar plus immediate)
   *
   * LD2B { <Zt1>.B, <Zt2>.B }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   * LD2H { <Zt1>.H, <Zt2>.H }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   * LD2W { <Zt1>.S, <Zt2>.S }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   * LD2D { <Zt1>.D, <Zt2>.D }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   *)
  | I_LD2SP of simd_variant * reg list * reg * reg * 'k MemExt.ext
  (*
   * LD3{B,H,W,D} (scalar plus scalar)
   *
   * LD3B { <Zt1>.B, <Zt2>.B, <Zt3>.B }, <Pg>/Z, [<Xn|SP>, <Xm>]
   * LD3H { <Zt1>.H, <Zt2>.H, <Zt3>.H }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #1]
   * LD3W { <Zt1>.S, <Zt2>.S, <Zt3>.S }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #2]
   * LD3D { <Zt1>.D, <Zt2>.D, <Zt3>.D }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #3]
   *
   * LD3{B,H,W,D} (scalar plus immediate)
   *
   * LD3B { <Zt1>.B, <Zt2>.B, <Zt3>.B }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   * LD3H { <Zt1>.H, <Zt2>.H, <Zt3>.H }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   * LD3W { <Zt1>.S, <Zt2>.S, <Zt3>.S }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   * LD3D { <Zt1>.D, <Zt2>.D, <Zt3>.D }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   *)
  | I_LD3SP of simd_variant *  reg list * reg * reg * 'k MemExt.ext
  (*
   * LD4{B,H,W,D} (scalar plus scalar)
   *
   * LD4B { <Zt1>.B, <Zt2>.B, <Zt3>.B, <Zt4>.B }, <Pg>/Z, [<Xn|SP>, <Xm>]
   * LD4H { <Zt1>.H, <Zt2>.H, <Zt3>.H, <Zt4>.H }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #1]
   * LD4W { <Zt1>.S, <Zt2>.S, <Zt3>.S, <Zt4>.S }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #2]
   * LD4D { <Zt1>.D, <Zt2>.D, <Zt3>.D, <Zt4>.D }, <Pg>/Z, [<Xn|SP>, <Xm>, LSL #3]
   *
   * LD4{B,H,W,D} (scalar plus immediate)
   *
   * LD4B { <Zt1>.B, <Zt2>.B, <Zt3>.B, <Zt4>.B }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   * LD4H { <Zt1>.H, <Zt2>.H, <Zt3>.H, <Zt4>.H }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   * LD4W { <Zt1>.S, <Zt2>.S, <Zt3>.S, <Zt4>.S }, <Pg>/Z, [<Xn|SP>{, #<imm>, MUL VL}]
   *)
  | I_LD4SP of simd_variant * reg list * reg * reg * 'k MemExt.ext
  (*
   * ST1{B,H,W,D} (scalar plus scalar)
   *
   * ST1B { <Zt>.<T> }, <Pg>, [<Xn|SP>, <Xm>] for T in  D,S,H,B
   * ST1H { <Zt>.<T> }, <Pg>, [<Xn|SP>, <Xm>, LSL #1] for T in D,S,H
   * ST1W { <Zt>.<T> }, <Pg>, [<Xn|SP>, <Xm>, LSL #2] for T in D,S
   * ST1D { <Zt>.D }, <Pg>, [<Xn|SP>, <Xm>, LSL #3]
   *
   * ST1{B,H,W,D} (scalar plus immediate)
   *
   * ST1B { <Zt>.<T> }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}] for T in  D,S,H,B
   * ST1H { <Zt>.<T> }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}] for T in D,S,H
   * ST1W { <Zt>.<T> }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}] for T in D,S
   * ST1D { <Zt>.D }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   *
   * ST1{B,H,W,D} (scalar plus vector)
   *
   * ST1B { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D, <mod>]
   * ST1B { <Zt>.S }, <Pg>, [<Xn|SP>, <Zm>.S, <mod>]
   * ST1B { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D]
   * ST1H { <Zt>.S }, <Pg>, [<Xn|SP>, <Zm>.S, <mod> #1]
   * ST1H { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D, <mod> #1]
   * ST1H { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D, <mod>]
   * ST1H { <Zt>.S }, <Pg>, [<Xn|SP>, <Zm>.S, <mod>]
   * ST1H { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D, LSL #1]
   * ST1H { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D]
   * ST1W { <Zt>.S }, <Pg>, [<Xn|SP>, <Zm>.S, <mod> #2]
   * ST1W { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D, <mod> #2]
   * ST1W { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D, <mod>]
   * ST1W { <Zt>.S }, <Pg>, [<Xn|SP>, <Zm>.S, <mod>]
   * ST1W { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D, LSL #2]
   * ST1W { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D]
   * ST1D { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D, <mod> #3]
   * ST1D { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D, <mod>]
   * ST1D { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D, LSL #3]
   * ST1D { <Zt>.D }, <Pg>, [<Xn|SP>, <Zm>.D]
   *)
  | I_ST1SP of simd_variant * reg list * reg * reg * 'k MemExt.ext
  (*
   * ST2{B,H,W,D} (scalar plus scalar)
   *
   * ST2B { <Zt1>.B, <Zt2>.B }, <Pg>, [<Xn|SP>, <Xm>]
   * ST2H { <Zt1>.H, <Zt2>.H }, <Pg>, [<Xn|SP>, <Xm>, LSL #1]
   * ST2W { <Zt1>.S, <Zt2>.S }, <Pg>, [<Xn|SP>, <Xm>, LSL #2]
   * ST2D { <Zt1>.D, <Zt2>.D }, <Pg>, [<Xn|SP>, <Xm>, LSL #3]
   *
   * ST2{B,H,W,D} (scalar plus immediate)
   *
   * ST2B { <Zt1>.B, <Zt2>.B }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   * ST2H { <Zt1>.H, <Zt2>.H }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   * ST2W { <Zt1>.S, <Zt2>.S }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   * ST2D { <Zt1>.D, <Zt2>.D }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   *)
  | I_ST2SP of simd_variant * reg list * reg * reg * 'k MemExt.ext
  (*
   * ST3{B,H,W,D} (scalar plus scalar)
   *
   * ST3B { <Zt1>.B, <Zt2>.B, <Zt3>.B }, <Pg>, [<Xn|SP>, <Xm>]
   * ST3H { <Zt1>.H, <Zt2>.H, <Zt3>.H }, <Pg>, [<Xn|SP>, <Xm>, LSL #1]
   * ST3W { <Zt1>.S, <Zt2>.S, <Zt3>.S }, <Pg>, [<Xn|SP>, <Xm>, LSL #2]
   * ST3D { <Zt1>.D, <Zt2>.D, <Zt3>.D }, <Pg>, [<Xn|SP>, <Xm>, LSL #3]
   *
   * ST3{B,H,W,D} (scalar plus immediate)
   *
   * ST3B { <Zt1>.B, <Zt2>.B }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   * ST3H { <Zt1>.H, <Zt2>.H }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   * ST3W { <Zt1>.S, <Zt2>.S }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   * ST3D { <Zt1>.D, <Zt2>.D }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   *)
  | I_ST3SP of simd_variant * reg list * reg * reg * 'k MemExt.ext
  (*
   * ST4{B,H,W,D} (scalar plus scalar)
   *
   * ST4B { <Zt1>.B, <Zt2>.B, <Zt3>.B, <Zt4>.B }, <Pg>, [<Xn|SP>, <Xm>]
   * ST4H { <Zt1>.H, <Zt2>.H, <Zt3>.H, <Zt4>.H }, <Pg>, [<Xn|SP>, <Xm>, LSL #1]
   * ST4W { <Zt1>.S, <Zt2>.S, <Zt3>.S, <Zt4>.S }, <Pg>, [<Xn|SP>, <Xm>, LSL #2]
   * ST4D { <Zt1>.D, <Zt2>.D, <Zt3>.D, <Zt4>.D }, <Pg>, [<Xn|SP>, <Xm>, LSL #3]
   *
   * ST4{B,H,W,D} (scalar plus immediate)
   *
   * ST4B { <Zt1>.B, <Zt2>.B }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   * ST4H { <Zt1>.H, <Zt2>.H }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   * ST4W { <Zt1>.S, <Zt2>.S }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   * ST4D { <Zt1>.D, <Zt2>.D }, <Pg>, [<Xn|SP>{, #<imm>, MUL VL}]
   *)
  | I_ST4SP of simd_variant * reg list * reg * reg * 'k MemExt.ext
  (* MOV <Zd>.<T>, #<imm>{, <shift>} *)
  | I_MOV_SV of reg * 'k * 'k s
  (* DUP <Zd>.<T>, <R><n|SP> *)
  | I_DUP_SV of reg * variant * reg
  (* ADD <Zd>.<T>, <Zn>.<T>, <Zm>.<T> *)
  | I_ADD_SV of reg * reg * reg
  (* NEG <Zd>.<T>, <Pg>/M, <Zn>.<T> *)
  | I_NEG_SV of reg * reg * reg
  (* MOVPRFX <Zd>.<T>, <Pg>/<ZM>, <Zn>.<T> *)
  | I_MOVPRFX of reg * reg * reg
  (* EOR <Zd>.D, <Zn>.D, <Zm>.D, vectors, unpredicated *)
  | I_OP3_SV of op * reg * reg * reg
  (* INDEX <Zd>.<T>, <R><n>, #<imm> *)
  | I_INDEX_SI of reg * variant * reg * 'k
  (* INDEX <Zd>.<T>, #<imm>, <R><m> *)
  | I_INDEX_IS of reg * variant * 'k * reg
  (* INDEX <Zd>.<T>, <R><n>, <R><m> *)
  | I_INDEX_SS of reg * variant * reg * reg
  (* INDEX <Zd>.<T>, #<imm1>, #<imm2> *)
  | I_INDEX_II of reg * 'k * 'k
  (* RDVL <Xd>, #<imm> *)
  | I_RDVL of reg * 'k
  (* ADDVL <Xd>, <Xn>, #<imm> *)
  | I_ADDVL of reg * reg * 'k
(* {CNT,INC}<B|H|W|D> <Xd>{, pattern{, MULL #imm}} *)
  | I_CNT_INC_SVE of ( cnt_inc_op * simd_variant ) * reg * pattern * 'k
  (* CTERM{EQ,NE} <Rn>,<Rm> *)
  | I_CTERM of CTERM.cond * variant * reg * reg
(* Scalable Matrix Extension *)
  (*
   * LD1{B,H,W,D,Q} (scalar plus scalar, tile slice)
   *
   * LD1B { ZA0<HV>.B[<Ws>, <offs>] }, <Pg>/Z, [<Xn|SP>{, <Xm>}]
   * LD1H { <ZAt><HV>.H[<Ws>, <offs>] }, <Pg>/Z, [<Xn|SP>{, <Xm>, LSL #1}]
   * LD1W { <ZAt><HV>.S[<Ws>, <offs>] }, <Pg>/Z, [<Xn|SP>{, <Xm>, LSL #2}]
   * LD1D { <ZAt><HV>.D[<Ws>, <offs>] }, <Pg>/Z, [<Xn|SP>{, <Xm>, LSL #3}]
   * LD1Q { <ZAt><HV>.Q[<Ws>, <offs>] }, <Pg>/Z, [<Xn|SP>{, <Xm>, LSL #4}]
   *)
  | I_LD1SPT of simd_variant * reg * reg * 'k * reg * reg * 'k MemExt.ext
  (*
   * ST1{B,H,W,D,Q} (scalar plus scalar, tile slice)
   *
   * ST1B { ZA0<HV>.B[<Ws>, <offs>] }, <Pg>, [<Xn|SP>{, <Xm>}]
   * ST1H { <ZAt><HV>.H[<Ws>, <offs>] }, <Pg>, [<Xn|SP>{, <Xm>, LSL #1}]
   * ST1W { <ZAt><HV>.S[<Ws>, <offs>] }, <Pg>, [<Xn|SP>{, <Xm>, LSL #2}]
   * ST1D { <ZAt><HV>.D[<Ws>, <offs>] }, <Pg>, [<Xn|SP>{, <Xm>, LSL #3}]
   * ST1Q { <ZAt><HV>.Q[<Ws>, <offs>] }, <Pg>, [<Xn|SP>{, <Xm>, LSL #4}]
   *)
  | I_ST1SPT of simd_variant * reg * reg * 'k * reg * reg * 'k MemExt.ext
  (*
   * MOVA (vector to tile, single)
   *
   * MOVA ZA0<HV>.B[<Ws>, <offs>], <Pg>/M, <Zn>.B
   * MOVA <ZAd><HV>.H[<Ws>, <offs>], <Pg>/M, <Zn>.H
   * MOVA <ZAd><HV>.S[<Ws>, <offs>], <Pg>/M, <Zn>.S
   * MOVA <ZAd><HV>.D[<Ws>, <offs>], <Pg>/M, <Zn>.D
   * MOVA <ZAd><HV>.Q[<Ws>, <offs>], <Pg>/M, <Zn>.Q
   *)
  | I_MOVA_VT of reg * reg * 'k * reg * reg
  (*
   * MOVA (tile to vector, single)
   *
   * MOVA <Zd>.B, <Pg>/M, ZA0<HV>.B[<Ws>, <offs>]
   * MOVA <Zd>.H, <Pg>/M, <ZAn><HV>.H[<Ws>, <offs>]
   * MOVA <Zd>.S, <Pg>/M, <ZAn><HV>.S[<Ws>, <offs>]
   * MOVA <Zd>.D, <Pg>/M, <ZAn><HV>.D[<Ws>, <offs>]
   * MOVA <Zd>.Q, <Pg>/M, <ZAn><HV>.Q[<Ws>, <offs>]
   *)
  | I_MOVA_TV of reg * reg * reg * reg * 'k
  (*
   * ADDHA <ZAda>.S, <Pn>/M, <Pm>/M, <Zn>.S
   * ADDVA <ZAda>.S, <Pn>/M, <Pm>/M, <Zn>.S
   *)
   | I_ADDA of za_direction * reg * reg * reg * reg
  (* SMSTART {<option>} *)
  | I_SMSTART of reg option
  (* SMSTOP {<option>} *)
  | I_SMSTOP  of reg option
(* Morello *)
  | I_ALIGND of reg * reg * 'k
  | I_ALIGNU of reg * reg * 'k
  | I_BUILD of reg * reg * reg
  | I_CHKEQ of reg * reg
  | I_CHKSLD of reg
  | I_CHKTGD of reg
  | I_CLRTAG of reg * reg
  | I_CPYTYPE of reg * reg * reg
  | I_CPYVALUE of reg * reg * reg
  | I_CSEAL of reg * reg * reg
  | I_GC of gc * reg * reg
  | I_LDCT of reg * reg
  | I_SC of sc * reg * reg * reg
  | I_SEAL of reg * reg * reg
  | I_STCT of reg * reg
  | I_UNSEAL of reg * reg * reg
(* Guarded Control Stack Extention *)
  (* GCSPOPM {<Xt>} *)
  | I_GCSPOPM of reg
  (* GCSPUSHM <Xt> *)
  | I_GCSPUSHM of reg
  (* GCSSTR <Xt>, [<Xn|SP>] *)
  | I_GCSSTR of reg * reg
  (* GCSSS1 <Xt> *)
  | I_GCSSS1 of reg
  (* GCSSS2 <Xt> *)
  | I_GCSSS2 of reg
(* Idem for bytes and half words *)
  | I_LDRBH of bh * reg * reg * 'k MemExt.ext
  | I_LDRS of (variant * bh) * reg * reg * 'k MemExt.ext
  | I_LDARBH of bh * ld_type * reg * reg
  | I_STRBH of bh * reg * reg * 'k MemExt.ext
  | I_STLRBH of bh * reg * reg
  | I_STXRBH of bh * st_type * reg * reg * reg
(* CAS *)
  | I_CAS of variant * rmw_type * reg * reg * reg
  | I_CASBH of bh * rmw_type  * reg * reg * reg
  | I_CASP of variant * rmw_type * reg * reg * reg * reg * reg
(* SWP *)
  | I_SWP of variant * rmw_type * reg * reg * reg
  | I_SWPBH of bh * rmw_type  * reg * reg * reg
(* Fetch and op *)
  | I_LDOP of  atomic_op * variant * rmw_type  * reg * reg * reg
  | I_LDOPBH of atomic_op * bh * rmw_type  * reg * reg * reg
  | I_STOP of  atomic_op * variant * w_type * reg * reg
  | I_STOPBH of  atomic_op * bh * w_type  * reg * reg
(* Operations *)
  | I_MOV of variant * reg * 'k kr
  | I_MOVZ of variant * reg * 'k * 'k s
  | I_MOVN of variant * reg * 'k * 'k s
  | I_MOVK of variant * reg * 'k * 'k s
  | I_SXTW of reg * reg
  | I_SBFM of variant * reg * reg * 'k * 'k
  | I_UBFM of variant * reg * reg * 'k * 'k
  | I_ADDSUBEXT of
      variant * Ext.op * reg * reg * (variant * reg) * 'k Ext.ext
  | I_MOPL of MOPLExt.sop * reg * reg * reg *reg
  | I_MOP of MOPExt.op * variant * reg * reg * reg * reg
  | I_OP3 of variant * op * reg * reg * 'k OpExt.ext
  | I_ADR of reg * lbl
  | I_RBIT of variant * reg * reg
  | I_ABS of variant * reg * reg
  | I_REV of rev_variant * reg * reg
  | I_EXTR of variant * reg * reg * reg * 'k
(* Barrier *)
  | I_FENCE of barrier
(* Conditional select *)
  | I_CSEL of variant * reg *reg * reg * condition * opsel
(* Cache maintenance *)
  | I_IC of IC.op * reg
  | I_DC of DC.op * reg
  | I_TLBI of TLBI.op * reg
(* Address translation *)
  | I_AT of AT.op * reg
(* Read system register *)
  | I_MRS of reg * sysreg
(* Write system register *)
  | I_MSR of sysreg * reg
(* Memory Tagging *)
  | I_STG of reg * reg * 'k idx
  | I_ST2G of reg * reg * 'k idx
  | I_STZG of reg * reg * 'k idx
  | I_STZ2G of reg * reg * 'k idx
  | I_LDG of reg * reg * 'k
(* IRG <Xd|SP>, <Xn|SP>{, <Xm>} *)
  | I_IRG of reg * reg * reg
  | I_UDF of 'k
(* Pointer Authentication Code: Basic instruction only
   See ARM Arm Issue K.a, C3.1.10 for the complete list of instructions
    - First part: Add PAC to a register or SP, and and return the value in a
    general purpose register
*)
  (* see ARM Arm Issue K.a, C6.2.266
   * PACIA <Xd>, <Xn|Sp>
   * PACIZA <Xd>, <X31>
   * PACIASP <X30>, <Sp>
   * PACIAZ <X30>, <X31>
   * PACIA1716 <X17>, <X16>
   *
   * see ARM Arm Issue K.a, C6.2.267
   * PACIB <Xd>, <Xn|Sp>
   * PACIZA <Xd>, <X31>
   * PACIBSP <X30>, <Sp>
   * PACIBZ <X30>, <X31>
   * PACIB1716 <X17>, <X16>
   *
   * see ARM Arm Issue K.a, C6.2.263
   * PACDA <Xd>, <Xn|Sp>
   * PACDZA <Xd>, <X31>
   *
   * see ARM Arm Issue K.a, C6.2.264
   * PACDB <Xd>, <Xn|Sp>
   * PACDZB <Xd>, <X31>
   *)
  | I_PAC of PAC.key * reg * reg     (* destination <- AddPACIA(source) *)

(*  - Second part: check the PAC of a register *)
  (* see ARM Arm Issue K.a, C6.2.23
   * AUTIA <Xd>, <Xn|Sp>
   * AUTIZA <Xd>, <X31>
   * AUTIASP <X30>, <Sp>
   * AUTIAZ <X30>, <X31>
   * AUTIA1716 <X17>, <X16>
   *
   * see ARM Arm Issue K.a, C6.2.24
   * AUTIB <Xd>, <Xn|Sp>
   * AUTIZB <Xd>, <X31>
   * AUTIBSP <X30>, <Sp>
   * AUTIBZ <X30>, <X31>
   * AUTIB1716 <X17>, <X16>
   *
   * see ARM Arm Issue K.a, C6.2.21
   * AUTDA <Xd>, <Xn|Sp>
   * AUTDZA <Xd>, <X31>
   *
   * see ARM Arm Issue K.a, C6.2.22
   * AUTDB <Xd>, <Xn|Sp>
   * AUTDZB <Xd>, <X31>
   *)
  | I_AUT of PAC.key * reg * reg (* destination <- AuthIA(source) *)

(*  - Third part: strip the PAC of a register *)
  (* | I_XPACLRI (* strip a PAC from LR *) *)
  | I_XPACI of reg (* strip an instruction address PAC *)
  | I_XPACD of reg (* strip a data address PAC *)

type instruction = int kinstruction
type parsedInstruction = MetaConst.k kinstruction

let nop = Some I_NOP
let mk_imm_branch off = Some (I_B (BranchTarget.Offset off)) 
let is_nop = function
  | I_NOP -> true
  | _ -> false

let pp_memo memo = memo

let pp_cond = function
  | EQ -> "EQ"
  | NE -> "NE"
  | CS -> "CS"
  | CC -> "CC"
  | MI -> "MI"
  | PL -> "PL"
  | VS -> "VS"
  | VC -> "VC"
  | HI -> "HI"
  | LS -> "LS"
  | GE -> "GE"
  | LT -> "LT"
  | GT -> "GT"
  | LE -> "LE"
  | AL -> "AL"

let pp_pattern = function
  | POW2 -> "POW2"
  | VL1 -> "VL1"
  | VL2 -> "VL2"
  | VL3 -> "VL3"
  | VL4 -> "VL4"
  | VL5 -> "VL5"
  | VL6 -> "VL6"
  | VL7 -> "VL7"
  | VL8 -> "VL8"
  | VL16 -> "VL16"
  | VL32 -> "VL32"
  | VL64 -> "VL64"
  | VL128 -> "VL128"
  | VL256 -> "VL256"
  | MUL4 -> "MUL4"
  | MUL3 -> "MUL3"
  | ALL -> "ALL"

let pp_pattern_no_all = function
| ALL -> ""
| pat -> "," ^ pp_pattern pat

let pp_pattern_scaled m pat k =
  if m.onep k then pp_pattern_no_all pat
  else
    sprintf ",%s,MUL %s"
      (pp_pattern pat)
      (m.pp_k k)

let pp_vsimdreg v r = match v with
| VSIMD8 -> pp_simd_scalar_reg bvrs r
| VSIMD16 -> pp_simd_scalar_reg hvrs r
| VSIMD32 -> pp_simd_scalar_reg svrs r
| VSIMD64 -> pp_simd_scalar_reg dvrs r
| VSIMD128 -> pp_simd_scalar_reg qvrs r

let pp_simd_variant v = match v with
| VSIMD8 -> "B"
| VSIMD16 -> "H"
| VSIMD32 -> "W"
| VSIMD64 -> "D"
| VSIMD128 -> "Q"

let pp_cnt_inc_op_base = function
| CNT -> "CNT"
| INC -> "INC"

let pp_cnt_inc_op (op,v) =
  pp_cnt_inc_op_base op ^ pp_simd_variant v

let pp_op = function
  | ADD  -> "ADD"
  | ADDS -> "ADDS"
  | EOR  -> "EOR"
  | EON  -> "EON"
  | ORR  -> "ORR"
  | ORN  -> "ORN"
  | SUB  -> "SUB"
  | SUBS -> "SUBS"
  | AND  -> "AND"
  | ANDS -> "ANDS"
  | ASR  -> "ASR"
  | LSR  -> "LSR"
  | LSL  -> "LSL"
  | ROR  -> "ROR"
  | BICS -> "BICS"
  | BIC -> "BIC"

let pp_sc = function
  | CLRPERM -> "CLRPERM"
  | CTHI -> "CTHI"
  | SCFLGS -> "SCFLGS"
  | SCTAG -> "SCTAG"
  | SCVALUE -> "SCVALUE"

let pp_gc = function
  | CFHI -> "CFHI"
  | GCFLGS -> "GCFLGS"
  | GCPERM -> "GCPERM"
  | GCSEAL -> "GCSEAL"
  | GCTAG -> "GCTAG"
  | GCTYPE -> "GCTYPE"
  | GCVALUE -> "GCVALUE"

module MakePP(C:sig val is_morello : bool end) = struct

let do_pp_instruction m =
  let pp_rrr memo v rt rn rm =
    pp_memo memo ^ " " ^ pp_vreg v rt ^ "," ^
    pp_vreg v rn ^ "," ^ pp_vreg v  rm
  and pp_ri memo v r k =
    pp_memo memo ^ " " ^ pp_vreg v r ^ "," ^  m.pp_k k
  and pp_rr memo v r1 r2 =
    pp_memo memo ^ " " ^ pp_vreg v r1 ^ "," ^  pp_vreg v r2
  and pp_vrivri memo r1 i1 r2 i2 =
    pp_memo memo ^ " " ^ pp_simd_vector_reg r1 ^ "[" ^ string_of_int i1 ^"]," ^
    pp_simd_vector_reg r2 ^ "[" ^ string_of_int i2 ^ "]"
  and pp_vrir memo r1 i v r2 =
    pp_memo memo ^ " " ^ pp_simd_vector_reg r1 ^ "[" ^ string_of_int i ^ "]," ^
    pp_vreg v r2
  and pp_vri memo r i =
    pp_memo memo ^ " " ^ pp_simd_vector_reg r ^ "," ^ m.pp_k i
  and pp_rvri memo v r1 r2 i =
    pp_memo memo ^ " " ^ pp_vreg v r1 ^ "," ^
    pp_simd_vector_reg r2 ^ "[" ^ string_of_int i ^ "]"
  and pp_vrvr memo r1 r2 =
    pp_memo memo ^ " " ^ pp_simd_vector_reg r1 ^ "," ^ pp_simd_vector_reg r2
  and pp_sri memo v r i =
    pp_memo memo ^ " " ^ pp_vsimdreg v r ^ "," ^ m.pp_k i
  and pp_srvri memo v r1 r2 i =
    pp_memo memo ^ " " ^ pp_vsimdreg v r1 ^ "," ^
    pp_simd_vector_reg r2 ^ "[" ^ string_of_int i ^ "]"
  and pp_simd_rrr memo r1 r2 r3 =
    pp_memo memo ^ " " ^ pp_simd_vector_reg r1 ^ "," ^ pp_simd_vector_reg r2
    ^ "," ^ pp_simd_vector_reg r3
  and pp_simd_srrr memo r1 r2 r3 =
    pp_memo memo ^ " " ^ pp_vsimdreg VSIMD64 r1 ^ "," ^ pp_vsimdreg VSIMD64 r2
    ^ "," ^ pp_vsimdreg VSIMD64 r3 in

  let pp_op2 memo v r e =
    sprintf "%s %s,%s" memo (pp_vreg v r) (OpExt.pp_ext m v e)

  and pp_op3 memo v r1 r2 e =
    sprintf "%s %s,%s,%s"
      memo (pp_vreg v r1) (pp_vreg v r2) (OpExt.pp_ext m v e)
  in


  let pp_kr showsxtw showzero kr = match kr with
  | K k when m.zerop k && not showzero -> ""
  | K k -> "," ^ m.pp_k k
  | RV (v,r) ->
      "," ^ pp_vreg v r ^
      (match v with V32 when showsxtw -> ",SXTW" | V32|V64 -> "" | V128 -> assert false) in


  let pp_ra r = if C.is_morello then pp_creg r else pp_xreg r in

  let do_pp_idx from_pair ra (k,idx) =
    match idx with
    | Idx when  m.zerop k ->
       sprintf "[%s]" (pp_ra ra)
    | Idx ->
       sprintf "[%s,%s]" (pp_xreg ra) (m.pp_k k)
    | PostIdx ->
       let pp =
         if m.compat then begin
             if from_pair then
               sprintf " [%s]%s"
             else
               sprintf "[%s]%s"
           end else
           sprintf "[%s],%s" in
       pp (pp_xreg ra) (m.pp_k k)
    | PreIdx ->
       sprintf "[%s,%s]!" (pp_xreg ra) (m.pp_k k) in

  let pp_idx = do_pp_idx false in

  let pp_mem_idx memo v rt ra idx =
    Printf.sprintf "%s %s,%s" memo (pp_vreg v rt) (pp_idx ra idx) in

  let pp_addr ra =
    let open MemExt in
    function
    | Imm idx -> pp_idx ra idx
    | Reg (v,r,LSL,k) when m.zerop k ->
       sprintf "[%s,%s]" (pp_xreg ra) (pp_vreg v r)
    | Reg (v,r,(UXTW|SXTW|SXTX as ext),k) when m.zerop k->
       sprintf "[%s,%s,%s]" (pp_xreg ra) (pp_vreg v r) (pp_sext ext)
    | Reg (v,r,ext,k) ->
       sprintf "[%s,%s,%s %s]" (pp_xreg ra) (pp_vreg v r) (pp_sext ext) (m.pp_k k)
    | ZReg (r,LSL,k) when m.zerop k ->
       sprintf "[%s,%s]" (pp_xreg ra) (pp_zreg r)
    | ZReg (r,(UXTW|SXTW|SXTX as ext),k) when m.zerop k->
       sprintf "[%s,%s,%s]" (pp_xreg ra) (pp_zreg r) (pp_sext ext)
    | ZReg (r,ext,k) ->
       sprintf "[%s,%s,%s %s]" (pp_xreg ra) (pp_zreg r) (pp_sext ext) (m.pp_k k) in

  let pp_mem_ext memo v rt ra idx =
    Printf.sprintf "%s %s,%s" memo (pp_vreg v rt) (pp_addr ra idx) in

  let pp_mem memo v rt ra kr =
    let pp_addr = if C.is_morello then pp_creg else pp_xreg in
    pp_memo memo ^ " " ^ pp_vreg v rt ^
    ",[" ^ pp_addr ra ^ pp_kr true false kr ^ "]" in

  let pp_memp memo v r1 r2 ra idx =
    pp_memo memo ^ " " ^
    pp_vreg v r1 ^ "," ^
    pp_vreg v r2 ^ "," ^
    do_pp_idx true ra idx in

  let pp_smem memo v rt ra idx =
    pp_memo memo ^ " " ^ pp_vsimdreg v rt ^
    "," ^ pp_addr ra idx in

  let pp_smemp memo v r1 r2 ra idx =
    pp_memo memo ^ " " ^
    pp_vsimdreg v r1 ^ "," ^
    pp_vsimdreg v r2 ^ "," ^
    pp_idx ra idx in

  let pp_vmem_shift memo r k s =
    pp_memo memo ^ " " ^ pp_simd_vector_reg r ^ "," ^ m.pp_k k ^
    pp_barrel_shift "," s (m.pp_k) in

  let pp_vmem_s memo rs i r2 kr =
    pp_memo memo ^ " " ^
    "{" ^ String.concat ", " (List.map pp_simd_vector_reg rs) ^ "}" ^
    "[" ^ string_of_int i ^ "]" ^
    ",[" ^ pp_xreg r2 ^ "]" ^
    pp_kr false false kr in

  let pp_vmem_r_m memo rs r2 kr =
    pp_memo memo ^ " " ^
    "{" ^ String.concat ", " (List.map pp_simd_vector_reg rs) ^ "}" ^
    ",[" ^ pp_xreg r2 ^ "]" ^
    pp_kr false false kr in

  let pp_rkr memo v r1 kr = match v,kr with
  | _, K k -> pp_ri memo v r1 k
  | V32, RV (V32,r2)
  | V64, RV (V64,r2)
  | V128,RV (V128,r2) ->
      pp_rr memo v r1 r2
  | V32,RV ((V64|V128),_)
  | V64,RV ((V32|V128),_)
  | V128,RV ((V32|V64),_) -> assert false in

  let pp_stxr memo v r1 r2 r3 =
    pp_memo memo ^ " " ^
    pp_wreg r1 ^"," ^
    pp_vreg v r2 ^ ",[" ^
    pp_xreg r3 ^ "]" in

  let pp_ldxp memo v r1 r2 r3 =
    pp_memo memo ^ " "
    ^ (if m.compat then pp_wreg r1 else pp_vreg v r1) ^","
    ^ pp_vreg v r2 ^ ",["
    ^ pp_xreg r3 ^ "]" in

  let pp_stxp memo v r1 r2 r3 r4 =
    pp_memo memo ^ " "
    ^ pp_wreg r1 ^","
    ^ pp_vreg v r2 ^ ","
    ^ pp_vreg v r3 ^ ",["
    ^ pp_xreg r4 ^ "]" in

  let pp_cnt_inc op r pat k =
    sprintf "%s %s%s"
      (pp_cnt_inc_op op)
      (pp_xreg r)
      (pp_pattern_scaled m pat k) in

  fun i -> match i with
  | I_NOP -> "NOP"
(* Branches *)
  | I_B lbl ->
      sprintf "B %s" (pp_label lbl)
  | I_BR r ->
      sprintf "BR %s" (pp_xreg r)
  | I_BC (cond,lbl) ->
      sprintf "B.%s %s" (pp_cond cond) (pp_label lbl)
  | I_CBZ (v,r,lbl) ->
      sprintf "CBZ %s,%s" (pp_vreg v r) (pp_label lbl)
  | I_CBNZ (v,r,lbl) ->
      sprintf "CBNZ %s,%s" (pp_vreg v r) (pp_label lbl)
  | I_TBNZ (v,r, k, lbl) ->
      sprintf "TBNZ %s,%s,%s" (pp_vreg v r) (m.pp_k k) (pp_label lbl)
  | I_TBZ (v,r, k, lbl) ->
      sprintf "TBZ %s,%s,%s" (pp_vreg v r) (m.pp_k k) (pp_label lbl)
  | I_BL lbl ->
      sprintf "BL %s" (pp_label lbl)
  | I_BLR r ->
      sprintf "BLR %s" (pp_xreg r)
  | I_RET None->
      "RET"
  | I_RET (Some r) ->
      sprintf "RET %s" (pp_xreg r)
  | I_ERET ->
     "ERET"
  | I_SVC k ->
    sprintf "SVC %s" (m.pp_k k)

(* Load and Store *)
  | I_LDR (v,r1,r2,idx) ->
      pp_mem_ext "LDR" v r1 r2 idx
  | I_LDRSW (r1,r2,idx) ->
      pp_mem_ext "LDRSW" V64 r1 r2 idx
  | I_LDRS ((v,bh),r1,r2,idx) ->
     pp_mem_ext (ldrs_memo bh) v r1 r2 idx
  | I_LDUR (_,r1,r2,k) ->
      sprintf "LDUR %s, [%s%s]" (pp_reg r1) (pp_reg r2) (pp_kr false false (K k))
  | I_LDP (t,v,r1,r2,r3,idx) ->
      pp_memp (ldp_memo t) v r1 r2 r3 idx
  | I_LDPSW (r1,r2,r3,idx) ->
      pp_memp "LDPSW" V64 r1 r2 r3 idx
  | I_STP (t,v,r1,r2,r3,idx) ->
      pp_memp (stp_memo t) v r1 r2 r3 idx
  | I_LDAR (v,t,r1,r2) ->
      pp_mem (ldr_memo t) v r1 r2 m.k0
  | I_LDARBH (bh,t,r1,r2) ->
      pp_mem (ldrbh_memo bh t)  V32 r1 r2 m.k0
  | I_LDXP (v,t,r1,r2,r3) ->
      pp_ldxp (ldxp_memo t) v r1 r2 r3
  | I_STR (v,r1,r2,idx) ->
      pp_mem_ext "STR" v r1 r2 idx
  | I_STLR (v,r1,r2) ->
      pp_mem "STLR" v r1 r2 m.k0
  | I_STXR (v,t,r1,r2,r3) ->
      pp_stxr (str_memo t) v r1 r2 r3
  | I_STXP (v,t,r1,r2,r3,r4) ->
     pp_stxp (stxp_memo t) v r1 r2 r3 r4
  | I_LDRBH (bh,r1,r2,idx) ->
      pp_mem_ext ("LDR"^pp_bh bh) V32 r1 r2 idx
  | I_STRBH (bh,r1,r2,idx) ->
      pp_mem_ext ("STR"^pp_bh bh) V32 r1 r2 idx
  | I_STLRBH (bh,r1,r2) ->
      pp_mem ("STLR"^pp_bh bh) V32 r1 r2 m.k0
  | I_STXRBH (bh,t,r1,r2,r3) ->
      pp_stxr (strbh_memo bh t) V32 r1 r2 r3
(* Neon Extension Load and Store *)
  | I_LD1 (rs,i,r2,kr) ->
      pp_vmem_s "LD1" rs i r2 kr
  | I_LDAP1 (rs,i,r2,kr) ->
      pp_vmem_s "LDAP1" rs i r2 kr
  | I_LD1M (rs,r2,kr) ->
      pp_vmem_r_m "LD1" rs r2 kr
  | I_LD1R (rs, r2, kr) ->
      pp_vmem_r_m "LD1R" rs r2 kr
  | I_LD2 (rs,i,r2,kr) ->
      pp_vmem_s "LD2" rs i r2 kr
  | I_LD2M (rs,r2,kr) ->
      pp_vmem_r_m "LD2" rs r2 kr
  | I_LD2R (r1,r2,kr) ->
      pp_vmem_r_m "LD2R" r1 r2 kr
  | I_LD3 (rs,i,r2,kr) ->
      pp_vmem_s "LD3" rs i r2 kr
  | I_LD3M (rs,r2,kr) ->
      pp_vmem_r_m "LD3" rs r2 kr
  | I_LD3R (rs, r2, kr) ->
      pp_vmem_r_m "LD3R" rs r2 kr
  | I_LD4 (rs,i,r2,kr) ->
      pp_vmem_s "LD4" rs i r2 kr
  | I_LD4M (rs,r2,kr) ->
      pp_vmem_r_m "LD4" rs r2 kr
  | I_LD4R (rs,r2,kr) ->
      pp_vmem_r_m "LD4R" rs r2 kr
  | I_ST1 (rs,i,r2,kr) ->
      pp_vmem_s "ST1" rs i r2 kr
  | I_STL1 (rs,i,r2,kr) ->
      pp_vmem_s "STL1" rs i r2 kr
  | I_ST1M (rs,r2,kr) ->
      pp_vmem_r_m "ST1" rs r2 kr
  | I_ST2 (rs,i,r2,kr) ->
      pp_vmem_s "ST2" rs i r2 kr
  | I_ST2M (rs,r2,kr) ->
      pp_vmem_r_m "ST2" rs r2 kr
  | I_ST3 (rs,i,r2,kr) ->
      pp_vmem_s "ST3" rs i r2 kr
  | I_ST3M (rs,r2,kr) ->
      pp_vmem_r_m "ST3" rs r2 kr
  | I_ST4 (rs,i,r2,kr) ->
      pp_vmem_s "ST4" rs i r2 kr
  | I_ST4M (rs,r2,kr) ->
      pp_vmem_r_m "ST4" rs r2 kr
  | I_LDP_SIMD (t,v,r1,r2,r3,idx) ->
      pp_smemp (match t with TT -> "LDP" | NT -> "LDNP") v r1 r2 r3 idx
  | I_STP_SIMD (t,v,r1,r2,r3,idx) ->
      pp_smemp (match t with TT -> "STP" | NT -> "STNP") v r1 r2 r3 idx
  | I_LDR_SIMD (v,r1,r2,idx) ->
      pp_smem "LDR" v r1 r2 idx
  | I_STR_SIMD (v,r1,r2,idx) ->
      pp_smem "STR" v r1 r2 idx
  | I_LDAPUR_SIMD (v,r1,r2,k) ->
      sprintf "LDAPUR %s,[%s%s]" (pp_vsimdreg v r1) (pp_reg r2) (pp_kr false false (K k))
  | I_LDUR_SIMD (v,r1,r2,k) ->
      sprintf "LDUR %s,[%s%s]" (pp_vsimdreg v r1) (pp_reg r2) (pp_kr false false (K k))
  | I_STUR_SIMD (v,r1,r2,k) ->
      sprintf "STUR %s,[%s%s]" (pp_vsimdreg v r1) (pp_reg r2) (pp_kr false false (K k))
  | I_STLUR_SIMD (v,r1,r2,k) ->
      sprintf "STLUR %s,[%s%s]" (pp_vsimdreg v r1) (pp_reg r2) (pp_kr false false (K k))
  | I_ADDV (v,r1,r2) ->
      sprintf "ADDV %s,%s" (pp_vsimdreg v r1) (pp_simd_vector_reg r2)
  | I_DUP (r1,v,r2) ->
      sprintf "DUP %s,%s" (pp_simd_vector_reg r1) (pp_vreg v r2)
  | I_FMOV_TG (v1,r1,v2,r2) ->
      sprintf "FMOV %s,%s" (pp_vreg v1 r1) (pp_vsimdreg v2 r2)
  | I_MOV_VE (r1,i1,r2,i2) ->
      pp_vrivri "MOV" r1 i1 r2 i2
  | I_MOV_V (r1,r2) ->
      pp_vrvr "MOV" r1 r2
  | I_MOV_TG (v,r1,r2,i) ->
      pp_rvri "MOV" v r1 r2 i
  | I_MOV_FG (r1,i,v,r2) ->
      pp_vrir "MOV" r1 i v r2
  | I_MOV_S (v,r1,r2,i) ->
      pp_srvri "MOV" v r1 r2 i
  | I_MOVI_V (r,k,S_NOEXT) ->
      pp_vri "MOVI" r k
  | I_MOVI_V (r,k,s) ->
      pp_vmem_shift "MOVI" r k s
  | I_MOVI_S (v,r,k) ->
      pp_sri "MOVI" v r k
  | I_OP3_SIMD (op,r1,r2,r3) ->
      pp_simd_rrr (pp_op op) r1 r2 r3
  | I_ADD_SIMD (r1,r2,r3) ->
      pp_simd_rrr "ADD" r1 r2 r3
  | I_ADD_SIMD_S (r1,r2,r3) ->
      pp_simd_srrr "ADD" r1 r2 r3
(* Scalable Vector Extention *)
  | I_PTRUE (predicate,pattern) ->
      sprintf "PTRUE %s,%s" (pp_preg predicate) (pp_pattern pattern)
  | I_WHILELT (p1,v,r2,r3) ->
      sprintf "WHILELT %s,%s,%s" (pp_preg p1) (pp_vreg v r2) (pp_vreg v r3)
  | I_WHILELE (p1,v,r2,r3) ->
      sprintf "WHILELE %s,%s,%s" (pp_preg p1) (pp_vreg v r2) (pp_vreg v r3)
  | I_WHILELO (p1,v,r2,r3) ->
      sprintf "WHILELO %s,%s,%s" (pp_preg p1) (pp_vreg v r2) (pp_vreg v r3)
  | I_WHILELS (p1,v,r2,r3) ->
      sprintf "WHILELS %s,%s,%s" (pp_preg p1) (pp_vreg v r2) (pp_vreg v r3)
  | I_UADDV (v,r1,r2,r3) ->
      sprintf "UADDV %s,%s,%s" (pp_vsimdreg v r1) (pp_preg_simple r2) (pp_zreg r3)
  | I_LD1SP (v,rs,r2,r3,idx) ->
      sprintf "LD1%s {%s},%s,%s" (pp_simd_variant v) (String.concat "," (List.map pp_zreg rs)) (pp_preg r2) (pp_addr r3 idx)
  | I_LD2SP (v,rs,r2,r3,idx) ->
      sprintf "LD2%s {%s},%s,%s" (pp_simd_variant v) (String.concat "," (List.map pp_zreg rs)) (pp_preg r2) (pp_addr r3 idx)
  | I_LD3SP (v,rs,r2,r3,idx) ->
      sprintf "LD3%s {%s},%s,%s" (pp_simd_variant v) (String.concat "," (List.map pp_zreg rs)) (pp_preg r2) (pp_addr r3 idx)
  | I_LD4SP (v,rs,r2,r3,idx) ->
      sprintf "LD4%s {%s},%s,%s" (pp_simd_variant v) (String.concat "," (List.map pp_zreg rs)) (pp_preg r2) (pp_addr r3 idx)
  | I_ST1SP (v,rs,r2,r3,idx) ->
      sprintf "ST1%s {%s},%s,%s" (pp_simd_variant v) (String.concat "," (List.map pp_zreg rs)) (pp_preg_simple r2) (pp_addr r3 idx)
  | I_ST2SP (v,rs,r2,r3,idx) ->
      sprintf "ST2%s {%s},%s,%s" (pp_simd_variant v) (String.concat "," (List.map pp_zreg rs)) (pp_preg_simple r2) (pp_addr r3 idx)
  | I_ST3SP (v,rs,r2,r3,idx) ->
      sprintf "ST3%s {%s},%s,%s" (pp_simd_variant v) (String.concat "," (List.map pp_zreg rs)) (pp_preg_simple r2) (pp_addr r3 idx)
  | I_ST4SP (v,rs,r2,r3,idx) ->
      sprintf "ST4%s {%s},%s,%s" (pp_simd_variant v) (String.concat "," (List.map pp_zreg rs)) (pp_preg_simple r2) (pp_addr r3 idx)
  | I_MOV_SV (r,k,s) ->
      sprintf "MOV %s,%s%s" (pp_zreg r) (m.pp_k k) (pp_barrel_shift "," s (m.pp_k))
  | I_DUP_SV (r1,v,r2) ->
      sprintf "DUP %s,%s" (pp_zreg r1) (pp_vreg v r2)
  | I_ADD_SV (r1,r2,r3) ->
      sprintf "ADD %s,%s,%s" (pp_zreg r1) (pp_zreg r2) (pp_zreg r3)
  | I_NEG_SV (r1,r2,r3) ->
    sprintf "NEG %s,%s,%s" (pp_zreg r1) (pp_preg r2) (pp_zreg r3)
  | I_MOVPRFX (r1,r2,r3) ->
    sprintf "MOVPRFX %s,%s,%s" (pp_zreg r1) (pp_preg r2) (pp_zreg r3)
  | I_OP3_SV (op,r1,r2,r3) ->
    sprintf "%s %s,%s,%s" (pp_op op) (pp_zreg r1) (pp_zreg r2) (pp_zreg r3)
  | I_INDEX_SI (r1,v,r2,k) ->
      sprintf "INDEX %s,%s,%s" (pp_zreg r1) (pp_vreg v r2) (m.pp_k k)
  | I_INDEX_IS (r1,v,k,r2) ->
      sprintf "INDEX %s,%s,%s" (pp_zreg r1) (m.pp_k k) (pp_vreg v r2)
  | I_INDEX_SS (r1,v,r2,r3) ->
      sprintf "INDEX %s,%s,%s" (pp_zreg r1) (pp_vreg v r2) (pp_vreg v r3)
  | I_INDEX_II (r1,k1,k2) ->
      sprintf "INDEX %s,%s,%s" (pp_zreg r1) (m.pp_k k1) (m.pp_k k2)
  | I_RDVL (r1,k1) ->
      sprintf "RDVL %s,%s" (pp_xreg r1) (m.pp_k k1)
  | I_ADDVL (r1,r2,k1) ->
      sprintf "ADDVL %s,%s,%s" (pp_xreg r1) (pp_xreg r2) (m.pp_k k1)
  | I_CNT_INC_SVE (op,r,pat,k) ->
      pp_cnt_inc op r pat k
  | I_CTERM (cond,v,rn,rm) ->
      pp_rr (CTERM.pp cond) v rn rm
(* Scalable Matrix Extention *)
  | I_LD1SPT (v,r,ri,k,p,ra,idx) ->
      sprintf "LD1%s {%s[%s,%s]},%s,%s" (pp_simd_variant v) (pp_zareg r) (pp_wreg ri) (m.pp_k k) (pp_preg p) (pp_addr ra idx)
  | I_ST1SPT (v,r,ri,k,p,ra,idx) ->
      sprintf "ST1%s {%s[%s,%s]},%s,%s" (pp_simd_variant v) (pp_zareg r) (pp_wreg ri) (m.pp_k k) (pp_preg_simple p) (pp_addr ra idx)
  | I_MOVA_VT (r,ri,k,p,rs) ->
      sprintf "MOVA %s[%s,%s],%s,%s" (pp_zareg r) (pp_wreg ri) (m.pp_k k) (pp_preg p) (pp_zreg rs)
  | I_MOVA_TV (r,p,rs,ri,k) ->
      sprintf "MOVA %s,%s,%s[%s,%s]" (pp_zreg r) (pp_preg p) (pp_zareg rs) (pp_wreg ri) (m.pp_k k)
  | I_ADDA (s,r1,p1,p2,r2) ->
      sprintf "ADD%sA %s,%s,%s,%s" (pp_za_dirrection_specifier s) (pp_zareg r1) (pp_preg p1) (pp_preg p2) (pp_zreg r2)
  | I_SMSTART (None) ->
      "SMSTART"
  | I_SMSTART (Some(mode)) ->
      sprintf "SMSTART %s" (pp_sm mode)
  | I_SMSTOP (None) ->
      "SMSTOP"
  | I_SMSTOP (Some(mode)) ->
      sprintf "SMSTOP %s" (pp_sm mode)
(* Morello *)
  | I_ALIGND (r1,r2,k) ->
      sprintf "ALIGND %s,%s,%s" (pp_creg r1) (pp_creg r2) (m.pp_k k)
  | I_ALIGNU (r1,r2,k) ->
      sprintf "ALIGNU %s,%s,%s" (pp_creg r1) (pp_creg r2) (m.pp_k k)
  | I_BUILD (r1,r2,r3) ->
      sprintf "BUILD %s,%s,%s" (pp_creg r1) (pp_creg r2) (pp_creg r3)
  | I_CHKEQ (r1,r2) ->
      sprintf "CHKEQ %s,%s" (pp_creg r1) (pp_creg r2)
  | I_CHKSLD (r1) ->
      sprintf "CHKSLD %s" (pp_creg r1)
  | I_CHKTGD (r1) ->
      sprintf "CHKTGD %s" (pp_creg r1)
  | I_CLRTAG (r1,r2) ->
      sprintf "CLRTAG %s,%s" (pp_creg r1) (pp_creg r2)
  | I_CPYTYPE (r1,r2,r3) ->
      sprintf "CPYTYPE %s,%s,%s" (pp_creg r1) (pp_creg r2) (pp_creg r3)
  | I_CPYVALUE (r1,r2,r3) ->
      sprintf "CPYVALUE %s,%s,%s" (pp_creg r1) (pp_creg r2) (pp_creg r3)
  | I_CSEAL (r1,r2,r3) ->
      sprintf "CSEAL %s,%s,%s" (pp_creg r1) (pp_creg r2) (pp_creg r3)
  | I_GC (op,r1,r2) ->
      sprintf "%s %s,%s" (pp_gc op) (pp_xreg r1) (pp_creg r2)
  | I_LDCT (r1,r2) ->
      sprintf "LDCT %s,[%s]" (pp_xreg r1) (pp_xreg r2)
  | I_SC (op,r1,r2,r3) ->
      sprintf "%s %s,%s,%s" (pp_sc op) (pp_creg r1) (pp_creg r2) (pp_xreg r3)
  | I_SEAL (r1,r2,r3) ->
      sprintf "SEAL %s,%s,%s" (pp_creg r1) (pp_creg r2) (pp_creg r3)
  | I_STCT (r1,r2) ->
      sprintf "STCT %s,[%s]" (pp_xreg r1) (pp_xreg r2)
  | I_UNSEAL (r1,r2,r3) ->
      sprintf "UNSEAL %s,%s,%s" (pp_creg r1) (pp_creg r2) (pp_creg r3)
(* Guarded Control Stack *)
  | I_GCSPOPM (ZR) ->
      "GCSPOPM"
  | I_GCSPOPM (r) ->
      sprintf "GCSPOPM %s" (pp_xreg r)
  | I_GCSPUSHM (r) ->
      sprintf "GCSPUSHM %s" (pp_xreg r)
  | I_GCSSTR (r1,r2) ->
      sprintf "GCSSTR %s,[%s]" (pp_xreg r1) (pp_xreg r2)
  | I_GCSSS1 (r) ->
      sprintf "GCSSS1 %s" (pp_xreg r)
  | I_GCSSS2 (r) ->
      sprintf "GCSSS2 %s" (pp_xreg r)
(* CAS *)
  | I_CAS (v,rmw,r1,r2,r3) ->
      sprintf "%s %s,%s,[%s]" (cas_memo rmw) (pp_vreg v r1) (pp_vreg v r2) (pp_xreg r3)
  | I_CASBH (bh,rmw,r1,r2,r3) ->
      sprintf "%s %s,%s,[%s]" (casbh_memo bh rmw) (pp_wreg r1) (pp_wreg r2) (pp_xreg r3)
  | I_CASP (v,rmw,r1,r2,r3,r4,r5) ->
      sprintf "%s %s,%s,%s,%s,[%s]" (casp_memo rmw) (pp_vreg v r1) (pp_vreg v r2) (pp_vreg v r3) (pp_vreg v r4) (pp_xreg r5)
(* SWP *)
  | I_SWP (v,rmw,r1,r2,r3) ->
      sprintf "%s %s,%s,[%s]" (swp_memo rmw) (pp_vreg v r1) (pp_vreg v r2) (pp_xreg r3)
  | I_SWPBH (bh,rmw,r1,r2,r3) ->
      sprintf "%s %s,%s,[%s]" (swpbh_memo bh rmw) (pp_wreg r1) (pp_wreg r2) (pp_xreg r3)
(* Fecth and Op *)
  | I_LDOP (op,v,(RMW_P|RMW_L as rmw),r1,ZR,r2) ->
     if m.compat then
       sprintf "%s %s,%s,[%s]"
        (ldop_memo op rmw) (pp_vreg v r1) (pp_vreg v ZR) (pp_xreg r2)
     else
       sprintf "%s %s,[%s]"
         (stop_memo op (rmw_to_w rmw)) (pp_vreg v r1) (pp_xreg r2)
  | I_LDOP (op,v,rmw,r1,r2,r3) ->
      sprintf "%s %s,%s,[%s]"
        (ldop_memo op rmw) (pp_vreg v r1) (pp_vreg v r2) (pp_xreg r3)
  | I_LDOPBH (op,v,(RMW_P|RMW_L as rmw),r1,ZR,r2) ->
     if m.compat then
       sprintf "%s %s,%s,[%s]"
         (ldopbh_memo op v rmw) (pp_wreg r1) (pp_wreg ZR) (pp_xreg r2)
     else
      sprintf "%s %s,[%s]"
        (stopbh_memo op v (rmw_to_w rmw)) (pp_wreg r1) (pp_xreg r2)
  | I_LDOPBH (op,v,rmw,r1,r2,r3) ->
      sprintf "%s %s,%s,[%s]"
        (ldopbh_memo op v rmw) (pp_wreg r1) (pp_wreg r2) (pp_xreg r3)
  | I_STOP (op,v,rmw,r1,r2) ->
      sprintf "%s %s,[%s]"
        (stop_memo op rmw) (pp_vreg v r1) (pp_xreg r2)
  | I_STOPBH (op,v,rmw,r1,r2) ->
      sprintf "%s %s,[%s]"
        (stopbh_memo op v rmw) (pp_wreg r1) (pp_xreg r2)
(* Operations *)
  | I_MOV (v,r,kr) ->
      pp_rkr "MOV" v r kr
  | I_MOVZ (v,r,k,S_NOEXT) ->
      sprintf "MOVZ %s,%s" (pp_vreg v r) (m.pp_k k)
  | I_MOVZ (v,r,k,s) ->
      sprintf "MOVZ %s,%s,%s"
        (pp_vreg v r)
        (m.pp_k k)
        (pp_barrel_shift "," s (m.pp_k))
  | I_MOVN (v,r,k,S_NOEXT) ->
      sprintf "MOVN %s,%s" (pp_vreg v r) (m.pp_k k)
  | I_MOVN (v,r,k,s) ->
      sprintf "MOVN %s,%s,%s"
        (pp_vreg v r)
        (m.pp_k k)
        (pp_barrel_shift "," s (m.pp_k))
  | I_MOVK (v,r,k,S_NOEXT) ->
      sprintf "MOVK %s,%s" (pp_vreg v r) (m.pp_k k)
  | I_MOVK (v,r,k,s) ->
      sprintf "MOVK %s,%s,%s"
        (pp_vreg v r)
        (m.pp_k k)
        (pp_barrel_shift "," s (m.pp_k))
  | I_SXTW (r1,r2) ->
      sprintf "SXTW %s,%s" (pp_xreg r1) (pp_wreg r2)
  | I_UBFM (_,r1,r2,k1,k2) ->
      sprintf "UBFM %s,%s,%s,%s" (pp_reg r1) (pp_reg r2) (m.pp_k k1) (m.pp_k k2)
  | I_SBFM (_,r1,r2,k1,k2) ->
      sprintf "SBFM %s,%s,%s,%s" (pp_reg r1) (pp_reg r2) (m.pp_k k1) (m.pp_k k2)
  | I_ADDSUBEXT (v1,op,r1,r2,(v3,r3),ext) ->
     sprintf "%s %s,%s,%s,%s"
       (Ext.pp_op op)
       (pp_vreg v1 r1)
       (pp_vreg v1 r2)
       (pp_vreg v3 r3)
       (Ext.pp_ext m ext)
  | I_MOPL (sop,rd,rn,rm,ZR) ->
     sprintf "%s %s,%s,%s"
       (MOPLExt.memo_z sop)
       (pp_xreg rd) (pp_wreg rn) (pp_wreg rm)
  | I_MOPL (sop,rd,rn,rm,ra) ->
     sprintf "%s %s,%s,%s,%s"
       (MOPLExt.memo sop)
       (pp_xreg rd) (pp_wreg rn) (pp_wreg rm) (pp_xreg ra)
  | I_MOP (op, v, rd, rn, rm, ZR) ->
      sprintf "%s %s,%s,%s"
      (MOPExt.memo_z op)
      (pp_vreg v rd) (pp_vreg v rn) (pp_vreg v rm)
  | I_MOP (op, v, rd, rn, rm, ra) ->
      sprintf "%s %s,%s,%s,%s"
      (MOPExt.memo op)
      (pp_vreg v rd) (pp_vreg v rn) (pp_vreg v rm) (pp_vreg v ra)
  | I_OP3 (v,SUBS,ZR,r,e) ->
     pp_op2 "CMP" v r e
  | I_OP3 (v,SUB,r,ZR,(OpExt.Reg _ as e)) when not m.compat ->
     pp_op2 "NEG" v r e
  | I_OP3 (v,SUBS,r,ZR,(OpExt.Reg _ as e)) when not m.compat ->
     pp_op2 "NEGS" v r e
  | I_OP3 (v,ANDS,ZR,r,e) ->
      pp_op2 "TST" v r e
  | I_OP3 (v,ORN,r,ZR,e) ->
      pp_op2 "MVN" v r e
  | I_OP3 (v,op,r1,r2,e) ->
      pp_op3 (pp_op op) v r1 r2 e
  | I_ADR (r,lbl) ->
     sprintf "%s %s,%s"
       (if m.compat then "ADDR" else "ADR")
       (pp_xreg r) (pp_label lbl)
  | I_RBIT (v,rd,rs) ->
      sprintf "RBIT %s,%s" (pp_vreg v rd) (pp_vreg v rs)
  | I_ABS (v,rd,rs) ->
      sprintf "ABS %s,%s" (pp_vreg v rd) (pp_vreg v rs)
  | I_REV (rv,rd,rs) ->
     let memo = memo_of_rev rv
     and v = variant_of_rev rv in
     sprintf "%s %s,%s" memo (pp_vreg v rd) (pp_vreg v rs)
  | I_EXTR (v,rd,rn,rm,k) ->
     sprintf "EXTR %s,%s,%s,%s"
       (pp_vreg v rd)  (pp_vreg v rn) (pp_vreg v rm)
       (m.pp_k k)
(* Barrier *)
  | I_FENCE b ->
      pp_barrier b
(* Conditional select *)
  | I_CSEL (v,r1,ZR,ZR,c,Inc) ->
      sprintf "CSET %s,%s" (pp_vreg v r1)  (pp_cond (inverse_cond c))
  | I_CSEL (v,r1,ZR,ZR,c,Inv) ->
      sprintf "CSETM %s,%s" (pp_vreg v r1)  (pp_cond (inverse_cond c))
  | I_CSEL (v,r1,r2,r3,c,Inc) when r2=r3 ->
     sprintf "CINC %s,%s,%s"
       (pp_vreg v r1) (pp_vreg v r2) (pp_cond (inverse_cond c))
  | I_CSEL (v,r1,r2,r3,c,op) ->
      pp_rrr (sel_memo op) v r1 r2 r3 ^ "," ^ pp_cond c
(* Cache maintenance *)
  | I_IC (op,r) ->
      sprintf "IC %s,%s" (IC.pp_op op) (pp_xreg r)
  | I_DC (op,r) ->
      sprintf "DC %s,%s" (DC.pp_op op) (pp_xreg r)
  | I_TLBI (op,ZR)->
      sprintf "TLBI %s" (TLBI.pp_op op)
  | I_TLBI (op,r)->
      sprintf "TLBI %s,%s" (TLBI.pp_op op) (pp_xreg r)
  | I_AT (op, r) ->
      sprintf "AT %s, %s" (AT.pp_op op) (pp_xreg r)
(* Read System register *)
  | I_MRS (r,sr) ->
      sprintf "MRS %s,%s" (pp_xreg r) (pp_sysreg sr)
  (* Read System register *)
  | I_MSR (sr,r) ->
     sprintf "MSR %s,%s" (pp_sysreg sr) (pp_xreg r)
(* Memory Tagging *)
  | I_STG (rt,rn,idx) ->
      pp_mem_idx  "STG" V64 rt rn idx
  | I_ST2G (rt,rn,idx) ->
      pp_mem_idx  "ST2G" V64 rt rn idx
  | I_STZG (rt,rn,idx) ->
      pp_mem_idx "STZG" V64 rt rn idx
  | I_STZ2G (rt,rn,idx) ->
      pp_mem_idx "STZ2G" V64 rt rn idx
  | I_LDG (rt,rn,k) ->
      pp_mem "LDG" V64 rt rn (K k)
  | I_IRG (rd,rn,ZR) ->
      sprintf "IRG %s,%s" (pp_xreg rd) (pp_xreg rn)
  | I_IRG (rd,rn,rm) ->
      sprintf "IRG %s,%s,%s" (pp_xreg rd) (pp_xreg rn) (pp_xreg rm)
  | I_UDF k ->
      sprintf "UDF %s" (m.pp_k k)
  (* Pointer Authentication Code *)
  | I_PAC (key, r1, r2) ->
      sprintf "PAC%s %s, %s" (PAC.pp_upper_key key) (pp_reg r1) (pp_reg r2)
  | I_AUT (key, r1, r2) ->
      sprintf "AUT%s %s, %s" (PAC.pp_upper_key key) (pp_reg r1) (pp_reg r2)
  | I_XPACI r ->
      sprintf "XPACI %s" (pp_reg r)
  | I_XPACD r ->
      sprintf "XPACD %s" (pp_reg r)

let m_int = { compat = false ; pp_k = string_of_int ;
              zerop = (function 0 -> true | _ -> false);
              onep = (function 1 -> true | _ -> false);
              k0 = k0; }

let m_hash = { m_int with pp_k = sprintf "#%i"; }

let pp_instruction m =
  do_pp_instruction {m_int with pp_k = pp_k m; }

let dump_pattern_scaled = pp_pattern_scaled m_hash

let dump_instruction = do_pp_instruction m_hash

let dump_instruction_hash =
  do_pp_instruction
    {m_int with compat=true; pp_k = (fun v -> "#" ^ string_of_int v); }

let dump_parsedInstruction =
  do_pp_instruction
    {  compat = false; pp_k = MetaConst.pp_prefix "#";
       zerop = (fun k -> MetaConst.compare MetaConst.zero k = 0);
       onep = (fun k -> MetaConst.compare MetaConst.one k = 0);
       k0 = K MetaConst.zero; }


end

let dump_barrel_shift sh =
  pp_barrel_shift "" sh (fun v -> "#" ^ string_of_int v)

(****************************)
(* Symbolic registers stuff *)
(****************************)

let all_gprs =  List.map (fun r -> Ireg r) gprs

let allowed_for_symb = List.filter (fun r -> r <> linkreg) all_gprs

let fold_regs (f_regs,f_sregs) =

  let fold_reg reg (y_reg,y_sreg) = match reg with
  | Ireg _ -> f_regs reg y_reg,y_sreg
  | Vreg _ -> f_regs reg y_reg,y_sreg
  | SIMDreg _ -> f_regs reg y_reg,y_sreg
  | Zreg _ -> f_regs reg y_reg,y_sreg
  | Preg _ -> f_regs reg y_reg,y_sreg
  | PMreg _ -> f_regs reg y_reg,y_sreg
  | Symbolic_reg reg ->  y_reg,f_sregs reg y_sreg
  | Internal _ | PState _ | ZR | SP | PC | ZAreg _
  | ResAddr | Tag _ | SysReg _
    -> y_reg,y_sreg in

  let fold_kr kr y = match kr with
  | K _ -> y
  | RV (_,r) -> fold_reg r y in

  let fold_idx idx c =
    let open MemExt in
    match idx with
    | Imm _ -> c
    | Reg (_,r,_,_) -> fold_reg r c
    | ZReg (r,_,_) -> fold_reg r c in

  let fold_op_ext e c =
    let open OpExt in
    match e with
    | Imm _ -> c
    | Reg (r,_) -> fold_reg r c in

  fun c ins -> match ins with
  | I_NOP | I_B _ | I_BC _ | I_BL _ | I_FENCE _ | I_RET None | I_ERET | I_SVC _
  | I_UDF _ |  I_SMSTART (None) | I_SMSTOP (None)
    -> c
  | I_CBZ (_,r,_) | I_CBNZ (_,r,_) | I_BLR r | I_BR r | I_RET (Some r)
  | I_MOVZ (_,r,_,_) | I_MOVN (_,r,_,_) | I_MOVK (_,r,_,_)
  | I_ADR (r,_) | I_IC (_,r) | I_DC (_,r)
  | I_TBNZ (_,r,_,_) | I_TBZ (_,r,_,_)
  | I_CHKSLD r | I_CHKTGD r
  | I_MOVI_V (r,_,_) | I_MOVI_S (_,r,_)
  | I_TLBI (_,r)
  | I_AT (_,r)
  | I_MOV_SV (r,_,_)
  | I_INDEX_II (r,_,_)
  | I_RDVL (r,_)
  | I_CNT_INC_SVE (_,r,_,_)
  | I_PTRUE (r,_)
  | I_SMSTART (Some(r)) | I_SMSTOP (Some(r))
  | I_GCSPOPM (r) | I_GCSPUSHM (r) | I_GCSSS1 (r) | I_GCSSS2 (r)
    -> fold_reg r c
  | I_MOV (_,r1,kr)
    -> fold_reg r1 (fold_kr kr c)
  | I_LDAR (_,_,r1,r2) | I_STLR (_,r1,r2) | I_STLRBH (_,r1,r2)
  | I_SXTW (r1,r2) | I_LDARBH (_,_,r1,r2)
  | I_SBFM (_,r1,r2,_,_) | I_UBFM (_,r1,r2,_,_)
  | I_STOP (_,_,_,r1,r2) | I_STOPBH (_,_,_,r1,r2)
  | I_RBIT (_,r1,r2) | I_ABS (_,r1,r2)
  | I_REV (_,r1,r2) | I_LDUR (_, r1, r2, _)
  | I_CHKEQ (r1,r2) | I_CLRTAG (r1,r2) | I_GC (_,r1,r2) | I_LDCT (r1,r2)
  | I_STCT (r1,r2)
  | I_MOV_VE (r1,_,r2,_) | I_MOV_V (r1,r2) | I_MOV_TG (_,r1,r2,_) | I_MOV_FG (r1,_,_,r2)
  | I_MOV_S (_,r1,r2,_)
  | I_FMOV_TG (_,r1,_,r2)
  | I_DUP (r1,_,r2) | I_DUP_SV (r1,_,r2)
  | I_ADDV (_,r1,r2) | I_INDEX_SI (r1,_,r2,_) | I_INDEX_IS (r1,_,_,r2)
  | I_LDUR_SIMD (_,r1,r2,_) | I_LDAPUR_SIMD (_,r1,r2,_)
  | I_STUR_SIMD (_,r1,r2,_) | I_STLUR_SIMD (_,r1,r2,_)
  | I_LDG (r1,r2,_) | I_STZG (r1,r2,_)
  | I_STZ2G (r1,r2,_) | I_STG (r1,r2,_) | I_ST2G (r1,r2,_)
  | I_ALIGND (r1,r2,_) | I_ALIGNU (r1,r2,_)
  | I_ADDVL (r1,r2,_) | I_CTERM (_,_,r1,r2)
  | I_GCSSTR (r1,r2)
    -> fold_reg r1 (fold_reg r2 c)
  | I_MRS (r,sr) | I_MSR (sr,r)
    -> fold_reg (SysReg sr) (fold_reg r c)
  | I_OP3 (_,_,r1,r2,e)
    -> fold_reg r1 (fold_reg r2 (fold_op_ext e c))
  | I_LDR (_,r1,r2,idx) | I_LDRSW (r1,r2,idx)
  | I_LDRS (_,r1,r2,idx) | I_STR (_,r1,r2,idx)
  | I_LDRBH (_,r1,r2,idx) | I_STRBH (_,r1,r2,idx)
  | I_LDR_SIMD (_,r1,r2,idx) | I_STR_SIMD (_,r1,r2,idx)
    -> fold_reg r1 (fold_reg r2 (fold_idx idx c))
  | I_LD1 (rs,_,r2,kr) | I_LD1M (rs,r2,kr) | I_LD1R (rs,r2,kr) | I_LDAP1 (rs,_,r2,kr)
  | I_LD2 (rs,_,r2,kr) | I_LD2M (rs,r2,kr) | I_LD2R (rs,r2,kr)
  | I_LD3 (rs,_,r2,kr) | I_LD3M (rs,r2,kr) | I_LD3R (rs,r2,kr)
  | I_LD4 (rs,_,r2,kr) | I_LD4M (rs,r2,kr) | I_LD4R (rs,r2,kr)
  | I_ST1 (rs,_,r2,kr) | I_ST1M (rs,r2,kr) | I_STL1 (rs,_,r2,kr)
  | I_ST2 (rs,_,r2,kr) | I_ST2M (rs,r2,kr)
  | I_ST3 (rs,_,r2,kr) | I_ST3M (rs,r2,kr)
  | I_ST4 (rs,_,r2,kr) | I_ST4M (rs,r2,kr)
    -> List.fold_right fold_reg rs (fold_reg r2 (fold_kr kr c))
  | I_LD1SP (_,rs,r2,r3,idx)
  | I_LD2SP (_,rs,r2,r3,idx)
  | I_LD3SP (_,rs,r2,r3,idx)
  | I_LD4SP (_,rs,r2,r3,idx)
  | I_ST1SP (_,rs,r2,r3,idx)
  | I_ST2SP (_,rs,r2,r3,idx)
  | I_ST3SP (_,rs,r2,r3,idx)
  | I_ST4SP (_,rs,r2,r3,idx)
    -> List.fold_right fold_reg rs (fold_reg r2 ( fold_reg r3 (fold_idx idx c)))
  | I_CSEL (_,r1,r2,r3,_,_)
  | I_STXR (_,_,r1,r2,r3) | I_STXRBH (_,_,r1,r2,r3)
  | I_BUILD (r1,r2,r3) | I_CPYTYPE (r1,r2,r3) | I_CPYVALUE (r1,r2,r3)
  | I_CSEAL (r1,r2,r3) | I_SEAL (r1,r2,r3) | I_UNSEAL (r1,r2,r3)
  | I_SC (_,r1,r2,r3)
  | I_LDP_SIMD (_,_,r1,r2,r3,_)
  | I_STP_SIMD (_,_,r1,r2,r3,_)
  | I_OP3_SIMD (_,r1,r2,r3) | I_ADD_SIMD (r1,r2,r3) | I_ADD_SIMD_S (r1,r2,r3)
  | I_LDXP (_,_,r1,r2,r3)
  | I_WHILELT (r1,_,r2,r3) | I_WHILELE (r1,_,r2,r3) | I_WHILELO (r1,_,r2,r3) | I_WHILELS (r1,_,r2,r3)
  | I_INDEX_SS(r1,_,r2,r3)
  | I_UADDV (_,r1,r2,r3) | I_ADD_SV (r1,r2,r3) | I_NEG_SV (r1,r2,r3) | I_MOVPRFX (r1,r2,r3) | I_OP3_SV (_,r1,r2,r3)
    -> fold_reg r1 (fold_reg r2 (fold_reg r3 c))
  | I_LDP (_,_,r1,r2,r3,_)
  | I_LDPSW (r1,r2,r3,_)
  | I_STP (_,_,r1,r2,r3,_)
    -> fold_reg r1 (fold_reg r2 (fold_reg r3 c))
  | I_CAS (_,_,r1,r2,r3)
  | I_CASBH (_,_,r1,r2,r3)
  | I_SWP (_,_,r1,r2,r3)
  | I_SWPBH (_,_,r1,r2,r3)
  | I_LDOP (_,_,_,r1,r2,r3)
  | I_LDOPBH (_,_,_,r1,r2,r3)
  | I_ADDSUBEXT (_,_,r1,r2,(_,r3),_)
  | I_EXTR (_,r1,r2,r3,_)
  | I_IRG (r1,r2,r3)
    -> fold_reg r1 (fold_reg r2 (fold_reg r3 c))
  | I_STXP (_,_,r1,r2,r3,r4)
  | I_MOPL (_,r1,r2,r3,r4)
  | I_MOVA_VT (r1,r2,_,r3,r4)
  | I_MOVA_TV (r1,r2,r3,r4,_)
  | I_ADDA (_,r1,r2,r3,r4)
  | I_MOP (_,_,r1,r2,r3,r4)
    -> fold_reg r1 (fold_reg r2 (fold_reg r3 (fold_reg r4 c)))
  | I_CASP (_,_,r1,r2,r3,r4,r5)
    -> fold_reg r1 (fold_reg r2 (fold_reg r3 (fold_reg r4 (fold_reg r5 c))))
  | I_LD1SPT (_,r1,r2,_,r3,r4,idx)
  | I_ST1SPT (_,r1,r2,_,r3,r4,idx)
    -> fold_reg r1 (fold_reg r2 ( fold_reg r3 (fold_reg r4 (fold_idx idx c))))
  | I_PAC (_, src, dst)
  | I_AUT (_, src, dst)
    -> fold_reg src (fold_reg dst c)
  | I_XPACI r -> fold_reg r c
  | I_XPACD r -> fold_reg r c

let map_regs f_reg f_symb =

  let map_reg reg = match reg with
  | Ireg _ -> f_reg reg
  | Vreg _ -> f_reg reg
  | SIMDreg _ -> f_reg reg
  | Zreg _ -> f_reg reg
  | Preg _ -> f_reg reg
  | PMreg _ -> f_reg reg
  | Symbolic_reg reg -> f_symb reg
  | Internal _ | ZR | SP| PC | ZAreg _
  | PState _ | ResAddr | Tag _ | SysReg _
    -> reg in

  let map_kr kr = match kr with
  | K _ -> kr
  | RV (v,r) -> RV (v,map_reg r) in

  let map_idx idx =
    let open MemExt in
    match idx with
    | Imm _ -> idx
    | Reg (v,r,ext,k) -> Reg (v,map_reg r,ext,k)
    | ZReg (r,ext,k) -> ZReg (map_reg r,ext,k) in

  let map_op_ext e =
    let open OpExt in
    match e with
    | Imm _ -> e
    | Reg (r,s) -> Reg (map_reg r,s) in

  fun ins -> match ins with
  | I_NOP
(* Branches *)
  | I_B _
  | I_BC _
  | I_FENCE _
  | I_BL _
  | I_RET None
  | I_ERET
  | I_SVC _
  | I_UDF _
    -> ins
  | I_CBZ (v,r,lbl) ->
      I_CBZ (v,map_reg r,lbl)
  | I_CBNZ (v,r,lbl) ->
      I_CBNZ (v,map_reg r,lbl)
  | I_TBNZ (v,r,k,lbl) ->
      I_TBNZ (v,map_reg r,k,lbl)
  | I_TBZ (v,r,k,lbl) ->
      I_TBZ (v,map_reg r,k,lbl)
  | I_BR r ->
      I_BR (map_reg r)
  | I_BLR r ->
      I_BLR (map_reg r)
  | I_RET (Some r) ->
      I_RET (Some (map_reg r))
(* Load and Store *)
  | I_LDR (v,r1,r2,idx) ->
     I_LDR (v,map_reg r1,map_reg r2,map_idx idx)
  | I_LDRSW (r1,r2,idx) ->
     I_LDRSW (map_reg r1,map_reg r2,map_idx idx)
  | I_LDRS (v,r1,r2,idx) ->
     I_LDRS (v,map_reg r1,map_reg r2,map_idx idx)
  | I_LDRBH (v,r1,r2,idx) ->
     I_LDRBH (v,map_reg r1,map_reg r2,map_idx idx)
  | I_LDUR (v,r1,r2,k) ->
     I_LDUR (v,map_reg r1,map_reg r2,k)
  | I_LDP (t,v,r1,r2,r3,idx) ->
     I_LDP (t,v,map_reg r1,map_reg r2,map_reg r3,idx)
  | I_LDPSW (r1,r2,r3,idx) ->
     I_LDPSW (map_reg r1,map_reg r2,map_reg r3,idx)
  | I_STP (t,v,r1,r2,r3,idx) ->
     I_STP (t,v,map_reg r1,map_reg r2,map_reg r3,idx)
  | I_LDAR (v,t,r1,r2) ->
     I_LDAR (v,t,map_reg r1,map_reg r2)
  | I_LDARBH (bh,t,r1,r2) ->
     I_LDARBH (bh,t,map_reg r1,map_reg r2)
  | I_LDXP (v,t,r1,r2,r3) ->
     I_LDXP (v,t,map_reg r1,map_reg r2,map_reg r3)
  | I_STR (v,r1,r2,idx) ->
      I_STR (v,map_reg r1,map_reg r2,map_idx idx)
  | I_STRBH (v,r1,r2,idx) ->
     I_STRBH (v,map_reg r1,map_reg r2,map_idx idx)
  | I_STLR (v,r1,r2) ->
      I_STLR (v,map_reg r1,map_reg r2)
  | I_STLRBH (v,r1,r2) ->
      I_STLRBH (v,map_reg r1,map_reg r2)
  | I_STXR (v,t,r1,r2,r3) ->
      I_STXR (v,t,map_reg r1,map_reg r2,map_reg r3)
  | I_STXRBH (bh,t,r1,r2,r3) ->
      I_STXRBH (bh,t,map_reg r1,map_reg r2,map_reg r3)
  | I_STXP (v,t,r1,r2,r3,r4) ->
     I_STXP (v,t,map_reg r1,map_reg r2,map_reg r3,map_reg r4)
(* Neon Extension Loads and Stores *)
  | I_LD1 (rs,i,r2,kr) ->
      I_LD1 (List.map map_reg rs, i, map_reg r2, map_kr kr)
  | I_LDAP1 (rs,i,r2,kr) ->
      I_LDAP1 (List.map map_reg rs, i, map_reg r2, map_kr kr)
  | I_LD1M (rs,r2,kr) ->
      I_LD1M (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_LD1R (rs,r2,kr) ->
      I_LD1R (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_LD2 (rs,i,r2,kr) ->
      I_LD2 (List.map map_reg rs,i,map_reg r2,map_kr kr)
  | I_LD2M (rs,r2,kr) ->
      I_LD2M (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_LD2R (rs,r2,kr) ->
      I_LD2R (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_LD3 (rs,i,r2,kr) ->
      I_LD3 (List.map map_reg rs,i,map_reg r2,map_kr kr)
  | I_LD3M (rs,r2,kr) ->
      I_LD3M (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_LD3R (rs,r2,kr) ->
      I_LD3R (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_LD4 (rs,i,r2,kr) ->
      I_LD4 (List.map map_reg rs,i,map_reg r2,map_kr kr)
  | I_LD4M (rs,r2,kr) ->
      I_LD4M (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_LD4R (rs,r2,kr) ->
      I_LD4R (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_ST1 (rs,i,r2,kr) ->
      I_ST1 (List.map map_reg rs,i,map_reg r2,map_kr kr)
  | I_STL1 (rs,i,r2,kr) ->
      I_STL1 (List.map map_reg rs,i,map_reg r2,map_kr kr)
  | I_ST1M (rs,r2,kr) ->
      I_ST1M (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_ST2 (rs,i,r2,kr) ->
      I_ST2 (List.map map_reg rs,i,map_reg r2,map_kr kr)
  | I_ST2M (rs,r2,kr) ->
      I_ST2M (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_ST3 (rs,i,r2,kr) ->
      I_ST3 (List.map map_reg rs,i,map_reg r2,map_kr kr)
  | I_ST3M (rs,r2,kr) ->
      I_ST3M (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_ST4 (rs,i,r2,kr) ->
      I_ST4 (List.map map_reg rs,i,map_reg r2,map_kr kr)
  | I_ST4M (rs,r2,kr) ->
      I_ST4M (List.map map_reg rs,map_reg r2,map_kr kr)
  | I_LDP_SIMD (t,v,r1,r2,r3,idx) ->
      I_LDP_SIMD (t,v,map_reg r1,map_reg r2,map_reg r3,idx)
  | I_STP_SIMD (t,v,r1,r2,r3,idx) ->
      I_STP_SIMD (t,v,map_reg r1,map_reg r2,map_reg r3,idx)
  | I_LDR_SIMD (v,r1,r2,idx) ->
      I_LDR_SIMD (v,map_reg r1,map_reg r2,map_idx idx)
  | I_STR_SIMD (v,r1,r2,idx) ->
      I_STR_SIMD (v,map_reg r1,map_reg r2,map_idx idx)
  | I_LDUR_SIMD (v,r1,r2,k) ->
      I_LDUR_SIMD (v,map_reg r1, map_reg r2,k)
  | I_LDAPUR_SIMD (v,r1,r2,k) ->
      I_LDAPUR_SIMD (v,map_reg r1, map_reg r2,k)
  | I_STUR_SIMD (v,r1,r2,k) ->
      I_STUR_SIMD (v,map_reg r1, map_reg r2,k)
  | I_STLUR_SIMD (v,r1,r2,k) ->
      I_STLUR_SIMD (v,map_reg r1, map_reg r2,k)
  | I_ADDV (v,r1,r2) ->
      I_ADDV (v,map_reg r1,map_reg r2)
  | I_DUP (r1,v,r2) ->
      I_DUP (map_reg r1,v,map_reg r2)
  | I_FMOV_TG (v1,r1,v2,r2) ->
      I_FMOV_TG (v1,map_reg r1,v2,map_reg r2)
  | I_MOV_VE (r1,i1,r2,i2) ->
      I_MOV_VE (map_reg r1,i1,map_reg r2,i2)
  | I_MOV_V (r1,r2) ->
      I_MOV_V (map_reg r1,map_reg r2)
  | I_MOV_TG (v,r1,r2,i) ->
      I_MOV_TG (v,map_reg r1,map_reg r2,i)
  | I_MOV_FG (r1,i,v,r2) ->
      I_MOV_FG (map_reg r1,i,v,map_reg r2)
  | I_MOV_S (v,r1,r2,i) ->
      I_MOV_S (v,map_reg r1,map_reg r2,i)
  | I_MOVI_V (r,k,os) ->
      I_MOVI_V (map_reg r,k,os)
  | I_MOVI_S (v,r,k) ->
      I_MOVI_S (v,map_reg r,k)
  | I_OP3_SIMD (op,r1,r2,r3) ->
      I_OP3_SIMD(op,map_reg r1,map_reg r2,map_reg r3)
  | I_ADD_SIMD (r1,r2,r3) ->
      I_ADD_SIMD (map_reg r1,map_reg r2,map_reg r3)
  | I_ADD_SIMD_S (r1,r2,r3) ->
     I_ADD_SIMD_S (map_reg r1,map_reg r2,map_reg r3)
(* Scalable Vector Extension *)
  | I_PTRUE (predicate,pattern) ->
     I_PTRUE (map_reg predicate,pattern)
  | I_WHILELT (r1,v,r2,r3) ->
     I_WHILELT (map_reg r1,v,map_reg r2,map_reg r3)
  | I_WHILELE (r1,v,r2,r3) ->
     I_WHILELE (map_reg r1,v,map_reg r2,map_reg r3)
  | I_WHILELO (r1,v,r2,r3) ->
     I_WHILELO (map_reg r1,v,map_reg r2,map_reg r3)
  | I_WHILELS (r1,v,r2,r3) ->
     I_WHILELS (map_reg r1,v,map_reg r2,map_reg r3)
  | I_UADDV (v,r1,r2,r3) ->
     I_UADDV (v,map_reg r1,map_reg r2,map_reg r3)
  | I_LD1SP (v,rs,r2,r3,idx) ->
     I_LD1SP (v,List.map map_reg rs,map_reg r2,map_reg r3,map_idx idx)
  | I_LD2SP (v,rs,r2,r3,idx) ->
     I_LD2SP (v,List.map map_reg rs,map_reg r2,map_reg r3,map_idx idx)
  | I_LD3SP (v,rs,r2,r3,idx) ->
     I_LD3SP (v,List.map map_reg rs,map_reg r2,map_reg r3,map_idx idx)
  | I_LD4SP (v,rs,r2,r3,idx) ->
     I_LD4SP (v,List.map map_reg rs,map_reg r2,map_reg r3,map_idx idx)
  | I_ST1SP (v,rs,r2,r3,idx) ->
     I_ST1SP (v,List.map map_reg rs,map_reg r2,map_reg r3,map_idx idx)
  | I_ST2SP (v,rs,r2,r3,idx) ->
     I_ST2SP (v,List.map map_reg rs,map_reg r2,map_reg r3,map_idx idx)
  | I_ST3SP (v,rs,r2,r3,idx) ->
     I_ST3SP (v,List.map map_reg rs,map_reg r2,map_reg r3,map_idx idx)
  | I_ST4SP (v,rs,r2,r3,idx) ->
     I_ST4SP (v,List.map map_reg rs,map_reg r2,map_reg r3,map_idx idx)
  | I_MOV_SV (r,k,os) ->
      I_MOV_SV (map_reg r,k,os)
  | I_DUP_SV (r1,v,r2) ->
      I_DUP_SV (map_reg r1,v,map_reg r2)
  | I_ADD_SV (r1,r2,r3) ->
      I_ADD_SV (map_reg r1,map_reg r2,map_reg r3)
  | I_NEG_SV (r1,r2,r3) ->
      I_NEG_SV (map_reg r1,map_reg r2,map_reg r3)
  | I_MOVPRFX (r1,r2,r3) ->
      I_MOVPRFX (map_reg r1,map_reg r2,map_reg r3)
  | I_OP3_SV (op,r1,r2,r3) ->
      I_OP3_SV (op,map_reg r1,map_reg r2,map_reg r3)
  | I_INDEX_SI (r1,v,r2,k) ->
      I_INDEX_SI (map_reg r1,v,map_reg r2,k)
  | I_INDEX_IS (r1,v,k,r2) ->
      I_INDEX_IS (map_reg r1,v,k,map_reg r2)
  | I_INDEX_SS (r1,v,r2,r3) ->
      I_INDEX_SS (map_reg r1,v,map_reg r2,map_reg r3)
  | I_INDEX_II (r1,k1,k2) ->
      I_INDEX_II (map_reg r1,k1,k2)
  | I_RDVL (r1,k1) ->
     I_RDVL (map_reg r1,k1)
  | I_ADDVL (r1,r2,k1) ->
     I_ADDVL (map_reg r1,map_reg r2,k1)
  | I_CNT_INC_SVE (op,r1,pat,k1) ->
     I_CNT_INC_SVE (op,map_reg r1,pat,k1)
  | I_CTERM (cond,v,rn,rm) ->
     I_CTERM (cond,v,map_reg rn, map_reg rm)
  | I_LD1SPT (v,r1,r2,k,r3,r4,idx) ->
     I_LD1SPT (v,map_reg r1,map_reg r2,k,map_reg r3,map_reg r4,map_idx idx)
  | I_ST1SPT (v,r1,r2,k,r3,r4,idx) ->
     I_ST1SPT (v,map_reg r1,map_reg r2,k,map_reg r3,map_reg r4,map_idx idx)
  | I_MOVA_VT (r1,r2,k,r3,r4) ->
      I_MOVA_VT (map_reg r1,map_reg r2,k,map_reg r3,map_reg r4)
  | I_MOVA_TV (r1,r2,r3,r4,k) ->
      I_MOVA_TV (map_reg r1,map_reg r2,map_reg r3,map_reg r4,k)
  | I_ADDA (s,r1,r2,r3,r4) ->
      I_ADDA (s,map_reg r1,map_reg r2,map_reg r3,map_reg r4)
  | I_SMSTART (Some(r)) ->
      I_SMSTART (Some(map_reg r))
  | I_SMSTOP (Some(r)) ->
      I_SMSTOP (Some(map_reg r))
  | I_SMSTART (None) | I_SMSTOP (None) -> ins
(* Morello *)
  | I_ALIGNU (r1,r2,k) ->
      I_ALIGNU(map_reg r1,map_reg r2,k)
  | I_ALIGND (r1,r2,k) ->
      I_ALIGND (map_reg r1,map_reg r2,k)
  | I_BUILD (r1,r2,r3) ->
      I_BUILD(map_reg r1,map_reg r2,map_reg r3)
  | I_CHKEQ (r1,r2) ->
      I_CHKEQ(map_reg r1,map_reg r2)
  | I_CHKSLD (r1) ->
      I_CHKSLD(map_reg r1)
  | I_CHKTGD (r1) ->
      I_CHKTGD(map_reg r1)
  | I_CLRTAG (r1,r2) ->
      I_CLRTAG(map_reg r1,map_reg r2)
  | I_CPYTYPE (r1,r2,r3) ->
      I_CPYTYPE(map_reg r1,map_reg r2,map_reg r3)
  | I_CPYVALUE (r1,r2,r3) ->
      I_CPYVALUE(map_reg r1,map_reg r2,map_reg r3)
  | I_CSEAL (r1,r2,r3) ->
      I_CSEAL(map_reg r1,map_reg r2,map_reg r3)
  | I_GC (op,r1,r2) ->
      I_GC(op,map_reg r1,map_reg r2)
  | I_LDCT (r1,r2) ->
      I_LDCT(map_reg r1,map_reg r2)
  | I_SC (op,r1,r2,r3) ->
      I_SC(op,map_reg r1,map_reg r2,map_reg r3)
  | I_SEAL (r1,r2,r3) ->
      I_SEAL(map_reg r1,map_reg r2,map_reg r3)
  | I_STCT (r1,r2) ->
      I_STCT(map_reg r1,map_reg r2)
  | I_UNSEAL (r1,r2,r3) ->
      I_UNSEAL(map_reg r1,map_reg r2,map_reg r3)
(* Guarded Control Stack *)
  | I_GCSPOPM (r) ->
      I_GCSPOPM (map_reg r)
  | I_GCSPUSHM (r) ->
      I_GCSPUSHM (map_reg r)
  | I_GCSSTR (r1,r2) ->
      I_GCSSTR (map_reg r1,map_reg r2)
  | I_GCSSS1 (r) ->
      I_GCSSS1 (map_reg r)
  | I_GCSSS2 (r) ->
      I_GCSSS2 (map_reg r)
(* CAS *)
  | I_CAS (v,rmw,r1,r2,r3) ->
      I_CAS (v,rmw,map_reg r1,map_reg r2,map_reg r3)
  | I_CASBH (bh,rmw,r1,r2,r3) ->
      I_CASBH (bh,rmw,map_reg r1,map_reg r2,map_reg r3)
  | I_CASP (v,rmw,r1,r2,r3,r4,r5) ->
      I_CASP (v,rmw,map_reg r1, map_reg r2, map_reg r3, map_reg r4, map_reg r5)
(* SWP *)
  | I_SWP (v,rmw,r1,r2,r3) ->
      I_SWP (v,rmw,map_reg r1,map_reg r2,map_reg r3)
  | I_SWPBH (bh,rmw,r1,r2,r3) ->
      I_SWPBH (bh,rmw,map_reg r1,map_reg r2,map_reg r3)
(* Fetch and Op *)
  | I_LDOP (op,v,rmw,r1,r2,r3) ->
      I_LDOP (op,v,rmw,map_reg r1,map_reg r2,map_reg r3)
  | I_LDOPBH (op,v,rmw,r1,r2,r3) ->
      I_LDOPBH (op,v,rmw,map_reg r1,map_reg r2,map_reg r3)
  | I_STOP (op,v,rmw,r1,r2) ->
      I_STOP (op,v,rmw,map_reg r1,map_reg r2)
  | I_STOPBH (op,v,rmw,r1,r2) ->
      I_STOPBH (op,v,rmw,map_reg r1,map_reg r2)
(* Operations *)
  | I_MOV (v,r,kr) ->
      I_MOV (v,map_reg r,map_kr kr)
  | I_MOVZ (v,r,k,s) ->
      I_MOVZ (v,map_reg r,k,s)
  | I_MOVN (v,r,k,s) ->
      I_MOVN (v,map_reg r,k,s)
  | I_MOVK (v,r,k,s) ->
      I_MOVK (v,map_reg r,k,s)
  | I_SXTW (r1,r2) ->
      I_SXTW (map_reg r1,map_reg r2)
  | I_SBFM (v,r1,r2,k1,k2) ->
      I_SBFM (v,map_reg r1, map_reg r2, k1, k2)
  | I_UBFM (v,r1,r2,k1,k2) ->
      I_UBFM (v,map_reg r1, map_reg r2, k1, k2)
  | I_ADDSUBEXT (v1,op,r1,r2,(v3,r3),ext) ->
     I_ADDSUBEXT (v1,op,map_reg r1,map_reg r2,(v3,map_reg r3),ext)
  | I_MOPL (sop,r1,r2,r3,r4) ->
     I_MOPL (sop,map_reg r1,map_reg r2,map_reg r3,map_reg r4)
  | I_MOP (op, v, r1, r2, r3, r4) ->
      I_MOP (op, v, map_reg r1, map_reg r2, map_reg r3, map_reg r4)
  | I_OP3 (v,op,r1,r2,e) ->
      I_OP3 (v,op,map_reg r1,map_reg r2,map_op_ext e)
  | I_ADR (r,lbl) ->
      I_ADR (map_reg r,lbl)
  | I_RBIT (v,r1,r2) ->
      I_RBIT (v,map_reg r1,map_reg r2)
  | I_ABS (v,r1,r2) ->
      I_ABS (v,map_reg r1,map_reg r2)
  | I_REV (rv,r1,r2) ->
     I_REV (rv,map_reg r1,map_reg r2)
  | I_EXTR (v,r1,r2,r3,k) ->
     I_EXTR (v,map_reg r1,map_reg r2,map_reg r3,k)
  (* Conditinal select *)
  | I_CSEL (v,r1,r2,r3,c,op) ->
      I_CSEL (v,map_reg r1,map_reg r2,map_reg r3,c,op)
(* Cache maintenance *)
  | I_IC (op,r) ->
      I_IC (op,map_reg r)
  | I_DC (op,r) ->
      I_DC (op,map_reg r)
  | I_TLBI (op,r) ->
      I_TLBI (op,map_reg r)
  | I_AT (op,r) ->
      I_AT (op,map_reg r)
(* Read system register *)
  | I_MRS (r,sr) ->
     let sr =
       match map_reg (SysReg sr) with
       | SysReg sr -> sr
       | _ -> assert false in
      I_MRS (map_reg r,sr)
(* Write system register *)
  | I_MSR (sr,r) ->
     let sr =
       match map_reg (SysReg sr) with
       | SysReg sr -> sr
       | _ -> assert false in
     I_MSR (sr,map_reg r)
(* Memory Tagging *)
  | I_STG (r1,r2,k) ->
      I_STG (map_reg r1,map_reg r2,k)
  | I_ST2G (r1,r2,k) ->
      I_ST2G (map_reg r1,map_reg r2,k)
  | I_STZG (r1,r2,k) ->
      I_STZG (map_reg r1,map_reg r2,k)
  | I_STZ2G (r1,r2,k) ->
      I_STZ2G (map_reg r1,map_reg r2,k)
  | I_LDG (r1,r2,k) ->
      I_LDG (map_reg r1,map_reg r2, k)
  | I_IRG (r1,r2,r3_opt) ->
      I_IRG (map_reg r1,map_reg r2,map_reg r3_opt)
  (* Pointer Authentication code *)
  | I_PAC (key, r1, r2) ->
      I_PAC (key, map_reg r1, map_reg r2)
  | I_AUT (key, r1, r2) ->
      I_AUT (key, map_reg r1, map_reg r2)
  | I_XPACI r ->
      I_XPACI (map_reg r)
  | I_XPACD r ->
      I_XPACD (map_reg r)

(* No addresses burried in ARM code *)
let fold_addrs _f c _ins = c

let map_addrs _f ins = ins

let norm_ins ins = ins

(* PLDI submission, complete later *)
let is_data _ _ = assert false

(* Instruction continuation *)

let get_next =
  let open BranchTarget in
  function
  | I_B lbl -> [tgt2next lbl;]
  | I_BC (_,lbl)
  | I_CBZ (_,_,lbl)
  | I_CBNZ (_,_,lbl)
  | I_TBNZ (_,_,_,lbl)
  | I_TBZ (_,_,_,lbl)
  | I_BL lbl
    -> tgt_cons Label.Next lbl
  | I_BLR _|I_BR _|I_RET _ |I_ERET -> [Label.Any]
  | I_NOP
  | I_LDR _
  | I_LDRSW _
  | I_LDRS _
  | I_LDUR _
  | I_LDP _
  | I_LDPSW _
  | I_STP _
  | I_STR _
  | I_LDAR _
  | I_LDARBH _
  | I_STLR _
  | I_STLRBH _
  | I_STXR _
  | I_STXRBH _
  | I_LDRBH _
  | I_STRBH _
  | I_MOV _
  | I_MOVZ _
  | I_MOVN _
  | I_MOVK _
  | I_SXTW _
  | I_SBFM _
  | I_UBFM _
  | I_ADDSUBEXT _
  | I_MOPL _
  | I_MOP _
  | I_OP3 _
  | I_FENCE _
  | I_CSEL _
  | I_CAS _
  | I_CASBH _
  | I_CASP _
  | I_SWP _
  | I_SWPBH _
  | I_LDOP _
  | I_LDOPBH _
  | I_STOP _
  | I_STOPBH _
  | I_ADR _
  | I_RBIT _
  | I_ABS _
  | I_REV _
  | I_EXTR _
  | I_IC _
  | I_DC _
  | I_TLBI _
  | I_AT _
  | I_MRS _ | I_MSR _
  | I_STG _|I_ST2G _|I_STZG _|I_STZ2G _|I_LDG _|I_IRG _
  | I_ALIGND _| I_ALIGNU _|I_BUILD _|I_CHKEQ _|I_CHKSLD _|I_CHKTGD _|I_CLRTAG _
  | I_CPYTYPE _|I_CPYVALUE _|I_CSEAL _|I_GC _|I_LDCT _|I_SC _|I_SEAL _|I_STCT _
  | I_UNSEAL _
  | I_LD1 _ | I_LD1M _ | I_LD1R _ | I_LDAP1 _
  | I_LD2 _ | I_LD2M _ | I_LD2R _
  | I_LD3 _ | I_LD3M _ | I_LD3R _
  | I_LD4 _ | I_LD4M _ | I_LD4R _
  | I_ST1 _ | I_ST1M _ | I_STL1 _
  | I_ST2 _ | I_ST2M _
  | I_ST3 _ | I_ST3M _
  | I_ST4 _ | I_ST4M _
  | I_LDP_SIMD _
  | I_STP_SIMD _
  | I_LDR_SIMD _ | I_STR_SIMD _
  | I_LDUR_SIMD _ | I_LDAPUR_SIMD _
  | I_STUR_SIMD _ | I_STLUR_SIMD _
  | I_ADDV _ | I_DUP _ | I_FMOV_TG _
  | I_MOV_VE _ | I_MOV_V _ | I_MOV_TG _ | I_MOV_FG _
  | I_MOV_S _
  | I_MOVI_V _ | I_MOVI_S _
  | I_OP3_SIMD _ | I_ADD_SIMD _ | I_ADD_SIMD_S _
  | I_LDXP _|I_STXP _|I_SVC _ | I_UDF _
  | I_WHILELT _ | I_WHILELE _ | I_WHILELO _ | I_WHILELS _
  | I_UADDV _ | I_DUP_SV _ | I_PTRUE _
  | I_INDEX_SI _ | I_INDEX_IS _ | I_INDEX_SS _ | I_INDEX_II _
  | I_RDVL _ | I_ADDVL _ | I_CNT_INC_SVE _ | I_CTERM _
  | I_LD1SP _ | I_LD2SP _ | I_LD3SP _ | I_LD4SP _
  | I_ST1SP _ | I_ST2SP _ | I_ST3SP _ | I_ST4SP _
  | I_MOV_SV _ | I_ADD_SV _ | I_NEG_SV _ | I_OP3_SV _ | I_MOVPRFX _
  | I_LD1SPT _  | I_ST1SPT _ | I_SMSTART _ | I_SMSTOP _
  | I_MOVA_TV _ | I_MOVA_VT _ | I_ADDA _
  | I_PAC _ | I_AUT _
  | I_XPACI _ | I_XPACD _
  | I_GCSPOPM _ | I_GCSPUSHM _ | I_GCSSTR _ | I_GCSSS1 _ | I_GCSSS2 _
    -> [Label.Next;]

(* Check instruction validity, beyond parsing *)

let is_nbits_unsigned n =
  let mask = (1 lsl n) - 1 in
  fun k -> k land mask = k

let is_4bits_unsigned = is_nbits_unsigned 4
and is_6bits_unsigned = is_nbits_unsigned 6
and is_12bits_unsigned = is_nbits_unsigned 12
and is_16bits_unsigned = is_nbits_unsigned 16

let is_nbits_signed n =
  let max = 1 lsl (n-1) in
  fun k -> -max <= k && n < max

let is_6bits_signed = is_nbits_signed 6

let is_granule_offset k = is_nbits_signed 9 k && (k mod MachSize.granule_nbytes == 0)

let variant_raw = function
  | V128 -> 128
  | V64 -> 64
  | V32 -> 32

let do_tr_mov k =
  try
    let p =
      let msk = 0xffff in
      if msk land k = k then k,0
      else if (msk lsl 16) land k = k then k lsr 16,16
      else if (msk lsl 32) land k = k then k lsr 32,32
      else if (msk lsl 48) land k = k then k lsr 48,48
      else raise Exit in
    Some p
  with Exit -> None

let tr_mov_imm v k =
  let r =
    match do_tr_mov k with
    | None ->
       begin
         match do_tr_mov (lnot k) with
         | None -> None
         | Some (k,s) -> Some (true,k,s)
       end
    | Some (k,s) -> Some (false,k,s) in
  match r,v with
  | (None,_)
  | (Some (_,_,(32|48)),V32) -> None
  | _,_ -> r

let shift_amount = function
  | S_NOEXT -> 0
  | S_LSL s| S_LSR s| S_ASR s (* | S_ROR s *)
  | S_MSL s
    -> s

let unalias i =
  match i with
  | I_MOV (v,r1,RV (w,r2))
       when v=w ->
     if r1=SP || r2=SP then
       I_OP3 (v,ADD,r1,r2,OpExt.zero)
     else
       I_OP3 (v,ORR,r1,ZR,OpExt.Reg (r2,OpExt.no_shift))
  | I_SXTW (rd,rn) -> I_SBFM (V64,rd,rn,0,31)
  | I_OP3 (V64|V32 as v,LSL,rd,rn,OpExt.Imm (k,0)) ->
     let sz = variant_raw v-1 in
     let imms = sz-k in
     let immr = imms+1 in
    I_UBFM (v,rd,rn,immr,imms)
  | I_OP3 (V64|V32 as v,LSR,rd,rn,OpExt.Imm (k,0)) ->
     let sz = variant_raw v-1 in
     let imms = sz in
     let immr = k in
     I_UBFM (v,rd,rn,immr,imms)
  | I_OP3 (V64|V32 as v,ASR,rd,rn,OpExt.Imm (k,0)) ->
         let sz = variant_raw v-1 in
         let imms = sz in
         let immr = k in
         I_SBFM (v,rd,rn,immr,imms)
  | I_OP3 (V64|V32 as v,ROR,rd,rn,OpExt.Imm (k,0)) ->
     I_EXTR (v,rd,rn,rn,k)
  | I_OP3 (v, ((ADD|ADDS|SUB|SUBS) as op), rd, rn,OpExt.Imm (k,s))
       when k < 0 ->
     let k = -k
     and op =
       match op with
       | ADD -> SUB
       | SUB -> ADD
       | ADDS -> SUBS
       | SUBS -> ADDS
       | _ -> assert false in
     I_OP3 (v, op, rd, rn,OpExt.Imm (k,s))
  | I_MOV (v,rd,K k) ->
     begin
       match tr_mov_imm v k with
       | None ->
          assert false
       | Some (false,k,s) ->
          I_MOVZ (v,rd,k,S_LSL s)
       | Some (true,k,s) ->
          I_MOVN (v,rd,k,S_LSL s)
     end
  | I_STOP (op,v,w,rs,rn) -> I_LDOP (op,v,w_to_rmw w,rs,ZR,rn)
  | I_STOPBH (op,v,w,rs,rn) -> I_LDOPBH (op,v,w_to_rmw w,rs,ZR,rn)
  | _ -> i

(* Check that Z registers are consecutive, wrapping after Z31. *)
let sve_consecutives_reg rs =
  let numbered_regs = List.mapi (fun n reg -> reg,n) vec_regs in
  let _,consecutive =
    List.fold_left (fun (previous,valid) reg ->
        match reg with
        | Zreg (z,_) ->
           let n = List.assoc z numbered_regs in
           let pair_ok =
             match previous with
             | None -> true
             | Some prev -> (prev+1) mod 32 = n in
           Some n, valid && pair_ok
        | _ -> None,false) (None,true) rs in
  consecutive

(* Check that every Z-register element size matches the instruction suffix. *)
let sve_esize_matches_variant v rs =
  let esize = 8 * simd_variant_nbytes v in
  List.for_all (function Zreg (_,size) -> size = esize | _ -> false) rs

(* LD2-4/ST2-4 encode the first Z register and its element size. *)
let is_valid_sve_struct nregs v rs ext =
  let open MemExt in
  let ext_ok =
    match (v,ext) with
    | (_,Imm (_,Idx))
    | (VSIMD8,Reg (V64,_,LSL, 0))
    | (VSIMD16,Reg (V64,_,LSL, 1))
    | (VSIMD32,Reg (V64,_,LSL, 2))
    | (VSIMD64,Reg (V64,_,LSL, 3))
      -> true
    | _ -> false in
  List.length rs = nregs &&
  sve_consecutives_reg rs &&
  sve_esize_matches_variant v rs &&
  ext_ok

let is_valid i =
  match i with
  | I_MOV (v,_,RV (w,_)) -> v=w
  | I_CAS (_,_,_,_,ZR) -> false
  | I_CAS (_,_,_,_,_) -> true
  | I_MOP (_, V128,_,_, _,_) -> false
  | I_OP3 (_,(ADD|SUB|ADDS|SUBS),_,ZR,OpExt.Imm _)
  | I_OP3 (_,(ADD|SUB),ZR,_,OpExt.Imm _)
    -> false
  | I_OP3 (_,(ADD|SUB|ADDS|SUBS),_,_,OpExt.Imm (k,(0|12)))
    ->
(*
 * Using either ADD or SUB the immediate constant size is 12 bits
 *  unsigned + sign. In other words, sign is implemented by selecting
 *  the adequate  instruction and the immediate constant is unsigned.
 *)
     is_12bits_unsigned (abs k)
  | I_OP3 (_,(ADD|SUB|ADDS|SUBS),_,_,OpExt.(Imm _|Reg (_,ROR _)))
    -> false
  | I_OP3 (_,(AND|EOR|ORR),ZR,_,OpExt.Imm _)
    -> false
  | I_OP3 (_,(ADD|SUB|ADDS|SUBS|AND|ANDS|BIC|BICS|EOR|EON|ORN|ORR),
           _,_,OpExt.(Reg (_,(LSL s|LSR s|ASR s|ROR s)))) ->
           is_6bits_unsigned s
  | I_OP3 (_,(AND|ANDS|EOR|ORR),_,_,OpExt.Imm (_,s))
    -> s=0 (* TODO: handle encoding of immediates here? *)
  | I_OP3 (_,(ASR|LSL|LSR|ROR),_,_,OpExt.(Reg (_,s)))
    -> OpExt.is_no_shift s
  | I_MOV (v,_,K k) ->
       Misc.is_some (tr_mov_imm v k)
  | I_MOVZ (_,_,k,S_NOEXT)|I_MOVN (_,_,k,S_NOEXT) ->
     is_16bits_unsigned k
  | I_MOVZ (v,_,k,(S_LSL (0|16|32|48 as s)))
  | I_MOVN (v,_,k,(S_LSL (0|16|32|48 as s))) ->
     is_16bits_unsigned k &&
     begin
       match s with
       | 32|48 -> v = V64
       | _ -> true
     end
  | I_MOVZ _|I_MOVN _ -> false
  | I_STR (_,_,ZR,_)
  | I_STLR (_,_,ZR)
  | I_LDAR (_,_,_,ZR)
  | I_STXR (_,_,_,_,ZR)
    -> false
  | I_LDP ((`PaA),v,_,_,_,(k,idx)) ->
    begin match v,k,idx with
    | (V64,0,Idx) -> true
    | _ -> false
    end
  | I_STP ((`PaL),v,_,_,_,(k,idx)) ->
    begin match v,k,idx with
    | (V64,0,Idx) -> true
    | _ -> false
    end
  | I_LDRBH (_,_,ZR,_)
  | I_STRBH (_,_,ZR,_)
  | I_LDRBH (_,_,_,MemExt.(Reg(V32,_,LSL,_)))
  | I_STRBH (_,_,_,MemExt.(Reg(V32,_,LSL,_)))
    -> false
  | I_RDVL (ZR,_)|I_ADDVL(ZR,_,_)
    -> false
  | I_RDVL (_,k)|I_ADDVL(_,_,k)
    -> is_6bits_signed k
  | I_CNT_INC_SVE (_,_,_,k)
    -> is_4bits_unsigned (k-1)
  | I_STG (_,_,(k,Idx))
  | I_ST2G (_,_,(k,Idx))
  | I_STZG (_,_,(k,Idx))
  | I_STZ2G (_,_,(k,Idx))
  | I_LDG (_,_,k)
    -> is_granule_offset k
  | I_STG _ |I_ST2G _|I_STZG _|I_STZ2G _
    -> false
  | I_LDAP1 ([Vreg(_,(0,64))],_,_,_)
  | I_STL1 ([Vreg(_,(0,64))],_,_,_)
    -> true
  | I_LDAP1 _ | I_STL1 _
    -> false
  | I_OP3_SIMD (EOR,Vreg(_,(8,8)),Vreg(_,(8,8)),Vreg(_,(8,8)))
  | I_OP3_SIMD (EOR,Vreg(_,(16,8)),Vreg(_,(16,8)),Vreg(_,(16,8)))
     -> true
  | I_OP3_SIMD _
     -> false
  | I_OP3_SV(EOR,Zreg(_,64),Zreg(_,64),Zreg(_,64))
     -> true
  | I_OP3_SV _
     -> false
  | I_INDEX_SI (Zreg(_,64),V64,_,_)
  | I_INDEX_SI (Zreg(_,32),V32,_,_)
  | I_INDEX_SI (Zreg(_,16),V32,_,_)
  | I_INDEX_SI (Zreg(_,8),V32,_,_)
  | I_INDEX_IS (Zreg(_,64),V64,_,_)
  | I_INDEX_IS (Zreg(_,32),V32,_,_)
  | I_INDEX_IS (Zreg(_,16),V32,_,_)
  | I_INDEX_IS (Zreg(_,8),V32,_,_)
  | I_INDEX_SS (Zreg(_,64),V64,_,_)
  | I_INDEX_SS (Zreg(_,32),V32,_,_)
  | I_INDEX_SS (Zreg(_,16),V32,_,_)
  | I_INDEX_SS (Zreg(_,8),V32,_,_)
     -> true
  | I_INDEX_SI _ | I_INDEX_IS _ | I_INDEX_SS _
     -> false
  | I_ST1SP (v,_,_,_,ext)
  | I_LD1SP (v,_,_,_,ext) ->
     let open MemExt in
     begin match (v,ext) with
     | (_,Imm (_,Idx))
     | (VSIMD8,Reg (V64,_,LSL, 0))
     | (VSIMD8,ZReg (_,LSL, 0))
     | (VSIMD8,ZReg (_,UXTW, 0))
     | (VSIMD8,ZReg (_,SXTW, 0))
     | (VSIMD16,Reg (V64,_,LSL, 1))
     | (VSIMD16,ZReg (_,LSL, 0))
     | (VSIMD16,ZReg (_,UXTW, 0))
     | (VSIMD16,ZReg (_,SXTW, 0))
     | (VSIMD16,ZReg (_,LSL, 1))
     | (VSIMD16,ZReg (_,UXTW, 1))
     | (VSIMD16,ZReg (_,SXTW, 1))
     | (VSIMD32,Reg (V64,_,LSL, 2))
     | (VSIMD32,ZReg (_,LSL, 0))
     | (VSIMD32,ZReg (_,UXTW, 0))
     | (VSIMD32,ZReg (_,SXTW, 0))
     | (VSIMD32,ZReg (_,LSL, 2))
     | (VSIMD32,ZReg (_,UXTW, 2))
     | (VSIMD32,ZReg (_,SXTW, 2))
     | (VSIMD64,Reg (V64,_,LSL, 3))
     | (VSIMD64,ZReg (_,LSL, 0))
     | (VSIMD64,ZReg (_,UXTW, 0))
     | (VSIMD64,ZReg (_,SXTW, 0))
     | (VSIMD64,ZReg (_,LSL, 3))
     | (VSIMD64,ZReg (_,UXTW, 3))
     | (VSIMD64,ZReg (_,SXTW, 3))
      -> true
     | _ -> false
    end
  | I_ST2SP (v,rs,_,_,ext)
  | I_LD2SP (v,rs,_,_,ext) ->
     is_valid_sve_struct 2 v rs ext
  | I_ST3SP (v,rs,_,_,ext)
  | I_LD3SP (v,rs,_,_,ext) ->
     is_valid_sve_struct 3 v rs ext
  | I_ST4SP (v,rs,_,_,ext)
  | I_LD4SP (v,rs,_,_,ext) ->
     is_valid_sve_struct 4 v rs ext
  | I_ST1SPT (v,reg,index,offset,_,_,ext)
  | I_LD1SPT (v,reg,index,offset,_,_,ext) ->
    let open MemExt in
    let is_slice =
      let is_index =
        match index with
        | Ireg R12 | Ireg R13 | Ireg R14 | Ireg R15
          -> true
        | _ -> false in
      let is_offset =
        match v with
        | VSIMD8 when 0 <= offset && offset <= 15 -> true
        | VSIMD16 when 0 <= offset && offset <= 7 -> true
        | VSIMD32 when 0 <= offset && offset <= 3 -> true
        | VSIMD64 when 0 <= offset && offset <= 1 -> true
        | VSIMD128 when offset == 0 -> true
        | _ -> false in
      let is_tile tile =
        match v with
        | VSIMD8 when tile == 0 -> true
        | VSIMD16 when 0 <= tile && tile <= 1 -> true
        | VSIMD32 when 0 <= tile && tile <= 3 -> true
        | VSIMD64 when 0 <= tile && tile <= 7 -> true
        | VSIMD128 when 0 <= tile && tile <= 15 -> true
        | _ -> false in
      match reg with
      | ZAreg (tile,Some _,_)
        -> (is_tile tile) && is_offset && is_index
      | _ -> false
    in
    begin match (v,ext) with
    | (_,Imm (0,Idx))
    | (VSIMD8,Reg (V64,_,LSL, 0))
    | (VSIMD16,Reg (V64,_,LSL, 1))
    | (VSIMD32,Reg (V64,_,LSL, 2))
    | (VSIMD64,Reg (V64,_,LSL, 3))
    | (VSIMD128,Reg (V64,_,LSL, 4))
     -> is_slice
    | _ -> false
    end
  | I_ADDA (_,ZAreg (_,None,_),_,_,_)
    -> true
  | I_ADDA _
    -> false
  | _ -> true

module PseudoI = struct
      type ins = instruction
      type pins = parsedInstruction
      type reg_arg = reg

      let k_tr = MetaConst.as_int

      let kr_tr = function
        | K i -> K (k_tr i)
        | RV _ as kr -> kr

      let idx_tr (k,e) = k_tr k,e

      let ext_tr idx =
        let open MemExt in
        match idx with
        | Imm k -> Imm (idx_tr k)
        | Reg (v,r,ext,k) -> Reg (v,r,ext,k_tr k)
        | ZReg (r,ext,k) -> ZReg (r,ext,k_tr k)

      let op_ext_tr e =
        let open OpExt in
        match e with
        | Imm (k,s) -> Imm (k_tr k,k_tr s)
        | Reg (r,s) -> Reg (r,map_shift k_tr s)

      let ap_shift f s = match s with
        | S_LSL s -> S_LSL(f s)
        | S_LSR s -> S_LSR(f s)
        | S_ASR s -> S_ASR(f s)
        | S_MSL s -> S_MSL(f s)
        | S_NOEXT  -> S_NOEXT

      let parsed_tr i = match i with
        | I_NOP
        | I_B _
        | I_BR _
        | I_BC _
        | I_CBZ _
        | I_CBNZ _
        | I_BL _
        | I_BLR _
        | I_RET _
        | I_ERET
        | I_LDAR _
        | I_LDARBH _
        | I_STLR _
        | I_STLRBH _
        | I_STXR _
        | I_STXRBH _
        | I_SXTW _
        | I_FENCE _
        | I_CSEL _
        | I_CAS _
        | I_CASBH _
        | I_CASP _
        | I_SWP _
        | I_SWPBH _
        | I_LDOP _
        | I_LDOPBH _
        | I_STOP _
        | I_STOPBH _
        | I_ADR _
        | I_RBIT _
        | I_ABS _
        | I_REV _
        | I_IC _
        | I_DC _
        | I_TLBI _
        | I_AT _
        | I_MRS _ | I_MSR _
        | I_BUILD _|I_CHKEQ _|I_CHKSLD _|I_CHKTGD _|I_CLRTAG _|I_CPYTYPE _
        | I_CPYVALUE _|I_CSEAL _|I_GC _|I_LDCT _|I_SC _|I_SEAL _|I_STCT _
        | I_UNSEAL _
        | I_ADDV _ | I_DUP _ | I_FMOV_TG _
        | I_MOV_VE _ | I_MOV_V _ | I_MOV_TG _ | I_MOV_FG _
        | I_MOV_S _
        | I_LDXP _| I_STXP _
        | I_MOPL _
        | I_MOP _
        | I_WHILELT _ | I_WHILELE _ | I_WHILELO _| I_WHILELS _
        | I_UADDV _ | I_DUP_SV _ | I_PTRUE _
        | I_ADD_SV _ | I_INDEX_SS _
        | I_NEG_SV _ | I_OP3_SV _ | I_MOVPRFX _
        | I_SMSTART _ | I_SMSTOP _ | I_ADDA _
        | I_PAC _ | I_AUT _
        | I_XPACI _ | I_XPACD _
        | I_CTERM _
        | I_IRG _
        | I_GCSPOPM _ | I_GCSPUSHM _ | I_GCSSTR _ | I_GCSSS1 _ | I_GCSSS2 _
            as keep -> keep
        | I_LDR (v,r1,r2,idx) -> I_LDR (v,r1,r2,ext_tr idx)
        | I_LDRSW (r1,r2,idx) -> I_LDRSW (r1,r2,ext_tr idx)
        | I_LDRS (v,r1,r2,idx) -> I_LDRS (v,r1,r2,ext_tr idx)
        | I_LDUR (v,r1,r2,k) -> I_LDUR (v,r1,r2,k_tr k)
        | I_LDP (t,v,r1,r2,r3,idx) -> I_LDP (t,v,r1,r2,r3,idx_tr idx)
        | I_LDPSW (r1,r2,r3,idx) -> I_LDPSW (r1,r2,r3,idx_tr idx)
        | I_STP (t,v,r1,r2,r3,idx) -> I_STP (t,v,r1,r2,r3,idx_tr idx)
        | I_STR (v,r1,r2,idx) -> I_STR (v,r1,r2,ext_tr idx)
        | I_STG (r1,r2,k) -> I_STG (r1,r2,idx_tr k)
        | I_ST2G (r1,r2,k) -> I_ST2G (r1,r2,idx_tr k)
        | I_STZG (r1,r2,k) -> I_STZG (r1,r2,idx_tr k)
        | I_STZ2G (r1,r2,k) -> I_STZ2G (r1,r2,idx_tr k)
        | I_LDG (r1,r2,k) -> I_LDG (r1,r2,k_tr k)
        | I_LDRBH (v,r1,r2,idx) -> I_LDRBH (v,r1,r2,ext_tr idx)
        | I_STRBH (v,r1,r2,idx) -> I_STRBH (v,r1,r2,ext_tr idx)
        | I_SBFM (v,r1,r2,k1,k2) ->
            I_SBFM (v,r1,r2,k_tr k1, k_tr k2)
        | I_UBFM (v,r1,r2,k1,k2) ->
            I_UBFM (v,r1,r2,k_tr k1, k_tr k2)
        | I_TBNZ (v,r1,k,lbl) -> I_TBNZ (v,r1,k_tr k, lbl)
        | I_TBZ (v,r1,k,lbl) -> I_TBZ (v,r1,k_tr k, lbl)
        | I_MOV (v,r,k) -> I_MOV (v,r,kr_tr k)
        | I_MOVZ (v,r,k,s) -> I_MOVZ (v,r,k_tr k,ap_shift k_tr s)
        | I_MOVN (v,r,k,s) -> I_MOVN (v,r,k_tr k,ap_shift k_tr s)
        | I_MOVK (v,r,k,s) -> I_MOVK (v,r,k_tr k,ap_shift k_tr s)
        | I_ADDSUBEXT (v1,op,r1,r2,(v3,r3),(e,ko)) ->
           let ko = Misc.app_opt k_tr ko in
           I_ADDSUBEXT (v1,op,r1,r2,(v3,r3),(e,ko))
        | I_OP3 (v,op,r1,r2,e) -> I_OP3 (v,op,r1,r2,op_ext_tr e)
        | I_EXTR (v,r1,r2,r3,k) -> I_EXTR (v,r1,r2,r3,k_tr k)
        | I_ALIGND (r1,r2,k) -> I_ALIGND (r1,r2,k_tr k)
        | I_ALIGNU (r1,r2,k) -> I_ALIGNU (r1,r2,k_tr k)
        | I_LD1 (rs,i,r2,kr) -> I_LD1 (rs,i,r2,kr_tr kr)
        | I_LDAP1 (rs,i,r2,kr) -> I_LDAP1 (rs,i,r2,kr_tr kr)
        | I_LD1M (rs,r2,kr) -> I_LD1M (rs,r2,kr_tr kr)
        | I_LD1R (rs,r2,kr) -> I_LD1R (rs,r2,kr_tr kr)
        | I_LD2 (rs,i,r2,kr) -> I_LD2 (rs,i,r2,kr_tr kr)
        | I_LD2M (rs,r2,kr) -> I_LD2M (rs,r2,kr_tr kr)
        | I_LD2R (rs,r2,kr) -> I_LD2R (rs,r2,kr_tr kr)
        | I_LD3 (rs,i,r2,kr) -> I_LD3 (rs,i,r2,kr_tr kr)
        | I_LD3M (rs,r2,kr) -> I_LD3M (rs,r2,kr_tr kr)
        | I_LD3R (rs,r2,kr) -> I_LD3R (rs,r2,kr_tr kr)
        | I_LD4 (rs,i,r2,kr) -> I_LD4 (rs,i,r2,kr_tr kr)
        | I_LD4M (rs,r2,kr) -> I_LD4M (rs,r2,kr_tr kr)
        | I_LD4R (rs,r2,kr) -> I_LD4R (rs,r2,kr_tr kr)
        | I_ST1 (rs,i,r2,kr) -> I_ST1 (rs,i,r2,kr_tr kr)
        | I_STL1 (rs,i,r2,kr) -> I_STL1 (rs,i,r2,kr_tr kr)
        | I_ST1M (rs,r2,kr) -> I_ST1M (rs,r2,kr_tr kr)
        | I_ST2 (rs,i,r2,kr) -> I_ST2 (rs,i,r2,kr_tr kr)
        | I_ST2M (rs,r2,kr) -> I_ST2M (rs,r2,kr_tr kr)
        | I_ST3 (rs,i,r2,kr) -> I_ST3 (rs,i,r2,kr_tr kr)
        | I_ST3M (rs,r2,kr) -> I_ST3M (rs,r2,kr_tr kr)
        | I_ST4 (rs,i,r2,kr) -> I_ST4 (rs,i,r2,kr_tr kr)
        | I_ST4M (rs,r2,kr) -> I_ST4M (rs,r2,kr_tr kr)
        | I_LDP_SIMD (t,v,r1,r2,r3,idx) -> I_LDP_SIMD (t,v,r1,r2,r3,idx_tr idx)
        | I_STP_SIMD (t,v,r1,r2,r3,idx) -> I_STP_SIMD (t,v,r1,r2,r3,idx_tr idx)
        | I_LDR_SIMD (v,r1,r2,idx) -> I_LDR_SIMD (v,r1,r2,ext_tr idx)
        | I_STR_SIMD (v,r1,r2,idx) -> I_STR_SIMD (v,r1,r2,ext_tr idx)
        | I_LDUR_SIMD (v,r1,r2,k) -> I_LDUR_SIMD (v,r1,r2,k_tr k)
        | I_LDAPUR_SIMD (v,r1,r2,k) -> I_LDAPUR_SIMD (v,r1,r2,k_tr k)
        | I_STUR_SIMD (v,r1,r2,k) -> I_STUR_SIMD (v,r1,r2,k_tr k)
        | I_STLUR_SIMD (v,r1,r2,k) -> I_STLUR_SIMD (v,r1,r2,k_tr k)
        | I_MOVI_V (r,k,s) -> I_MOVI_V (r,k_tr k,ap_shift k_tr s)
        | I_MOVI_S (v,r,k) -> I_MOVI_S (v,r,k_tr k)
        | I_OP3_SIMD (op,r1,r2,r3) -> I_OP3_SIMD (op,r1,r2,r3)
        | I_ADD_SIMD (r1,r2,r3) -> I_ADD_SIMD (r1,r2,r3)
        | I_ADD_SIMD_S (r1,r2,r3) -> I_ADD_SIMD_S (r1,r2,r3)
        | I_SVC k -> I_SVC (k_tr k)
        | I_UDF k -> I_UDF (k_tr k)
        | I_MOV_SV (r,k,s) -> I_MOV_SV (r,k_tr k,ap_shift k_tr s)
        | I_LD1SP (v,r1,r2,r3,idx) -> I_LD1SP (v,r1,r2,r3,ext_tr idx)
        | I_LD2SP (v,r1,r2,r3,idx) -> I_LD2SP (v,r1,r2,r3,ext_tr idx)
        | I_LD3SP (v,r1,r2,r3,idx) -> I_LD3SP (v,r1,r2,r3,ext_tr idx)
        | I_LD4SP (v,r1,r2,r3,idx) -> I_LD4SP (v,r1,r2,r3,ext_tr idx)
        | I_ST1SP (v,r1,r2,r3,idx) -> I_ST1SP (v,r1,r2,r3,ext_tr idx)
        | I_ST2SP (v,r1,r2,r3,idx) -> I_ST2SP (v,r1,r2,r3,ext_tr idx)
        | I_ST3SP (v,r1,r2,r3,idx) -> I_ST3SP (v,r1,r2,r3,ext_tr idx)
        | I_ST4SP (v,r1,r2,r3,idx) -> I_ST4SP (v,r1,r2,r3,ext_tr idx)
        | I_INDEX_SI (r1,v,r2,k) -> I_INDEX_SI (r1,v,r2,k_tr k)
        | I_INDEX_IS (r1,v,k,r2) -> I_INDEX_IS (r1,v,k_tr k,r2)
        | I_INDEX_II (r1,k1,k2) -> I_INDEX_II (r1,k_tr k1,k_tr k2)
        | I_RDVL (r1,k1) -> I_RDVL (r1,k_tr k1)
        | I_ADDVL (r1,r2,k1) -> I_ADDVL (r1,r2,k_tr k1)
        | I_CNT_INC_SVE (op,r1,pat,k1) -> I_CNT_INC_SVE (op,r1,pat,k_tr k1)
        | I_LD1SPT (v,r1,r2,k,r3,r4,idx) -> I_LD1SPT (v,r1,r2,k_tr k,r3,r4,ext_tr idx)
        | I_ST1SPT (v,r1,r2,k,r3,r4,idx) -> I_ST1SPT (v,r1,r2,k_tr k,r3,r4,ext_tr idx)
        | I_MOVA_VT (r1,r2,k,r3,r4) -> I_MOVA_VT (r1,r2,k_tr k,r3,r4)
        | I_MOVA_TV (r1,r2,r3,r4,k) -> I_MOVA_TV (r1,r2,r3,r4,k_tr k)

      let get_simd_rpt_selem ins rs = match ins with
      | I_LD1M _
      | I_ST1M _
        -> (List.length rs, 1)
      | I_LD2M _
      | I_ST2M _
        -> (1, 2)
      | I_LD3M _
      | I_ST3M _
        -> (1, 3)
      | I_LD4M _
      | I_ST4M _
        -> (1, 4)
      | _ -> assert false

      let get_simd_elements rs = match List.hd rs with
      | Vreg (_, (n, _)) -> n
      | _ -> assert false

      let get_naccesses ins = match ins with
        | I_LDR _ | I_LDRSW _ | I_LDAR _ | I_LDARBH _ | I_LDUR _ | I_LDRS _
        | I_STR _ | I_STLR _ | I_STLRBH _ | I_STXR _
        | I_LDRBH _ | I_STRBH _ | I_STXRBH _ | I_IC _ | I_DC _
        | I_STG _ | I_LDG _
        | I_LDR_SIMD _ | I_STR_SIMD _
        | I_LD1 _ | I_LD1R _ | I_LDAP1 _
        | I_ST1 _ | I_STL1 _
        | I_LDUR_SIMD _ | I_LDAPUR_SIMD _
        | I_STUR_SIMD _ | I_STLUR_SIMD _
        | I_TLBI (_,_)
        | I_XPACI _
        | I_XPACD _
        | I_AT (_,_)
        | I_GCSPOPM _  | I_GCSPUSHM _ | I_GCSSTR _ | I_GCSSS1 _ | I_GCSSS2 _
          -> 1
        | I_LDP _|I_LDPSW _|I_STP _|I_LDXP _|I_STXP _
        | I_CAS _ | I_CASBH _
        | I_SWP _ | I_SWPBH _
        | I_LDOP _ | I_LDOPBH _
        | I_STOP _ | I_STOPBH _
        | I_STZG _|I_ST2G _
        | I_LDP_SIMD _ | I_STP_SIMD _
        | I_LD2 _ | I_LD2R _
        | I_ST2 _
        | I_PAC _
        | I_AUT _
          -> 2
        | I_LD3 _ | I_LD3R _
        | I_ST3 _
        | I_CASP _
          -> 3
        | I_LDCT _ | I_STCT _
        | I_LD4 _ | I_LD4R _
        | I_ST4 _ | I_STZ2G _
          -> 4
        | I_NOP
        | I_B _ | I_BR _
        | I_BL _ | I_BLR _
        | I_RET _
        | I_ERET
        | I_SVC _
        | I_BC _
        | I_CBZ _
        | I_CBNZ _
        | I_TBZ _
        | I_TBNZ _
        | I_MOV _
        | I_MOVZ _
        | I_MOVN _
        | I_MOVK _
        | I_SXTW _
        | I_SBFM _
        | I_UBFM _
        | I_ADDSUBEXT _
        | I_MOPL _
        | I_MOP _
        | I_OP3 _
        | I_FENCE _
        | I_CSEL _
        | I_ADR _
        | I_RBIT _
        | I_ABS _
        | I_REV _
        | I_EXTR _
(*        | I_TLBI (_,ZR) *)
        | I_MRS _ | I_MSR _
        | I_ALIGND _| I_ALIGNU _|I_BUILD _|I_CHKEQ _|I_CHKSLD _|I_CHKTGD _
        | I_CLRTAG _|I_CPYTYPE _|I_CPYVALUE _|I_CSEAL _|I_GC _|I_SC _|I_SEAL _
        | I_UNSEAL _
        | I_ADDV _|I_DUP _| I_FMOV_TG _
        | I_MOV_VE _ | I_MOV_V _ | I_MOV_TG _ | I_MOV_FG _
        | I_MOV_S _
        | I_MOVI_V _ | I_MOVI_S _
        | I_OP3_SIMD _ | I_ADD_SIMD _ | I_ADD_SIMD_S _
        | I_UDF _
        | I_WHILELT _ | I_WHILELE _ | I_WHILELO _ | I_WHILELS _
        | I_PTRUE _
        | I_ADD_SV _ | I_UADDV _ | I_DUP_SV _
        | I_NEG_SV _ | I_MOVPRFX _ | I_OP3_SV _
        | I_INDEX_SI _ | I_INDEX_IS _  | I_INDEX_SS _ | I_INDEX_II _
        | I_RDVL _ | I_ADDVL _ | I_CNT_INC_SVE _
        | I_MOV_SV _ | I_MOVA_TV _ | I_MOVA_VT _ | I_ADDA _
        | I_SMSTART _ | I_SMSTOP _ | I_CTERM _| I_IRG _
          -> 0
        | I_LD1M (rs, _, _)
        | I_LD2M (rs, _, _)
        | I_LD3M (rs, _, _)
        | I_LD4M (rs, _, _)
        | I_ST1M (rs, _, _)
        | I_ST2M (rs, _, _)
        | I_ST3M (rs, _, _)
        | I_ST4M (rs, _, _)
          -> let (rpt, selem) = (get_simd_rpt_selem ins rs) in
             let n = get_simd_elements rs in
             rpt * selem * n
        | I_LD1SP (_,rs,_,_,_) | I_LD2SP (_,rs,_,_,_) | I_LD3SP (_,rs,_,_,_) | I_LD4SP (_,rs,_,_,_)
        | I_ST1SP (_,rs,_,_,_) | I_ST2SP (_,rs,_,_,_) | I_ST3SP (_,rs,_,_,_) | I_ST4SP (_,rs,_,_,_)
          -> 16 * List.length rs (* upper bound *)
        | I_LD1SPT _ | I_ST1SPT _
          -> 16


      let size_of_ins _ = 4

      let fold_labels k f = function
        | I_B lbl
        | I_BC (_,lbl)
        | I_CBZ (_,_,lbl)
        | I_CBNZ (_,_,lbl)
        | I_TBNZ (_,_,_,lbl)
        | I_TBZ (_,_,_,lbl)
        | I_BL lbl
        | I_ADR (_,lbl)
          ->
           begin
             let open BranchTarget in
             match lbl with
             | Lbl lbl -> f k lbl
             | Offset _ -> k
           end
        | _ -> k

      let map_labels f =
        function
        | I_B lbl -> I_B (f lbl)
        | I_BL lbl -> I_BL (f lbl)
        | I_BC (c,lbl) -> I_BC (c,f lbl)
        | I_CBZ (v,r,lbl) -> I_CBZ (v,r,f lbl)
        | I_CBNZ (v,r,lbl) -> I_CBNZ (v,r,f lbl)
        | I_TBNZ (v,r,k,lbl) -> I_TBNZ (v,r,k,f lbl)
        | I_TBZ (v,r,k,lbl) -> I_TBZ (v,r,k,f lbl)
        | I_ADR (r,lbl) -> I_ADR (r, f lbl)
        | ins -> ins

    end

include Pseudo.Make(PseudoI)

(* Atomic-modify instruction *)
let is_atomic = function
  | I_CAS _ | I_CASBH _ | I_SWP _ | I_SWPBH _ | I_CASP _
  | I_LDOP _ | I_LDOPBH _ | I_STOP _ | I_STOPBH _
      -> true
  | _ -> false

let get_macro _name = raise Not_found

let base =  Internal 0
and max_idx = Internal 1
and idx = Internal 2
and ephemeral = Internal 3
let loop_idx = Internal 4

let hash_pteval p = AArch64PteVal.pp_hash (AArch64PteVal.tr p)

(*
 * The set of overwriting instruction is more extensive.
 * Only branches to explicit labels are excluded, as their direct
 * execution would differ in herd and litmus.
 *)

let can_overwrite =
  let open BranchTarget in
  function
  | I_B (Lbl _)
  | I_BC (_,Lbl _)
  | I_BL (Lbl _)
  | I_CBNZ (_,_,Lbl _) | I_CBZ (_,_,Lbl _)
  | I_TBNZ (_,_,_,Lbl _)
  | I_TBZ (_,_,_,Lbl _)
    -> false
  | _ ->
     true

let get_exported_label = function
  | I_ADR (_,bt) -> Some bt
  | _ -> None

let is_branch = function
  | I_B _ | I_BR _
  | I_BC _
  | I_CBZ _
  | I_CBNZ _
  | I_TBNZ _
  | I_TBZ _
  | I_BL _ | I_BLR _
  | I_RET _
  | I_ERET
  | I_SVC _ -> true
  | _ -> false

module
  MakeInstr
    (C:
       sig
         val is_morello : bool
         val parser : string -> instruction
       end)
    (Tr:InstrUtils.Tr with type data = instruction)  = struct

  type exec = Tr.exec
  type t = instruction

  let from_exec = Tr.from_exec
  and to_exec = Tr.to_exec

  let compare = Misc.polymorphic_compare
  let eq = (=)

  module PP = MakePP(C)

  let pp = function
    | I_NOP ->  "NOP"
    | i -> sprintf "instr:%S" (PP.dump_instruction i)

  let tr =
    let open InstrLit in
    function
    | LIT_NOP -> I_NOP
    | LIT_INSTR s -> C.parser s

  let can_overwrite =  can_overwrite

  module Set =
    MySet.Make
      (struct
        type t = instruction
        let compare = compare
      end)
end
