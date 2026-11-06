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


type t =
  A | XA | L | XL | X | N | Q | XQ | NoRet | S
  | NTA (* Non-Temporal, avoid clash with NT in AArch64Base *)
  | EX | EXA | EXL (* Exclusives *)

let is_speculated = function
  | S -> true
  | _ -> false

let is_non_temporal = function
  | NTA -> true
  | _ -> false

let is_atomic = function
  | XA | XQ | XL | X | NoRet -> true
  | _ -> false

let is_noreturn = function
  | NoRet -> true
  | _ -> false

let is_acquire = function
  | A | XA | EXA -> true
  | _ -> false

let is_acquire_pc = function
  | Q | XQ -> true
  | _ -> false

let is_release = function
  | L | XL | EXL -> true
  | _ -> false

let is_exclusive = function
  | EX | EXA | EXL -> true
  | _ -> false

let sets = [
    "X", is_atomic;
    "A",  is_acquire;
    "Q",  is_acquire_pc;
    "L",  is_release;
    "NoRet", is_noreturn;
    "S", is_speculated;
    "NT",is_non_temporal;
    "EX", is_exclusive;
  ]

let pp = function
  | XA -> "Acq*"
  | A -> "Acq"
  | Q -> "AcqPc"
  | XQ -> "AcqPc*"
  | XL -> "Rel*"
  | L -> "Rel"
  | X -> "*"
  | N -> ""
  | NoRet -> "NoRet"
  | S -> "^s"
  | NTA -> "NT"
  | EX -> "EX"
  | EXA -> "AcqEx"
  | EXL -> "RelEx"
