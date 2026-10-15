(* ========================================================================= *)
(*                               HOL LIGHT                                   *)
(*                                                                           *)
(*              Modern OCaml version of the HOL theorem prover               *)
(*                                                                           *)
(*                            John Harrison                                  *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2024                       *)
(*              (c) Copyright, Juneyoung Lee 2024                            *)
(* ========================================================================= *)

include Bignum;;
open Hol_loader;;

(* ------------------------------------------------------------------------- *)
(* Bind these to names that are independent of OCaml versions before they    *)
(* are potentially overwritten by an identifier of the same name. In older   *)
(* and newer Ocaml versions these are respectively:                          *)
(*                                                                           *)
(* Pervasives.sqrt -> Float.sqrt                                             *)
(* Pervasives.abs_float -> Stdlib.abs_float / Float.abs                      *)
(* ------------------------------------------------------------------------- *)

let float_sqrt = sqrt;;
let float_fabs = abs_float;;

(* ------------------------------------------------------------------------- *)
(* Various tweaks to OCaml and general library functions.                    *)
(* ------------------------------------------------------------------------- *)

loads "system.ml";;     (* Set up proper parsing and load bignums            *)
loads "lib.ml";;        (* Various useful general library functions          *)

(* ------------------------------------------------------------------------- *)
(* The logical core.                                                         *)
(* ------------------------------------------------------------------------- *)

loads "fusion.ml";;

(* ------------------------------------------------------------------------- *)
(* Some extra support stuff needed outside the core.                         *)
(* ------------------------------------------------------------------------- *)

loads "basics.ml";;     (* Additional syntax operations and other utilities  *)
loads "nets.ml";;       (* Term nets for fast matchability-based lookup      *)

(* ------------------------------------------------------------------------- *)
(* The interface.                                                            *)
(* ------------------------------------------------------------------------- *)

loads "printer.ml";;    (* Crude prettyprinter                               *)
loads "preterm.ml";;    (* Preterms and their interconversion with terms     *)
loads "parser.ml";;     (* Lexer and parser                                  *)

(* ------------------------------------------------------------------------- *)
(* Higher level deductive system.                                            *)
(* ------------------------------------------------------------------------- *)

loads "equal.ml";;      (* Basic equality reasoning and conversionals        *)
loads "bool.ml";;       (* Boolean theory and basic derived rules            *)
loads "drule.ml";;      (* Additional derived rules                          *)
loads "tactics.ml";;    (* Tactics, tacticals and goal stack                 *)
loads "itab.ml";;       (* Toy prover for intuitionistic logic               *)
loads "simp.ml";;       (* Basic rewriting and simplification tools          *)
loads "theorems.ml";;   (* Additional theorems (mainly for quantifiers) etc. *)
loads "ind_defs.ml";;   (* Derived rules for inductive definitions           *)
loads "class.ml";;      (* Classical reasoning: Choice and Extensionality    *)
loads "trivia.ml";;     (* Some very basic theories, e.g. type ":1"          *)
loads "canon.ml";;      (* Tools for putting terms in canonical forms        *)
loads "meson.ml";;      (* First order automation: MESON (model elimination) *)
loads "firstorder.ml";; (* More utilities for first-order shadow terms       *)
loads "metis.ml";;      (* More advanced first-order automation: Metis       *)
loads "thecops.ml";;    (* Connection-based automation: leanCoP and nanoCoP  *)
loads "quot.ml";;       (* Derived rules for defining quotient types         *)
loads "impconv.ml";;    (* More powerful implicational rewriting etc.        *)

(* ------------------------------------------------------------------------- *)
(* Mathematical theories and additional proof tools.                         *)
(* ------------------------------------------------------------------------- *)

loads "pair.ml";;       (* Theory of pairs                                   *)
loads "compute.ml";;    (* General call-by-value reduction tool for terms    *)
loads "nums.ml";;       (* Axiom of Infinity, definition of natural numbers  *)
loads "recursion.ml";;  (* Tools for primitive recursion on inductive types  *)
loads "arith.ml";;      (* Natural number arithmetic                         *)
loads "wf.ml";;         (* Theory of wellfounded relations                   *)
loads "calc_num.ml";;   (* Calculation with natural numbers                  *)
loads "normalizer.ml";; (* Polynomial normalizer for rings and semirings     *)
loads "grobner.ml";;    (* Groebner basis procedure for most semirings       *)
loads "ind_types.ml";;  (* Tools for defining inductive types                *)
loads "lists.ml";;      (* Theory of lists                                   *)
loads "realax.ml";;     (* Definition of real numbers                        *)
loads "calc_int.ml";;   (* Calculation with integer-valued reals             *)
loads "realarith.ml";;  (* Universal linear real decision procedure          *)
loads "real.ml";;       (* Derived properties of reals                       *)
loads "calc_rat.ml";;   (* Calculation with rational-valued reals            *)
loads "int.ml";;        (* Definition of integers                            *)
loads "sets.ml";;       (* Basic set theory                                  *)
loads "iterate.ml";;    (* Iterated operations                               *)
loads "cart.ml";;       (* Finite Cartesian products                         *)
loads "define.ml";;     (* Support for general recursive definitions         *)


(* ------------------------------------------------------------------------- *)
(* Checks that no axiom other than those allowed by core libs are introduced *)
(* ------------------------------------------------------------------------- *)

let check_axioms () =
  let basic_axioms = [INFINITY_AX; SELECT_AX; ETA_AX] in
  let l = filter (fun th -> not (mem th basic_axioms)) (axioms()) in
  if l <> [] then
    let msg = "[" ^ (String.concat ", " (map string_of_thm l)) ^ "]" in
    failwith ("check_axioms: " ^ msg);;
