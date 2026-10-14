(****************************************************************************)
(*                           the diy toolsuite                              *)
(*                                                                          *)
(* Jade Alglave, University College London, UK.                             *)
(* Luc Maranget, INRIA Paris-Rocquencourt, France.                          *)
(*                                                                          *)
(* Copyright 2013-present Institut National de Recherche en Informatique et *)
(* en Automatique and the authors. All rights reserved.                     *)
(*                                                                          *)
(* This software is governed by the CeCILL-B license under French law and   *)
(* abiding by the rules of distribution of free software. You can use,      *)
(* modify and/ or redistribute the software under the terms of the CeCILL-B *)
(* license as circulated by CEA, CNRS and INRIA at the following URL        *)
(* "http://www.cecill.info". We also give a copy in LICENSE.txt.            *)
(****************************************************************************)

(* Parsing of command line options and reading of configuration files
   modify mutable variables defined here *)

(* Myself *)
let prog =
  if Array.length Sys.argv > 0 then Sys.argv.(0)
  else "herd"

(* Local options *)
let verbose = ref 0
let libdir = ref (Filename.concat Version.libdir "herd")
let includes = ref []
let exit_if_failed = ref false
let timeout = ref None
let debug = ref Debug_herd.none
let kinds = ref []
let conds = ref []
let model = ref None
let bell = ref None
let macros = ref None
let unroll_default = function
|`ASL -> 4
| _ -> 2
let unroll = ref None
let speedcheck = ref Speed.False
let archcheck = ref true
let optace = ref None
let variant = ref (fun _ -> false)

module Refs = struct
  let fault_handling = ref Fault.Handling.default
  let mte_precision = ref Precision.default
  let mte_store_only = ref false
  let sve_vector_length = ref 128
  let sme_vector_length = ref 128
end

module OptS = ParseTag.MakeOptS(Variant)(Refs)

let byte = ref MachSize.Tag.Auto
let endian = ref None
let initwrites = ref None
let check_filter = ref true
let badexecs = ref true
let badflag = ref None
let through = ref Model.ThroughNone
let throughflag = ref None
let skipchecks = ref StringSet.empty
let strictskip = ref false
let cycles = ref StringSet.empty
let show = ref PrettyConf.ShowNone
let nshow = ref None
let candidates = ref false
let restrict = ref Restrict.No
let outcomereads = ref false
let suffix = ref ""
let dumpes = ref false
let outputdir = ref PrettyConf.NoOutputdir
let dumplem = ref false
let dumptex = ref false
let maxphantom= ref None
let statelessrc11 = ref false
let dumpallfaults = ref false

(* Pretty printing configuration, deserves its own module *)
module PP = struct
  open PrettyConf
  let dotmode =  ref Plain
  let dotcom = ref None
  let view = ref None
  let showevents = ref NonRegEvents
  let showkind = ref false
  let shortlegend = ref false
  let texmacros = ref false
  let tikz = ref false
  let hexa = ref false
  let mono = ref false
  let fontname = ref None
  let fontsize = ref None
  let edgedelta = ref 0
  let penwidth = ref None
  let arrowsize = ref None
  let splines = ref None
  let overlap = ref None
  let sep = ref None
  let pad = ref None
  let margin = ref None
  let scale = ref 1.0
  let xscale = ref 1.0
  let yscale = ref 1.0
  let dsiy = ref 0.3
  let siwidth = ref 0.75
  let boxscale = ref 1.0
  let ptscale = ref 3.0
  let squished = ref false
  let graph = ref Graph.Cluster
  let showpo = ref true
  let relabel = ref false
  let withbox = ref false
  let labelbox = ref false
  let showthread = ref true
  let showlegend = ref true
  let showfinalrf = ref false
  let showinitrf = ref false
  let finaldotpos = ref (0.4,-0.3333)
  let initdotpos = ref (-0.4,0.3333)
  let oneinit = ref true
  let initpos = ref None
  let showinitwrites = ref true
  let threadposy = ref 0.6
  let dotheader = ref None
  let brackets = ref true
  let showobserved = ref false
  let movelabel = ref false
  let fixedsize = ref false

  let edgeattrs = ref DotEdgeAttr.empty
  let add_edgeattr lbl a v = edgeattrs := DotEdgeAttr.add lbl a v !edgeattrs
  let get_edgeattrs () = !edgeattrs

  let doshow = ref StringSet.empty
  let unshow = ref StringSet.empty

  let add_doshow u =
    doshow := StringSet.union u !doshow ;
    unshow := StringSet.diff !unshow u

  let add_unshow u =
    unshow := StringSet.union u !unshow ;
    doshow := StringSet.diff !doshow u

  let noid = ref StringSet.empty
  let symetric = ref StringSet.empty
  let classes = ref None
  let showraw = ref StringSet.empty
  let extrachars = ref 0.0
  let shift = ref [| |]
  let edgemerge = ref false
  let labelinit = ref true
end

(* Load file from library, list of includes to add to search paths given *)

let libfind includes debug =
  let module ML =
    MyLib.Make
      (struct
        let includes = includes
        let env = Some "HERDLIB"
        let libdir = !libdir
        let debug = debug
      end) in
  ML.find
