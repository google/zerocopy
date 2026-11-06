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

module Make
    (TopConf:AArch64Sig.Config)
    (V:Value.AArch64 with type Cst.Instr.t = AArch64Base.instruction)
    =
  struct
    module C = TopConf.C
    module ConfLoc = SemExtra.ConfigToArchConfig(C)
    module AArch64 = AArch64Arch_herd.Make(ConfLoc)(V)
    module Act = MachAction.Make(ConfLoc)(AArch64)
    module Annot = AArch64Annot
    include SemExtra.Make(C)(AArch64)(Act)

    let dirty = match TopConf.dirty with | None -> DirtyBit.soft | Some d -> d
    let mixed = AArch64.is_mixed
    (* We need to be aware of endianness for 128-bit Neon LDR/STR, because
     * these are always little endian *)
    let endian = AArch64.endian
    let memtag = C.variant Variant.MemTag
    let morello = C.variant Variant.Morello
    let sme = C.variant Variant.SME
    let sve = C.variant Variant.SVE || sme
    let neon = C.variant Variant.Neon || sve
    let kvm = C.variant Variant.VMSA
    let is_branching = kvm && not (C.variant Variant.NoPteBranch)
    let pte2 = kvm && (C.variant Variant.PTE2 || C.variant Variant.ASL)
    let self = C.variant Variant.Ifetch
    let pauth1 = C.variant (Variant.PacVersion `PAuth1)
    let pauth2 = C.variant (Variant.PacVersion `PAuth2)
    let pac = pauth1 || pauth2
    let key_enable key = not (C.variant (Variant.NoPacKey key))
    let const_pac_field = C.variant Variant.ConstPacField
    let fpac = C.variant Variant.FPac
    let gcs = C.variant Variant.ShadowStack

    let check_kvm ins =
      if not kvm then
        Warn.user_error "%s without -variant vmsa" ins

    let check_mixed ins =
      if not mixed then
        Warn.user_error "%s without -variant mixed" ins

    let check_memtag ins =
      if not memtag then
        Warn.user_error "%s without -variant memtag" ins

    let check_morello inst =
      if not morello then
        Warn.user_error
          "morello instruction %s require -variant morello"
          (AArch64.dump_instruction inst)

    let check_neon inst =
      if not neon then
        Warn.user_error
          "Neon instruction %s requires -variant neon"
          (AArch64.dump_instruction inst)

    let check_sve inst =
      if not sve then
        Warn.user_error
          "SVE instruction %s requires -variant sve"
          (AArch64.dump_instruction inst)

    let check_sme inst =
      if not sme then
        Warn.user_error
          "SME instruction %s requires -variant sme"
          (AArch64.dump_instruction inst)

    let check_gcs inst =
      if not gcs then
        Warn.user_error
          "GCS instruction %s requires -variant shadowstack"
          (AArch64.dump_instruction inst)
    let check_pac inst =
      if not pac then
        Warn.user_error
          "Pauth instruction %s requires -variant pauth1 or pauth2"
          (AArch64.dump_instruction inst)

(* Barrier pretty print *)
    let barriers =
      let bs = AArch64Base.do_fold_dmb_dsb (fun h t -> h::t) []
      in List.map
        (fun b ->
          { barrier = b;
            pp = Misc.lowercase (AArch64Base.pp_barrier b)})
        bs
    let isync = Some { barrier = AArch64Base.ISB;pp = "isb";}

    let atomic_pair_allowed _ _ = true

    let quad = MachSize.Quad (* This machine natural size *)
    and aexp = AArch64Explicit.Exp    (* Explicit accesses *)

    let tnt2annot =
      let open Annot in
      function
      | AArch64.TT -> N
      | AArch64.NT -> NTA

    (* Semantics proper *)
    module Mixed(SZ:ByteSize.S) : sig
      val build_semantics : test -> A.inst_instance_id -> (proc * branch) M.t
      val can_unset_af_loc : event -> V.v option
      val spurious_setaf : value:V.v -> location:V.v -> unit M.t
    end = struct

      module Mixed = M.Mixed(SZ)

      let (>>=) = M.(>>=)
      let (let*) = M.(>>=)
      let (>>==) = M.(>>==)
      let (>>*=) = M.(>>*=)
      let (>>*==) = M.(>>*==)
      let (>>**==) = M.(>>**==)
      let (>>|) = M.(>>|)
      let (and*) = M.(>>|)
      let (>>||) = M.para_atomic
      let (>>!) = M.(>>!)
      let (>>::) = M.(>>::)
      let ( ||| ) = M.( ||| )

      let sxt_op sz = M.op1 (Op.Sxt sz)
      and uxt_op sz = M.op1 (Op.Mask sz)
      let sxtw_op = sxt_op MachSize.Word
      and uxtw_op = uxt_op MachSize.Word

      let assume_collision v1 v2 =
        M.restrict
          [M.VC.Predicate (A.CS.pred_assume_collision v1 v2)]

      let assume_no_collision v1 v2 =
        M.restrict
          [M.VC.Predicate (A.CS.pred_assume_no_collision v1 v2)]

      (* Wrap an operation by checking if the operands can be equal due to a
         hash collision of two PAC fields. When both operands are already
         determined, we first check whether such a collision is possible and
         avoid branching otherwise. *)
      let collision_wrapper op c1 c2 =
        if pac then
          let collision_possible =
            if V.is_var_determined c1 && V.is_var_determined c2 then
              M.op (Op.ArchOp AArch64Op.CollisionPossible) c1 c2
            else
              M.unitT V.v_true in
          collision_possible >>= fun c ->
          M.choiceT c
            (M.altT
               (assume_collision c1 c2 >>= fun _ ->
                op c1 c1)
               (assume_no_collision c1 c2 >>= fun _ ->
                op c1 c2))
            (op c1 c2)
        else
          op c1 c2

      (* Wrap equality test to check for a hash collision of two PAC fields *)
      let is_eq c1 c2 =
        collision_wrapper (M.op Op.Eq) c1 c2

      (* Ensure that two constants are different for the rest of the execution *)
      let neqT c1 c2 =
        if pac then
          assume_no_collision c1 c2 >>= fun _ -> M.unitT ()
        else
          M.neqT c1 c2

      (* Wrap exclusive-or to check for a hash collision of two PAC fields *)
      let exclusive_or c1 c2 =
        collision_wrapper (M.op Op.Xor) c1 c2

      (* Wrap subtraction to check for a hash collision of two PAC fields *)
      let subtraction c1 c2 =
        collision_wrapper (M.op Op.Sub) c1 c2

      let mask32 ty m =
        let open AArch64Base in
        match ty with
        | V32 -> fun v -> uxtw_op v >>= m
        | V64 when not morello -> m
        | V64 -> fun v -> uxt_op MachSize.Quad v >>= m
        | V128 -> m

(*  Promotion/Demotion *)
      let promote = M.op1 Op.Promote
      and demote = M.op1 Op.Demote


      let is_zero v = M.op Op.Eq v V.zero
      and is_not_zero v = M.op Op.Ne v V.zero
      and add_if ok k = if ok then fun a -> M.add a (V.intToV k) else M.unitT

(* Ordinary access action *)
      let access_anexp anexp d loc v ac =
        Act.Access (d,loc,v,Annot.N,anexp,quad,ac)
      let access_ord d loc v ac = access_anexp aexp d loc v ac

(* Basic read, from register *)
      let mk_read sz an anexp loc v =
        let ac = Act.access_of_location_std loc in
        Act.Access (Dir.R, loc, v, an, anexp, sz, ac)

      let has_handler ii =
        match ii.A.env.A.fh_code with
        | Some _ -> true
        | None -> false

      let is_mte_sync dir =
        let open Precision in
        match C.mte_precision,dir with
        | (Synchronous,_)|(Asymmetric,(Dir.R)) -> true
        | (Asynchronous,_)|(Asymmetric,Dir.W) -> false

      let mk_fault a dir annot ii ft msg =
        let open FaultType.AArch64 in
        let fh = has_handler ii in
        let is_sync_exc_entry, ii, loc =
          match ft, is_mte_sync dir with
          | Some FaultType.AArch64.TagCheck, false ->
            assert (C.variant Variant.MemTag) ;
            false, { ii with A.labels = Label.Set.empty }, None
          | _, _ ->
            true, ii, Misc.map_opt (fun a -> A.Location_global a) a in
        M.mk_singleton_es
          (Act.Fault (ii,loc,dir,annot,fh || is_sync_exc_entry,ft,msg)) ii

      let read_reg port r ii = match r with
      | AArch64.ZR -> M.unitT V.zero
      | _ ->
          M.read_loc port
            (mk_read quad Annot.N aexp) (A.Location_reg (ii.A.proc,r)) ii

      let read_reg_morello port r ii =
        if not morello then
          Warn.user_error "capabilities require -variant morello" ;
        match r with
        | AArch64.ZR -> M.unitT V.zero
        | _ ->
            M.read_loc port
              (mk_read MachSize.S128 Annot.N aexp)
              (A.Location_reg (ii.A.proc,r)) ii

      let read_reg_neon port r ii =
        let vr = match r with
        | AArch64Base.SIMDreg _ -> r
        | AArch64Base.Vreg(vr',_) -> (AArch64Base.SIMDreg vr')
        | _ -> assert false in
          let location = A.Location_reg (ii.A.proc,vr) in
          M.read_loc port (mk_read MachSize.S128 Annot.N aexp) location ii

      let neon_getlane cur_val idx esize =
        let mask = V.op1 (Op.LeftShift (idx*esize)) (AArch64.neon_mask esize) in
        M.op Op.And mask cur_val >>= fun masked_val ->
        M.op1 (Op.LogicalRightShift (idx*esize)) masked_val

      let read_reg_neon_elem port r idx ii = match r with
      | AArch64Base.Vreg (_,(_,esize)) ->
          read_reg_neon port r ii >>= fun cur_val ->
          neon_getlane cur_val idx esize
      | _ -> assert false

      let read_reg_sz port sz r ii = match sz with
      | MachSize.S128 -> read_reg_morello port r ii
      | MachSize.Quad when not morello -> read_reg port r ii
      | MachSize.Quad|MachSize.Word|MachSize.Short|MachSize.Byte ->
          read_reg port r ii >>= uxt_op sz

      let read_reg_ord = read_reg_sz Port.No quad
      let read_reg_ord_sz = read_reg_sz Port.No
      let read_reg_data = read_reg_sz Port.Data quad
      let read_reg_data_sz = read_reg_sz Port.Data
      let read_reg_addr = read_reg_sz Port.Addr quad
      let read_reg_addr_sz = read_reg_sz  Port.Addr

(* Fetch of an instruction, i.e., a read from a label *)
      let mk_fetch an ac loc v =
        Act.Access (Dir.R, loc, v, an, AArch64.nexp_ifetch, MachSize.Word, ac)

(* Basic write, to register  *)
      let mk_write sz an anexp ac v loc =
        Act.Access (Dir.W, loc, v, an, anexp, sz, ac)

      let write_reg r v ii = match r with
      | AArch64.ZR -> M.unitT ()
      | _ ->
          M.write_loc
            (mk_write quad Annot.N aexp Access.REG v)
            (A.Location_reg (ii.A.proc,r)) ii

      let write_reg_dest r v ii = match r with
        | AArch64.ZR -> M.unitT V.zero
        | _ ->
            write_reg r v ii >>= fun () -> M.unitT v

      let write_nzcv (n, z, c, v) ii =
        let reg_n = AArch64.(PState PSTATE.N)
        and reg_z = AArch64.(PState PSTATE.Z)
        and reg_c = AArch64.(PState PSTATE.C)
        and reg_v = AArch64.(PState PSTATE.V) in
            write_reg reg_n n ii
        ||| write_reg reg_z z ii
        ||| write_reg reg_c c ii
        ||| write_reg reg_v v ii
        >>= fun () -> M.unitT [ (reg_n, n); (reg_z, z); (reg_c, c); (reg_v, v) ]

      let write_nzcv_one_val v ii =
        M.op1 (Op.ReadBit 3) v >>| M.op1 (Op.ReadBit 2) v
        >>| M.op1 (Op.ReadBit 1) v >>| M.op1 (Op.ReadBit 0) v
        >>= fun (((n, z), c), v) -> write_nzcv (n, z, c, v) ii

      let write_nzcv_no_next vs ii = write_nzcv vs ii >>! ()

      let read_nzcv ii =
        let ( << ) m i = m >>= fun v -> M.op1 (Op.LeftShift i) v in
        let ( || ) m1 m2 = m1 >>| m2 >>= fun (v1, v2) -> M.op Op.Or v1 v2 in
        let n = read_reg Port.No AArch64.(PState PSTATE.N) ii
        and z = read_reg Port.No AArch64.(PState PSTATE.Z) ii
        and c = read_reg Port.No AArch64.(PState PSTATE.C) ii
        and v = read_reg Port.No AArch64.(PState PSTATE.V) ii in
        n << 3 || z << 2 || c << 1 || v

      let write_reg_morello r v ii =
        if not morello then
          Warn.user_error "capabilities require -variant morello" ;
        M.write_loc
          (mk_write MachSize.S128  Annot.N aexp Access.REG v)
          (A.Location_reg (ii.A.proc,r)) ii

      let neon_setlane old_val idx esize v =
        let mask =
          V.op1 (Op.LeftShift (idx*esize)) (AArch64.neon_mask esize) in
        let invert = V.op1 Op.Inv mask in
        M.op1 (Op.LeftShift (idx*esize)) v >>= fun new_val ->
        M.op Op.And invert old_val >>|
        M.op Op.And mask new_val >>= fun (v1,v2) ->
        M.op Op.Or v1 v2

      let rec neon_replicate old_val nelem esize v =
          if nelem <= 0 then
            M.unitT old_val
          else
            neon_setlane old_val (nelem-1) esize v >>= fun old_val ->
            neon_replicate old_val (nelem-1) esize v

      let write_reg_neon_sz sz r v ii =
        let vr = match r with
        | AArch64Base.SIMDreg _ -> r
        | AArch64Base.Vreg(vr',_) -> (AArch64Base.SIMDreg vr')
        | _ -> assert false in
          (* Clear unused register bits (zero extend) *)
          promote v >>= uxt_op sz >>= fun v ->
          let location = A.Location_reg (ii.A.proc,vr) in
          M.write_loc (mk_write MachSize.S128 Annot.N aexp Access.REG v) location ii

      let write_reg_neon = write_reg_neon_sz MachSize.S128

      let write_reg_neon_elem sz r idx v ii = match r with
      | AArch64Base.Vreg (_,(_,esize)) ->
         read_reg_neon Port.No r ii >>=
         fun old_val -> neon_setlane old_val idx esize v >>= fun new_val ->
         write_reg_neon_sz sz r new_val ii
      | _ -> assert false

      let write_reg_neon_rep sz r v ii = match r with
      | AArch64Base.Vreg (_,(nelem,esize)) ->
         neon_replicate v nelem esize v
         >>= fun new_val -> write_reg_neon_sz sz r new_val ii
      | _ -> assert false

      let scalable_nbits =
        if C.variant Variant.SME && C.variant Variant.SVE && (TopConf.sme_vector_length != TopConf.sve_vector_length) then
            Warn.user_error "Mismatch vector lengths: SME VL%d != SVE VL%d" TopConf.sme_vector_length TopConf.sve_vector_length
        else if C.variant Variant.SME then
          TopConf.sme_vector_length
        else if C.variant Variant.SVE then
          TopConf.sve_vector_length
        else 0

      let scalable_nbytes = scalable_nbits / 8

      let predicate_psize r = match r with
      | AArch64Base.Preg (_,esize)
      (* Infer predicate bitsize from Z or ZA register *)
      | AArch64Base.ZAreg (_,_,esize)
      | AArch64Base.Zreg (_,esize) -> esize / 8
      | _ -> assert false

      let predicate_nelem r = match r with
      | AArch64Base.Preg (_,esize)
      (* Infer predicate elements from Z or ZA register *)
      | AArch64Base.ZAreg (_,_,esize)
      | AArch64Base.Zreg (_,esize) -> scalable_nbits / esize
      | _ -> assert false

      let predicate_count predicate nelem =
        let open AArch64 in
        match predicate with
        | VL1 when nelem >= 1 -> 1
        | VL2 when nelem >= 2 -> 2
        | VL3 when nelem >= 3 -> 3
        | VL4 when nelem >= 4 -> 4
        | VL5 when nelem >= 5 -> 5
        | VL6 when nelem >= 6 -> 6
        | VL7 when nelem >= 7 -> 7
        | VL8 when nelem >= 8 -> 8
        | VL16 when nelem >= 16 -> 16
        | VL32 when nelem >= 32 -> 32
        | VL128 when nelem >= 128 -> 128
        | VL256 when nelem >= 256 -> 256
        | MUL3 -> nelem - (nelem mod 3)
        | MUL4 -> nelem - (nelem mod 4)
        | ALL -> nelem
        | POW2 ->
            let rec calc n =
              if nelem >= (Int.shift_left 1 n) then calc (n+1)
              else Int.shift_left 1 (n-1) in
            calc 1
        | _ -> 0

      let read_reg_predicate r ii =
        let vr = match r with
        | AArch64Base.Preg(_,_) | AArch64Base.PMreg(_,_) -> r
        | _ -> assert false in
        let location = A.Location_reg (ii.A.proc,vr) in
        M.read_loc Port.No (mk_read MachSize.S128 Annot.N aexp) location ii

      let predicate_setlane old_val idx psize v =
        let mask =
          V.op1 (Op.LeftShift (idx*psize))
            (AArch64.predicate_mask psize) in
        let invert = V.op1 Op.Inv mask in
        M.op1 (Op.LeftShift (idx*psize)) v  >>= fun new_val ->
        M.op Op.And invert old_val >>|
        M.op Op.And mask new_val >>= fun (v1,v2) ->
        M.op Op.Or v1 v2

      let predicate_getlane cur_val idx psize =
        let mask = V.op1 (Op.LeftShift (idx*psize)) (AArch64.predicate_mask psize) in
        M.op Op.And mask cur_val >>= fun masked_val ->
        M.op1 (Op.LogicalRightShift (idx*psize)) masked_val

      let write_reg_predicate r v ii =
        let pr = match r with
        | AArch64Base.Preg(_,_) -> r
        | _ -> assert false in
          let location = A.Location_reg (ii.A.proc,pr) in
          M.write_loc (mk_write MachSize.S128 Annot.N aexp Access.REG v) location ii

      let get_predicate_last pred psize idx =
        predicate_getlane pred idx psize
        >>= M.op Op.And AArch64.one_promoted
        >>= M.op Op.Ne AArch64.zero_promoted

      let get_predicate_any pred psize nelem =
        let mask idx =
          V.op1 (Op.LeftShift (idx*psize)) (AArch64.predicate_mask psize) in
        let ops = List.map mask (Misc.interval 0 nelem) in
        let allmask =
          List.fold_right (V.op Op.Or) ops AArch64.zero_promoted in
        M.op Op.And pred allmask >>= fun all ->
        M.op Op.Ne all AArch64.zero_promoted

      let scalable_esize r = match r with
      | AArch64Base.ZAreg (_,_,esize)
      | AArch64Base.Zreg (_,esize) -> esize
      | _ -> assert false

      let scalable_nelem r = match r with
      | AArch64Base.ZAreg (_,_,esize)
      | AArch64Base.Zreg (_,esize) -> scalable_nbits / esize
      | _ -> assert false

      let read_reg_scalable port r ii =
        let vr = match r with
        | AArch64Base.Zreg _ -> r
        | _ -> assert false in
          let location = A.Location_reg (ii.A.proc,vr) in
          M.read_loc port (mk_read MachSize.S128 Annot.N aexp) location ii

      let scalable_setlane old_val idx esize v =
        let mask =
          V.op1 (Op.LeftShift (idx*esize)) (AArch64.scalable_mask esize) in
        let invert = V.op1 Op.Inv mask in
        M.op1 (Op.LeftShift (idx*esize)) v >>= fun new_val ->
        M.op Op.And invert old_val >>|
        M.op Op.And mask new_val >>= fun (v1,v2) ->
        M.op Op.Or v1 v2

      let scalable_getlane cur_val idx esize =
        let mask = V.op1 (Op.LeftShift (idx*esize)) (AArch64.scalable_mask esize) in
        M.op Op.And mask cur_val >>= fun masked_val ->
        M.op1 (Op.LogicalRightShift (idx*esize)) masked_val

      let rec scalable_replicate old_val nelem esize v = match nelem with
      | 0 -> M.unitT old_val
      | _ ->
        scalable_setlane old_val (nelem-1) esize v >>= fun old_val ->
        scalable_replicate old_val (nelem-1) esize v

      let write_reg_scalable_sz sz r v ii =
        let pr = match r with
        | AArch64Base.Zreg(_,_) -> r
        | _ -> assert false in
        (* Clear unused register bits (zero extend) *)
          M.op1 (Op.Mask sz) v >>= fun v ->
          let location = A.Location_reg (ii.A.proc,pr) in
          M.write_loc (mk_write MachSize.S128 Annot.N aexp Access.REG v) location ii

      let write_reg_scalable = write_reg_scalable_sz MachSize.S128

      (* ZA offset, in bits, see ARM ARM B.1.4.10 "ZA tile access" *)
      let za_getoffset tile slice idx esize =
        let esize_to_shift = function
          | 8 -> 0
          | 16 -> 1
          | 32 -> 2
          | 64 -> 3
          | 128 -> 4
          | _ -> assert false in
        let shift = esize_to_shift esize in
        let mk_shift k = M.op1 (Op.LeftShift k) in
          begin
            begin
              mk_shift shift slice >>=
              M.add (V.intToV tile) >>=
              M.op Op.Mul (V.intToV scalable_nbits)
            end >>|
            mk_shift (shift+3) idx
          end >>= fun (base,idx) -> M.add base idx

      let za_getoffset_dir dir tile slice idx esize =
        match dir with
        | AArch64Base.Horizontal -> za_getoffset tile slice idx esize
        | AArch64Base.Vertical -> za_getoffset tile idx slice esize

      let za_getlane cur_val tile slice idx esize =
        let mask = AArch64.scalable_mask esize in
        za_getoffset tile slice idx esize >>= fun amount ->
          M.op Op.ShiftLeft mask amount >>= fun mask ->
            M.op Op.And mask cur_val >>= fun masked_val ->
              M.op Op.ShiftRight masked_val amount


      let za_getlane_dir dir cur_val tile slice idx esize =
        match dir with
        | AArch64Base.Horizontal -> za_getlane cur_val tile slice idx esize
        | AArch64Base.Vertical -> za_getlane cur_val tile idx slice esize

      let za_setlane old_val tile slice idx esize v =
        let mask = AArch64.scalable_mask esize in
        za_getoffset tile slice idx esize >>= fun amount ->
          M.op Op.ShiftLeft mask amount >>= fun mask ->
            M.op1 Op.Inv mask >>= fun invert ->
              M.op Op.And invert old_val >>|
                (M.op Op.ShiftLeft v amount >>= fun new_val ->
                  M.op Op.And mask new_val) >>= fun (v1,v2) ->
                    M.op Op.Or v1 v2

      let za_setlane_dir dir old_val tile slice idx esize v =
        match dir with
        | AArch64Base.Horizontal -> za_setlane old_val tile slice idx esize v
        | AArch64Base.Vertical -> za_setlane old_val tile idx slice esize v

      let read_reg_za r ii =
        let vr = match r with
        | AArch64Base.ZAreg _ -> r
        | _ -> assert false in
          let location = A.Location_reg (ii.A.proc,vr) in
          M.read_loc Port.No (mk_read MachSize.S128 Annot.N aexp) location ii

      let write_reg_za_sz sz r v ii =
        let pr = match r with
        | AArch64Base.ZAreg(_,_,_) -> r
        | _ -> assert false in
        (* Clear unused register bits (zero extend) *)
          M.op1 (Op.Mask sz) v >>= fun v ->
          let location = A.Location_reg (ii.A.proc,pr) in
          M.write_loc (mk_write MachSize.S128 Annot.N aexp Access.REG v) location ii

      let write_reg_za = write_reg_za_sz MachSize.S128

      let write_reg_scalable_rep r v ii =
        let nelem = scalable_nelem r in
        let esize = scalable_esize r in
        scalable_replicate v nelem esize v >>= fun new_val ->
          write_reg_scalable r new_val ii

      let do_write_reg_sz mop sz r v ii = match r with
      | AArch64.ZR -> M.unitT ()
      | _ -> match sz with
        | MachSize.S128 -> write_reg_morello r v ii
        | MachSize.Quad when not morello -> write_reg r v ii
        | MachSize.Quad|MachSize.Word|MachSize.Short|MachSize.Byte ->
            mop sz v >>= fun v -> write_reg r v ii

      let write_reg_sz = do_write_reg_sz uxt_op

      let write_reg_sz_dest sz r v ii =
        write_reg_sz sz r v ii >>= fun () -> M.unitT v

      let write_reg_op op sz r v ii =
        match r with
        | AArch64.ZR -> M.unitT ()
        | _ ->
           match sz with
           | MachSize.S128 -> write_reg_morello r v ii
           | MachSize.Quad|MachSize.Word|MachSize.Short|MachSize.Byte ->
              op v >>= fun v -> write_reg r v ii

      let write_reg_sz_non_mixed =
        if mixed then fun _sz -> write_reg
        else write_reg_sz

(* Emit commit event *)
      let commit_bcc ii = M.mk_singleton_es (Act.Commit (Act.Bcc,None)) ii
      and commit_pred_txt txt ii =
        M.mk_singleton_es (Act.Commit (Act.Pred,txt)) ii

      let commit_pred ii = commit_pred_txt None ii

(* Fence *)
      let create_barrier b ii = M.mk_singleton_es (Act.Barrier b) ii

(* Page tables and TLBs *)
      let inv_loc op loc ii =
        let oloc = if A.TLBI.inv_all op then None else Some loc in
        M.mk_singleton_es (Act.Inv (op,oloc)) ii

(* Neon size *)
      let neon_esize r = match r with
      | AArch64Base.Vreg (_,(_,esize)) -> esize
      | _ -> assert false

      let neon_nelem r = match r with
      | AArch64Base.Vreg (_,(nelem,_)) -> nelem
      | _ -> assert false

      let neon_sz r =
        let size = match r with
        | AArch64Base.Vreg(_,(0,esize)) -> esize
        | AArch64Base.Vreg(_,(nelem,esize)) -> nelem * esize
        | _ -> assert false in
        match size with
          | 64 -> MachSize.Quad
          | 128 -> MachSize.S128
          | _ -> assert false

      let neon_sz_k var = let open AArch64Base in
      match var with
      | VSIMD8   -> (V.intToV 1)
      | VSIMD16  -> (V.intToV 2)
      | VSIMD32  -> (V.intToV 4)
      | VSIMD64  -> (V.intToV 8)
      | VSIMD128 -> (V.intToV 16)

(******************)
(* Memory Tagging *)
(******************)


(* Decompose tagged location *)
      let tag_extract a = M.op1 Op.TagExtract a
      let loc_extract a = M.op1 Op.LocExtract a

(*  Low level tag access *)
      let do_read_tag a ii =
        M.read_loc Port.No
          (fun loc v -> access_ord Dir.R loc v Access.TAG)
          (A.Location_global a) ii
      and do_read_tag_nexp a ii =
        M.read_loc Port.No
          (fun loc v -> access_anexp AArch64.nexp_annot Dir.R loc v Access.TAG)
          (A.Location_global a) ii
      and do_write_tag a v ii =
        let loc = A.Location_global a in
        M.mk_singleton_es
          (access_ord Dir.W loc v Access.TAG)
          ii

      let do_read_morello_tag a ii =
        M.add_atomic_tag_read (M.unitT M.A.V.one) a
          (fun loc v -> Act.tag_access quad Dir.R loc v) ii >>= fun tagged ->
          M.op1 Op.CapaGetTag tagged
      and do_write_morello_tag a v ii =
        M.add_atomic_tag_write (M.unitT ()) a v
          (fun loc v -> Act.tag_access quad Dir.W loc v) ii

(* Read tag from memory *)
      let read_tag_mem a ii =
        M.op1 Op.TagLoc a >>= fun atag -> do_read_tag_nexp atag ii

(*******************)
(* Memory accesses *)
(*******************)

     (* Tag checking, MTE *)

      let delayed_check_tags a_virt a_phy ma ii m1 m2 =
        let (+++) = M.data_input_union in
        let rtag  =
          read_tag_mem (match a_phy with None -> a_virt | Some a -> a) ii in
        let commit =  commit_pred_txt (Some "color") ii in
        let choice c ma = M.choiceT c (m1 ma) (m2 ma) in
        let m =
          rtag +++ fun tag1 -> tag_extract a_virt +++ fun tag2 ->
          M.op Op.Eq tag1 tag2 in
        let m =
          let (>>=) = match a_phy with None -> (+++) | Some _ -> (>>=) in
          m >>= fun cond -> commit +++ fun _ -> M.unitT cond in
        M.delay_kont "check_tags" m
          (fun c m ->
            let ma = (* NB output to initial ma *)
              match a_phy with
              | None ->
                if pac
                then ma >>*== fun a -> m >>== fun _ -> loc_extract a
                else ma >>== fun a -> m >>== fun _ -> loc_extract a
              | Some _ ->
                M.bind_ctrldata ma (fun a -> m >>== fun _ -> M.unitT a) in
            choice c ma)

      (* Tag checking Morello *)
      let do_append_commit ma txt ii =
        ma >>== fun a -> commit_pred_txt txt ii >>= fun () -> M.unitT a

      let mzero = M.unitT M.A.V.zero
      let mzero_promoted = mzero >>= promote

      let check_morello_tag a ma mv mok mfault =
        M.op1 Op.CapaGetTag a >>= fun x ->
        M.op Op.Ne x V.zero >>= fun cond ->
        M.choiceT cond (mok ma mv) (mfault ma mzero)

      let check_morello_sealed a ma mv mok mfault =
        M.op1 Op.CheckSealed a >>= fun x ->
        M.op Op.Ne x V.zero >>= fun cond ->
        M.choiceT cond (mfault ma mzero) (mok ma mv)


 (* Semantics has changed, no ctrl-dep on mv *)
      let check_morello_perms a ma mv perms mok mfault =
        M.delay_kont "morello_perms"
          mv
          (fun v mv ->
            let v =
              if String.contains perms 'w' && String.contains perms 'c'
              then v else M.A.V.zero in
            M.op (Op.CheckPerms perms) a v >>= fun cond ->
            M.choiceT cond (mok ma mv) (mfault ma mv))

      let process_read_capability sz a m ii =
        match sz with
        | MachSize.S128 ->
            (M.op1 Op.CapaStrip a >>= fun a ->
             M.add_atomic_tag_read (m a) a
               (fun loc v -> Act.tag_access quad Dir.R loc v) ii)
            >>= fun v -> M.op Op.SquashMutable a v
        | _ -> M.op1 Op.CapaStrip a >>= fun a -> m a >>= fun v -> M.op Op.CapaSetTag v V.zero

(****************)
(* PTW checking *)
(****************)

(* Group pteval components together *)

      type ipte = {
        oa_v : V.v;
        af_v : V.v;
        db_v : V.v;
        dbm_v : V.v;
        valid_v : V.v;
        el0_v : V.v;
        tagged_v : V.v;
        x_v : V.v;
      }

      let arch_op1 op = M.op1 (Op.ArchOp1 op)

      let extract_af v = arch_op1 AArch64Op.AF v
      let extract_db v = arch_op1 AArch64Op.DB v
      let extract_dbm v = arch_op1 AArch64Op.DBM v
      let extract_valid v = arch_op1 AArch64Op.Valid v
      let extract_el0 v = arch_op1 AArch64Op.EL0 v
      let extract_x v = arch_op1 AArch64Op.X v
      let extract_oa v = arch_op1 AArch64Op.OA v
      let extract_tagged v = arch_op1 AArch64Op.Tagged v

      let mextract_whole_pte_val an nexp a_pte iiid domain =
        (M.do_read_loc Port.No
           (fun loc v ->
             Act.Access (Dir.R,loc,v,an,nexp,quad,Access.PTE domain))
           (A.Location_global a_pte) iiid)

      and write_whole_pte_val an explicit a_pte v iiid domain =
        M.do_write_loc
          (mk_write quad an explicit (Access.PTE domain) v)
          (A.Location_global a_pte) iiid


      let op_of_set =
        let open AArch64Explicit in
        function
        | AF -> AArch64Op.SetAF
        | DB -> AArch64Op.SetDB
        | IFetch|Other|AFDB|GCS -> assert false

      let do_test_and_set_bit v combine cond set a_pte iiid domain =
        let nexp = AArch64Explicit.NExp set in
        mextract_whole_pte_val Annot.X nexp a_pte iiid domain >>= fun pte_v ->
        (M.eqT pte_v v >>| cond pte_v) >>*= fun ((),c) ->
        combine c
            (arch_op1 (op_of_set set) pte_v >>= fun v ->
             write_whole_pte_val Annot.X nexp a_pte v iiid domain)
            (M.unitT ())

      let test_and_set_bit_succeeds v cond =
        do_test_and_set_bit v (fun c m _ -> M.assertT c m) cond

      let bit_is_zero op v = arch_op1 op v >>= is_zero
      let bit_is_not_zero op v = arch_op1 op v >>= is_not_zero
      let m_op op m1 m2 = (m1 >>| m2) >>= fun (v1,v2) -> M.op op v1 v2

      let do_set_bit an a_pte pte_v ii domain =
        let nexp = AArch64Explicit.NExp an in
        arch_op1 (op_of_set an) pte_v >>= fun v ->
        write_whole_pte_val Annot.X nexp a_pte v (E.IdSome ii) domain

      let set_af a_pte pte_v ii domain =
        do_set_bit AArch64Explicit.AF a_pte pte_v ii domain

      let set_afdb a_pte pte_v ii domain =
        let nexp = AArch64Explicit.NExp AArch64Explicit.AFDB in
        arch_op1 (AArch64Op.SetAF) pte_v >>= arch_op1 (AArch64Op.SetDB) >>= fun v ->
        write_whole_pte_val Annot.X nexp a_pte v (E.IdSome ii) domain

      let cond_af v =
        m_op Op.And
          (bit_is_zero AArch64Op.AF v) (bit_is_not_zero AArch64Op.Valid v)

      let test_and_set_af_succeeds value =
        test_and_set_bit_succeeds value cond_af AArch64Explicit.AF

      let mextract_pte_vals pte_v =
        (extract_oa pte_v >>|
        extract_el0 pte_v >>|
        extract_valid pte_v >>|
        extract_af pte_v >>|
        extract_db pte_v >>|
        extract_dbm pte_v >>|
        extract_tagged pte_v >>|
        extract_x pte_v) >>=
        (fun (((((((oa_v,el0_v),valid_v),af_v),db_v),dbm_v),tagged_v),x_v) ->
          M.unitT {oa_v; af_v; db_v; dbm_v; valid_v; el0_v; tagged_v; x_v})

      let get_oa a_virt mpte =
        (M.op1 Op.Offset a_virt >>| mpte)
        >>= fun (o,(_,ipte)) -> M.add ipte.oa_v o

(************************************************)
(* Add commit events, when commanded by options *)
(************************************************)


      let append_commit ma txt ii =
        if is_branching then do_append_commit ma txt ii else ma

      let do_insert_commit m1 m2 ii =
      (* Notice the complex dependency >>*==
         from branch to instructions events *)
        m1 >>= fun a -> commit_pred ii >>*== fun _ -> m2 a

      let do_insert_commit_to_fault m1 m2 txt ii =
        (* Dependencies to fault are simple: Rpte -data-> Branch -> Fault *)
        M.bind_data_to_minimals m1
          (fun a -> commit_pred_txt txt ii >>*= fun () -> m2 a)

      let insert_commit_to_fault m1 m2 txt ii =
        if is_branching || morello then do_insert_commit_to_fault m1 m2 txt ii
        else m1 >>*= m2 (* Direct control dependency to fault *)


(************)
(* Branches *)
(************)

      let v2tgt =
        let open Constant in
        function
        | M.A.V.Val (Symbolic (Virtual {name=Symbol.Label (_, lbl); _})) -> Some (B.Lbl lbl)
        | M.A.V.Val (Concrete i) -> Some (B.Addr (M.A.V.Cst.Scalar.to_int i))
        | _ -> None

      let do_indirect_jump test bds i ii v =
        match  v2tgt v with
        | Some tgt ->
          commit_bcc ii
          >>= fun () -> M.unitT (B.Jump (tgt,bds))
        | None ->
           match v with
           | M.A.V.Var(_) as v ->
              let lbls = get_exported_labels test in
              if Label.Full.Set.is_empty lbls  then begin
                if C.variant Variant.Telechat then M.unitT () >>! B.Exit
                else
                  Warn.fatal "Could find no potential target for indirect branch %s \
                    (potential targets are statically known labels)" (AArch64.dump_instruction i)
                end
              else
                commit_bcc ii
                >>= fun () -> B.indirectBranchT v lbls bds
        | _ -> Warn.fatal
            "illegal argument for the indirect branch instruction %s \
            (must be a label)" (AArch64.dump_instruction i)

      let get_link_addr test ii =
        let lbl =
          let a = ii.A.addr + 4 in
          let lbls = test.Test_herd.entry_points a in
          Label.norm lbls in
        match lbl with
        | Some l -> ii.A.addr2v ii.A.proc l
        | None ->  V.intToV (ii.A.addr + 4)

      let get_instr_label proc ii =
        match Label.norm ii.A.labels with
        | Some hd -> ii.A.addr2v proc hd
        | None -> V.intToV ii.A.addr

(******************)
(* Checking flags *)
(******************)

(* With choice operator *)
      let do_check_cond m m_cond k1 k2 =
        M.delay_kont "1"
          (m >>= fun (_,pte_v as p) ->
           m_cond pte_v >>= fun c -> M.unitT (c,p))
          (fun (c,p) m ->
            let m = m >>= fun _ -> M.unitT p in
            M.choiceT c (k1 m) (k2 m))

        (* Summary of access flag and dirty bit management.

          * Without HW-management (on old CPUs, or where TCR_ELx.{HA,HD} == {0,0}):

          A load/store to x where pte_x has the access flag clear will raise an
          Access flag fault

          A store to x where pte_x has the dirty bit clear will raise
          a permission fault

          and SW is expected to deal with this by updating the translation tables with
          explicit stores or atomics

          * With HW management (i.e. when ARMv8.1-TTHM is implemented) where TCR_ELx.HA = 1:
          A load/store to x where pte_x has the access flag clear results in the MMU
          updating the translation table entry to set the access flag, and continuing
          without a fault.

          A store where pte_x has the dirty bit clear will raise a permission fault.

          * With HW management (i.e. when ARMv8.1-TTHM is implemented) where TCR_ELx.{HA,HD} == {1,1}:
          A load/store to x where pte_x has the access flag clear results in the
          MMU updating the translation table entry to set the access flag, and continuing
          without a fault.

          A store to x where pte_x has the dirty bit clear and also has DBM clear
          will raise a permission fault

          A store to x where pte_x has the dirty bit clear and has DBM set results in the
          MMU updating the translation table entry to set the dirty bit, and continuing
          without a fault.

          Notice: The dirty bit correspond to HW level write permission in PTE's.
          Hence, in simple (stage 1) case, we have AP[2] == 0b1 for clean,
          and AP[2] == 0b0 for dirty, with AP[2] == 0b0 being more directly "writable".

         *)

      (*
       * Reading PTE from EL0 will yield a fault,
       * check perfomed early in standard
       * (ie non-pte2) mode.
       *)
       

      let set_elr_el1 v ii =
        write_reg AArch64Base.elr_el1 v ii
      and set_esr_el1 v ii =
        write_reg AArch64Base.esr_el1 v ii

      (* Emit fault event and set link register. *)
      let emit_fault a ma dir an ft msg ii =
        let lbl_v = get_instr_label ii.A.proc ii in
        insert_commit_to_fault ma
          (fun _ ->
             set_elr_el1 lbl_v ii
             >>|
             mk_fault a dir an ii ft msg) None ii
        >>!  B.fault [AArch64Base.elr_el1, lbl_v]

      (* Specific fault when accessing PTE from EL0. *)
      let mk_pte_fault a ma dir an ii domain =
        let open FaultType.AArch64 in
        let ft = Some (MMU (domain, Permission))
        and msg = Some "EL0" in
        emit_fault (Some a) ma dir an ft msg ii

      (* Return if a PAC field is canonical *)
      let check_canonical a =
        M.op1 (Op.ArchOp1 AArch64Op.MakeCanonical) a >>= is_eq a

      let check_ptw proc dir updatedb is_tag a_virt ma an ii mdirect mok mfault domain =

        let is_el0  = List.exists (Proc.equal proc) TopConf.procs_user in

        let check_el0 m =
          (* Handler runs at level more priviledged than EL0 *)
          if not ii.A.in_handler && is_el0 then
               fun pte_v -> m_op Op.Or (is_zero pte_v.el0_v) (m pte_v)
             else m in
        let execute_check cond =
          match domain with
          | DISide.Instr ->
              fun pte_v ->
                m_op Op.Or (cond pte_v) (is_zero pte_v.x_v)
          | _ -> cond in

        let open DirtyBit in
        let tthm = dirty.tthm proc
        and ha = dirty.ha proc
        and hd = dirty.hd proc in
        let ha = ha || hd in (* As far as we know hd => ha *)
        let mfault (_,ipte) m =
          let open FaultType.AArch64 in
          let open DISide in
          let transl_fault = M.unitT (Some (MMU (domain, Translation))) in
          let perm_fault = M.unitT (Some (MMU (domain, Permission))) in
          let af_fault = M.unitT (Some (MMU (domain, AccessFlag))) in
          let perm =
            match domain with
            | Instr ->
                (is_zero ipte.x_v) >>=
                  fun x ->
                    M.choiceT x perm_fault perm_fault
            | _ -> perm_fault in
          let af =
            if ha then perm
            else
              (is_zero ipte.af_v) >>=
                fun af ->
                  M.choiceT af af_fault perm in
          (is_zero ipte.valid_v) >>=
            fun v ->
              M.choiceT v transl_fault af >>= fun t ->
              mfault (get_oa a_virt m) a_virt t
        and mok (pte_v,ipte) a_pte m a =
          let m =
            let msg =
              match dir with
              | Dir.W ->
                 if hd then
                   "valid:1 && (db:1 || dbm:1 && hd)"
                 else if ha then
                   "valid:1 && db:1"
                 else
                   "valid:1 && af:1 && db:1"
              | Dir.R ->
                 if ha then "valid:1"
                 else "valid:1 && af:1" in
            let prefix = if is_tag then "Tag, " else "Data, " in
            let msg = if memtag then prefix ^ msg else msg in
            let m = append_commit m (Some msg) ii in
            let add_setbits cond txt set no =
              cond >>= fun c ->
              M.choiceT c
                (m >>**==
                   (fun _ ->
                     commit_pred_txt (Some txt) ii >>*=
                       fun _ -> set a_pte pte_v ii domain)
                 >>== fun () -> M.unitT (pte_v,ipte))
               no in
            let add_setbits_db ipte m =
              add_setbits
                (m_op Op.Or (is_zero ipte.af_v) (is_zero ipte.db_v))
                "af:0 || db:0"
                set_afdb m in
            let add_setbits_af ipte m =
              add_setbits (is_zero ipte.af_v) "af:0" set_af m in
            (* Write or failed CAS with no write, but with a db update *)
            if hd && updatedb then
              add_setbits_db ipte m
            else if ha then
              add_setbits_af ipte m
            else m in
          mok m a in


(* Action on case of page table access.
   Delay is used so as to have correct dependencies,
   getting content of PTE by anticipation. *)
        let mvirt = begin
          M.delay_kont "3"
            begin
              let kont _ = M.op1 Op.PTELoc a_virt >>= fun a_pte ->
                  let an,nexp =
                    if hd then (* Atomic accesses, tagged with updated bits *)
                      Annot.X,AArch64Explicit.NExp AArch64Explicit.AFDB
                    else if ha then
                      Annot.X,AArch64Explicit.NExp AArch64Explicit.AF
                    else
                      (* Ordinary non-explicit access *)
                      Annot.N,AArch64.nexp_annot in
                  mextract_whole_pte_val
                    an nexp a_pte (E.IdSome ii) domain >>== fun pte_v ->
                  (mextract_pte_vals pte_v) >>= fun ipte ->
                  M.unitT ((pte_v,ipte),a_pte)
                in
              if pac then M.bind_ctrldata ma kont else ma >>= kont
            end
          (fun (pair_pte,a_pte) ma -> (* now we have PTE content *)
            (* Monad will carry changing internal pte value *)
            let ma = ma >>= fun (p,_) -> M.unitT p in
            (* wrapping of success/failure continuations,
               only pte value may have changed *)
            let mok ma = mok pair_pte a_pte ma a_virt
(* a_virt was (if pte2 then a_virt else pte_v.oa_v), why? *)
            and mno ma =  mfault pair_pte ma in
            let check_cond cond =
              do_check_cond ma (check_el0 cond) mno mok in

            if (not tthm || (tthm && (not ha && not hd))) then
            (* No HW management *)
              let cond_R pte_v =
                m_op Op.Or (is_zero pte_v.valid_v) (is_zero pte_v.af_v) in
              let cond = match dir with (* No mercy, check all flags *)
              | Dir.R -> cond_R
              | Dir.W ->
                  fun pte_v ->
                    m_op Op.Or (cond_R pte_v) (is_zero pte_v.db_v) in
              let cond = execute_check cond in
              check_cond cond
            else if (tthm && ha && not hd) then (* HW managment of AF *)
              let cond = match dir with (* Do not check AF *)
              | Dir.R -> fun pte_v -> is_zero pte_v.valid_v
              | Dir.W ->
                  fun pte_v ->
                    m_op Op.Or (is_zero pte_v.valid_v) (is_zero pte_v.db_v) in
              let cond = execute_check cond in
              check_cond cond
            else (* HW management of AF and DB *)
              let cond = match dir with (* Do not check AF *)
              | Dir.R -> fun pte_v -> is_zero pte_v.valid_v
              | Dir.W ->
(* Check DB when dirty bit management disabled for this page *)
                  fun pte_v ->
                    m_op Op.Or
                      (is_zero pte_v.valid_v)
                      (m_op Op.And
                         (is_zero pte_v.db_v) (is_zero pte_v.dbm_v)) in
              let cond = execute_check cond in
              check_cond cond)
          end in
        if pte2 then  mvirt
        else begin
          let mdirect =
            (* Non-virtual accesses are disallowed from EL0.
               For instance, user code cannot access the page table. *)
            if is_el0 then mk_pte_fault a_virt ma dir an ii domain
            else mdirect in
          M.op1 Op.IsVirtual a_virt >>= fun cond ->
          M.choiceT cond mvirt mdirect
        end
(* Read memory, return value read *)
      let do_read_mem_ret sz an anexp ac a ii =
        let m a =
          if mixed then begin
              Mixed.read_mixed Port.No sz (fun sz -> mk_read sz an anexp) a ii
            end else begin
              let mk_act loc v =  Act.Access (Dir.R,loc,v,an,anexp,sz,ac) in
              let loc = A.Location_global a in
              M.read_loc Port.No mk_act loc ii
            end in
        if morello then process_read_capability sz a m ii
        else m a

(* Save value read in register rd *)
      let do_read_mem_op op sz an anexp ac rd a ii =
        do_read_mem_ret sz an anexp ac a ii
        >>= fun v -> write_reg_op op sz rd v ii
        >>= fun () -> B.nextT

      let do_read_mem sz  = do_read_mem_op (uxt_op sz) sz

      let read_mem_acquire sz = do_read_mem sz Annot.A
      let read_mem_acquire_pc sz = do_read_mem sz Annot.Q

      let read_mem_reserve sz an anexp ac rd a ii =
        let m a =
          (write_reg AArch64.ResAddr a ii
           >>| do_read_mem sz an anexp ac rd a ii)
          >>= fun ((),b) -> M.unitT b in
        if morello then
          M.op1 Op.CapaStrip a >>= m
        else
          m a

      (* Post-Indexed load immediate.
         Note: a (effective address) can be physical address,
         while postindex must apply to virtual address. *)
      let read_mem_postindexed a_virt op sz an anexp ac rd rs k a ii =
        let m a =
          begin
            (M.add a_virt (V.intToV k) >>= fun b -> write_reg rs b ii)
            >>| do_read_mem_op op sz an anexp ac rd a ii
          end >>= fun ((),r) -> M.unitT r in
        if morello then
          M.op1 Op.CapaStrip a >>= m
        else
          m a

(* Write *)
      let check_mixed_write_mem sz an anexp ac a v ii =
        if mixed then begin
            Mixed.write_mixed sz
              (fun sz loc v -> mk_write sz an anexp ac v loc)
              a v ii
          end else
          M.write_loc
            (mk_write sz an anexp ac v) (A.Location_global a) ii

      let check_morello_for_write m a v ii =
        if morello then
          M.op1 Op.CapaStrip a >>| M.op1 Op.CapaGetTag v >>= fun (a,tag) ->
          M.add_atomic_tag_write (m a) a tag
            (fun loc v -> Act.tag_access quad Dir.W loc v) ii
        else m a

      let do_write_mem sz an anexp ac a v ii =
        check_morello_for_write
          (fun a -> check_mixed_write_mem sz an anexp ac a v ii)
          a v ii


      let write_mem sz = do_write_mem sz Annot.N

(* Write atomic *)
      let write_mem_atomic sz an anexp ac a v resa ii =
        check_morello_for_write
          (fun a ->
            ((if false (* Write canot succeed without checking reservation. *)
              then M.unitT () else M.assign a resa)
             >>| check_mixed_write_mem sz an anexp ac a v ii)
            >>! ())
        a v ii

(* Page tables and TLBs *)
      let do_inv op a ii = inv_loc op (A.Location_global a) ii

(************************)
(* Conditions and flags *)
(************************)

      (* Force integer representation of booleans.
         Useful for the ASL case *)

      let forceIntBool b = M.op3 Op.If b V.one V.zero

      let condition_holds ii =
        (* Utils for writing formulas:
           Here we do operations on functions that will generate the
           underlying monadic operations. We first define our fake variables,
           then a few logical operations on those.*)
        (* Variables *)
        let n = read_reg Port.No AArch64.(PState PSTATE.N) ii
        and z = read_reg Port.No AArch64.(PState PSTATE.Z) ii
        and c = read_reg Port.No AArch64.(PState PSTATE.C) ii
        and v = read_reg Port.No AArch64.(PState PSTATE.V) ii in
        let true_ = M.unitT V.one in
        (* Operators *)
        (* Note: I use [!a] as a shortcut for [a == 0],
           and [a] as a shortcut for [a == 1]
           (the expended version is the one written in the ARM ARM). *)
        let ( ! ) m = m >>= M.op Op.Eq V.zero in
        let make_op op m1 m2 = m1 >>| m2 >>= fun (v1, v2) -> M.op op v1 v2 in
        let ( == ) m1 m2 = make_op Op.Eq m1 m2 >>= forceIntBool in
        let ( || ) = make_op Op.Or in
        let ( && ) = make_op Op.And in
        (* Note : I use [a <> b] as a shortcut for [!a == b]
           (the expended version is the one written in the ARM ARM). *)
        let ( <> ) = make_op Op.Xor in
        let open AArch64Base in
        (* The real operations, as defined by the ARM ARM. *)
        function
        | NE -> !z
        | EQ -> z
        | GE -> n == v
        | GT -> n == v && !z
        (* Note: for LE, the ARM ARM gives [!(!z && n == v)] here,
           but I've applied De Morgan's law. *)
        | LE -> n <> v || z
        | LT -> n <> v
        | CS -> c
        | CC -> !c
        | MI -> n
        | PL -> !n
        | VS -> v
        | VC -> !v
        | HI -> c && !z
        (* Note: for LS, the ARM ARM gives [!(c && !z)] here,
           but I've applied De Morgan's law. *)
        | LS -> !c || z
        | AL -> true_

(* Arithmetic flags handling *)
      let op_set_flags op ty =
        let open AArch64Base in
        (* Utils for writing formulas
           - We use a base functional type, this surely impacts performance,
             but clarity is improved.
           - We surcharge common operators to use our own functional
             types.
           - The main values come from the three arguments passed to every functions
           - The performance cost is never on operations that do not set flags,
             and mainly on ADDS/SUBS. It consists on an extra monad for every
             variable used.
        *)
        (* Operators *)
        let make_op op v0 v1 = v0 >>| v1 >>= fun (a, b) -> M.op op a b
        and make_op1 op v0 = v0 >>= M.op1 op in
        let ( ! ) = make_op1 Op.Inv
        and ( & ) = make_op Op.And
        and ( || ) = make_op Op.Or
        and ( + ) = make_op Op.Xor
        and ( === ) m v = m >>= M.op Op.Eq v >>= forceIntBool
        and to_integer = M.op Op.ToInteger
        and read_sign_bit =
          let sign_bit = MachSize.nbits (AArch64Base.tr_variant ty) - 1 in
          make_op1 (Op.ReadBit sign_bit)
        in
        let make ~n ~z ~c ~v =
          n >>| z >>| c >>| v >>= fun (((n, z), c), v) -> M.unitT (n, z, c, v)
        in
        (* Computation of nz flags *)
        let compute_z res = res === V.zero in
        let compute_n res = read_sign_bit res in
        (* Operation specific computations
           For specific formulae, see Hacker's Delight, 2-13.*)
        match op with
        | ADD | EOR | EON | ORR | ORN | SUB | AND | ASR | LSR | ROR | LSL | BIC
          ->
            None
        | ANDS | BICS ->
            Some
              (fun res _x _y ->
                let res = M.unitT res in
                make ~n:(compute_n res) ~z:(compute_z res) ~c:mzero ~v:mzero)
        | ADDS ->
            Some
              (fun res x y ->
                let res = M.unitT res
                and x = to_integer x res
                and y = to_integer y V.zero in
                let n = compute_n res
                and z = compute_z res
                and c = ((x & y) || ((x || y) & !res)) |> read_sign_bit
                and v = ((res + x) & (res + y)) |> read_sign_bit in
                make ~n ~z ~c ~v)
        | SUBS ->
            Some
              (fun res x y ->
                (*
                  This is the formula give by Hacker's Delight for the carry in
                  an unsigned subtraction:
                    (!x & y) || ((!x || y) & res)
                  But I use the formula given by Hacker's Delight for the carry
                  in an unsigned addition, with y replaced by !y, as the Arm
                  ARM specifies the subtraction as:
                    x - y := x + !y + 1
                  This gives the following formula, which seems to produce the
                  same results as hardware:
                *)
                let res = M.unitT res
                and x = to_integer x res
                and y = to_integer y V.zero in
                let n = compute_n res
                and z = compute_z res
                and c = ((x & !y) || ((x || !y) & !res)) |> read_sign_bit
                and v = ((x + y) & (res + x)) |> read_sign_bit in
                make ~n ~z ~c ~v)

      let mop3 inst v op rd margs ii =
        let open AArch64Base in
        margs >>=
        begin
          let with_correct_size f arg = f arg >>= mask32 v M.unitT in
          let do_write_reg v = write_reg_dest rd v ii in
          let write_reg_no_flags f arg =
            let without_flags v = M.unitT (v, None) in
            with_correct_size f arg >>= do_write_reg >>= without_flags in
          match v with
          | V128 ->
             check_morello inst;
             let tr_op = function
               | ADD -> Op.CapaAdd
               | SUB -> Op.CapaSub
               | SUBS -> Op.CapaSubs
               | op ->
                  Warn.fatal
                    "Operation '%s' is not available in morello mode"
                    (AArch64.pp_op op) in
                write_reg_no_flags
                  (fun (v1,v2) -> M.op (tr_op op) v1 v2)
          | (V64|V32) ->
             let get_res (v1,v2) =
                match op with
                | ADD | ADDS -> M.add v1 v2
                | EOR -> exclusive_or v1 v2
                | EON -> M.op1 Op.Inv v2 >>= exclusive_or v1
                | ORR -> M.op Op.Or v1 v2
                | ORN -> M.op1 Op.Inv v2 >>= M.op Op.Or v1
                | SUB | SUBS -> subtraction v1 v2
                | AND | ANDS -> M.op Op.And v1 v2
                | ASR -> M.op1 (Op.Mask (tr_variant v)) v2 >>= M.op Op.ASR v1
                | LSR -> M.op1 (Op.Mask (tr_variant v)) v2 >>= M.op Op.Lsr v1
                | LSL -> M.op1 (Op.Mask (tr_variant v)) v2 >>= M.op Op.ShiftLeft v1
                | ROR ->
                   let sz = tr_variant v in
                   let nbits = MachSize.nbits sz in
                   M.op1 (Op.Mask sz) v2 >>= fun v2 ->
                   (M.op Op.Lsr v1 v2
                   >>| (subtraction (V.intToV nbits) v2
                        >>= M.op Op.ShiftLeft v1))
                   >>= fun (v1,v2) -> M.op Op.Or v1 v2
                | BIC | BICS -> M.op Op.AndNot2 v1 v2 in
             match op_set_flags op v with
              | None -> write_reg_no_flags get_res
              | Some get_flags ->
                 let compute_and_write_flags res v1 v2 =
                   get_flags res v1 v2 >>= fun flags ->
                   write_nzcv flags ii >>= fun li ->
                   M.unitT (Some li)
                 in
                 fun (v1, v2 as p) ->
                 with_correct_size get_res p >>= fun res ->
                 do_write_reg res >>| compute_and_write_flags res v1 v2
        end
        >>= fun (v,wo) ->
        begin match wo with
        | None -> B.nextSetT rd v
        | Some ws -> M.unitT (B.Next ((rd,v) :: ws))
        end

(***************************)
(* Various lift functions. *)
(***************************)

(*
  Those fonction take genric 'mop' memory operations,
  and change their behaviour according to variants.
  Most lift function introduce validity checks on
  addresses. Thus the resulting monads will possess
  extra dependencies w.r.t the simple case.
 *)

(* KVM mode *)

      let can_be_pt v =
        match V.as_constant v with
        | None -> true
        | Some c -> Constant.is_pt c

      let can_af0 v =
        (match V.as_constant v with
        | Some (Constant.PteVal p) ->
           p.AArch64PteVal.valid <> 0 &&  p.AArch64PteVal.af = 0
        | _ -> true)

(* Raise a MMU:Translation fault if the virtual address is out of range.
   An address may be out of range if it contains a non-canonical PAC
   field, this functions also make the address syntactically canonical in case of
   a hash collision to construct the corect read-from map, if the address is not
   virtual, it returns `mok ma` *)
      let check_pac_va_range mok ma mfault ii domain =
        let open FaultType.AArch64 in
        let ft = Some (MMU (domain, Translation)) in
        let mok ma =
          let ma = do_append_commit ma (Some "va range") ii in
          mok (ma >>= M.op1 (Op.ArchOp1 AArch64Op.MakeCanonical)) in
        M.delay_kont "range check" ma (fun a ma ->
          check_canonical a >>= fun c ->
          M.choiceT c (mok ma) (mfault ma a ft))

      let lift_kvm _tag dir updatedb mop ma an ii mphy branch domain =
        let mfault ma a ft = emit_fault (Some a) ma dir an ft None ii in
        let maccess a ma =
          check_ptw ii.AArch64.proc dir updatedb false a ma an ii
            (mop (Access.PTE domain) ma |> branch)
            mphy
            mfault
            domain in
        M.delay_kont "6" ma (
          if pte2 then maccess
          else
             fun a ma ->
             match Act.access_of_location_std (A.Location_global a) with
             | Access.VIR|Access.PTE _ when not (A.V.is_instrloc a) ->
                 if pac then check_pac_va_range (maccess a) ma mfault ii domain
                 else maccess a ma
             | Access.VIR when (A.V.is_instrloc a) ->
                 maccess a ma
             | ac ->
                 mop ac ma |> branch
        )

(* Check that the Pointer Authentication Code of a virtual address is canonical
 * before a memory operation. Generate a Branching(pred) effect and an iico_ctrl
 * +iico_data dependency between the event `ma` and `mop` or `mfault`, and an
 * iico_data dependency between `mv` and `mop` in case of a success.
 *)
      let lift_pac_virt mop ma dir an ii branch domain =
        (* Addresses of memory operations must be canonical for the construction
         * of the rf, co and fr maps... *)
        let mfault ma a ft =
          let lbl_v = get_instr_label ii.A.proc ii in
          do_insert_commit_to_fault ma
            (fun _ -> set_elr_el1 lbl_v ii >>| mk_fault (Some a) dir an ii ft None)
            None ii
          >>! B.fault [AArch64Base.elr_el1, lbl_v]
        in
        let mok ma = mop ma |> branch in
        check_pac_va_range mok ma mfault ii domain

      let is_this_reg rA e =
        match E.location_reg_of e with
        | None -> false
        | Some rB -> AArch64.reg_compare rA rB=0

      module MTE = struct
        let lift_fault_async mfault ii ma =
          let set_tfsr = write_reg AArch64Base.tfsr V.one ii in
          ma >>*= fun _ -> (set_tfsr >>| mfault) >>!
            B.Next [AArch64Base.tfsr, V.one]

        let lift_fault_sync mfault ii =
          let lbl_v = get_instr_label ii.A.proc ii in
          let mexc _ =
            mfault >>| set_elr_el1 lbl_v ii >>!
                B.fault [AArch64Base.elr_el1, lbl_v] in
          if has_handler ii then
            fun ma -> M.bind_ctrldata ma mexc
              else
                fun ma -> ma >>*= mexc

        let lift_phy rA dir mop ma an ii mphy =
          let checked_op mpte_d a_virt =
            (* mpte_d - the event structure contains the data op up to the
                branching effect with the outcome of the translation *)
            let mok mtag =
              let mtag = M.short (is_this_reg rA) (E.is_pred_txt (Some "color")) mtag in
              (* mtag - the event structure contains the tag op up to the
                  branching effect with the outcome of the tag comparison *)
              let mtag =
                if is_mte_sync dir then
                  mtag
                else
                  let noact = M.mk_singleton_es Act.NoAction ii in
                  mtag >>*= fun v -> noact >>! v in
              let ma = M.para_bind_output_right mtag (fun _ -> mpte_d) in
              mphy ma a_virt >>= M.ignore >>= B.next1T
            and mno mtag =
              let mtag = M.short (is_this_reg rA) (E.is_pred_txt (Some "color")) mtag in
              (* mtag - the event structure contains the tag op up to the
                  branching effect with the outcome of the tag comparison *)
              let ft = Some FaultType.AArch64.TagCheck in
              let mfault = mk_fault (Some a_virt) dir an ii ft None in
              if is_mte_sync dir then
                let ma = M.para_bind_output_right mtag (fun _ -> mpte_d) in
                lift_fault_sync mfault ii ma
              else
                let mfault = lift_fault_async mfault ii in
                M.para_bind_output_right (mphy mpte_d a_virt) (fun _ -> mfault mtag) in
            let check_tag moa a_virt =
              let do_check_tag a_phy moa =
                delayed_check_tags a_virt (Some a_phy) moa ii mok mno in
              M.delay_kont "check_tag" moa do_check_tag in
            let cond_check_tag mpte_t a_virt =
              (* Only read and check the tag if the PTE of the tag op allows it *)
              M.delay_kont "cond_check_tag" mpte_t @@
                fun (_,ipte) mpte_t ->
                    let moa = get_oa a_virt mpte_t in
                    M.choiceT (ipte.tagged_v) (check_tag moa a_virt) (mok moa)
            and mfault ma a ft =
              let ma =
                let commit _ = commit_pred_txt None ii in
                ma >>= commit in
              let ma = M.para_bind_output_right ma (fun _ -> mpte_d) in
              let lbl_v = get_instr_label ii.A.proc ii in
              ma >>*= fun _ -> set_elr_el1 lbl_v ii >>| mk_fault (Some a) dir an ii ft None >>!
              B.fault [AArch64Base.elr_el1, lbl_v] in
            M.delay_kont "tag_ptw" ma @@ fun a ma ->
            (* tag checks only apply to data *)
            let domain = DISide.Data in
            let mdirect =
              mop (Access.PTE domain) ma >>= M.ignore >>= B.next1T in
            check_ptw ii.AArch64.proc Dir.R false true a ma an ii
              mdirect
              cond_check_tag
              mfault domain in
          fun mpte a_virt -> M.delay_kont "need_check_tag" mpte @@
            fun (_,ipte) mpte -> M.choiceT (ipte.tagged_v)
              (checked_op mpte a_virt) (mphy mpte a_virt)

        let lift_virt mop ma dir an ii branch =
          let do_lift_virt a_virt ma =
            let mm = mop Access.VIR in
            let mok ma =
              let noact = M.mk_singleton_es Act.NoAction ii in
              let ma =
                if is_mte_sync dir then
                  ma
                else
                  ma >>*== (fun a -> noact >>! a) in
              mm ma |> branch
            and mno ma =
              let ft = Some FaultType.AArch64.TagCheck in
              let mfault = mk_fault (Some a_virt) dir an ii ft None in
              if is_mte_sync dir then
                lift_fault_sync mfault ii ma
              else
                let mfault = lift_fault_async mfault ii in
                M.para_bind_output_right (mm ma) (fun _ -> mfault ma) in
            delayed_check_tags a_virt None ma ii mok mno in
          M.delay_kont "MTE.lift_virt" ma do_lift_virt
      end

      let lift_morello mop perms ma mv dir an ii branch =
        let mfault msg ma mv =
          let ft = None in (* FIXME *)
          do_insert_commit
            (ma >>| mv)
            (fun (a,_v) ->
              mk_fault (Some a) dir an ii ft (Some msg)) ii  >>! B.Exit in
        M.delay_kont "morello" ma
          (fun a ma ->
            (* Notice: virtual access only, because morello # kvm *)
            let mok ma mv = mop Access.VIR ma mv in
            check_morello_tag a ma mv
              (fun ma mv ->
                check_morello_sealed a ma mv
                  (fun ma mv ->
                    check_morello_perms a ma mv perms
                      (fun ma mv -> mok ma mv |> branch)
                      (mfault "CapPerms"))
                  (mfault "CapSeal"))
              (mfault "CapTag"))

(* Main choice between supported variants, notice:
   + memtag and kvm can be combined, other variants cannot.
   + mv abstracted for morello sake only
   + ma abstracted for all variants
 *)

      let to_perms str sz = str ^ if sz = MachSize.S128 then "_c" else ""

      let apply_mv mop mv = fun ac ma -> mop ac ma mv

(*
Arguments:
- rA:         Base address register.
- dir:        Access direction (Dir.R for reads, Dir.W for writes).
- updatedb:   If true, update the Dirty Bit in table descriptors.
- checked:    If true, perform memory tagging checks.
- mop:        Function defining the memory operation.
- perms:      Required permissions for Morello.
- ma:         Virtual address to be accessed, represented as the value within the monad.
- mv:         Value to be stored (for write operations), represented as the value in the monad.
- an:         Annotation for the event structure.
- ii:         Instruction metadata.
- branch:     Determines control flow after the translated memory access:
              typically next instruction for data accesses, or no change
              when translating for instruction fetches.
- domain:     Whether the translation is for data or instruction access.
*)
      let do_lift_memop ?tag rA (* Base address register *)
            dir updatedb checked mop perms ma mv an ii branch domain =
        if morello then
          lift_morello mop perms ma mv dir an ii branch
        else
          let mop = apply_mv mop mv in
          if kvm then
            let mphy ma a_virt =
              let ma = get_oa a_virt ma in
              if pte2 then
                M.op1 Op.IsVirtual a_virt >>= fun c ->
                M.choiceT c
                  (mop Access.PHY ma)
                  (mop Access.PHY_PTE ma)
                |> branch
              else
                mop Access.PHY ma |> branch in
            let mphy =
              if checked then MTE.lift_phy rA dir mop ma an ii mphy
              else mphy
            in
            lift_kvm tag dir updatedb mop ma an ii mphy branch domain
          else if checked then
            let mop ma = MTE.lift_virt mop ma dir an ii branch in
            if pac then lift_pac_virt mop ma dir an ii Fun.id domain else mop ma
          else if pac then
            lift_pac_virt (mop Access.VIR) ma dir an ii branch domain
          else
            mop Access.VIR ma |> branch

      let lift_memop ?(tag = "") rA (* Base address register *)
            dir updatedb checked mop perms ma mv an ii =
        let domain = DISide.Data in
        do_lift_memop ~tag rA dir updatedb checked mop perms ma mv an ii
          (fun a -> a >>= M.ignore >>= B.next1T) domain

      (* Address translation instruction *)
      let do_at op rd ii =
        check_kvm "AT";
        let open AArch64Base in
        let dir =
          match op.AArch64Base.AT.rw with
          | AArch64Base.AT.W -> Dir.W
          | AArch64Base.AT.R -> Dir.R in
        let sreg = SysReg AArch64Base.PAR_EL1 in
        let mfault ma _ _ =
            let* a = ma in
            let* v = M.op1 (Op.ArchOp1 AArch64Op.SetF) a in
            let set_par_el1 = write_reg AArch64Base.par_el1 v ii in
            set_par_el1 >>! B.Next [] in
        let mop _ac ma =
            let* a = ma in
            let* v = M.op1 (Op.ArchOp1 AArch64Op.SetOA) a in
            write_reg_dest sreg v ii in
        let mphy ma a_virt =
            let ma = get_oa a_virt ma in
            mop Access.PHY ma >>= M.ignore >>= B.next1T in
        let ma = read_reg_ord rd ii in
        let domain = DISide.Data in
        let maccess a ma =
          check_ptw ii.AArch64.proc dir false false a ma Annot.N ii
            (mop (Access.PTE domain) ma >>= M.ignore >>= B.next1T)
            mphy
            mfault
            domain in
        M.delay_kont "at::check_ptw" ma maccess

      let do_ldr rA sz an mop ma ii =
(* Generic load *)
        let checked = memtag && not C.mte_store_only in
        let ma =
          (* Extract location without a tag from an address *)
          if memtag && C.mte_store_only then
            ma >>= fun a -> loc_extract a
          else ma in
        lift_memop ~tag:"LD" rA Dir.R false checked
          (fun ac ma _mv -> (* value fake here *)
            let memtag_sync = checked && (is_mte_sync Dir.R) in
            if memtag_sync || Access.is_physical ac || pac then
              M.bind_ctrldata ma (mop ac)
            else
              ma >>= mop ac)
          (to_perms "r" sz)
          ma mzero an ii

(* Generic store *)
      let do_str rA mop sz an ma mv ii =
        lift_memop ~tag:"ST" rA Dir.W true memtag
          (fun ac ma mv ->
            let memtag_sync = memtag && (is_mte_sync Dir.W) in
            if pac || memtag_sync || (is_branching && Access.is_physical ac) then begin
              (* additional ctrl dep on address *)
              M.bind_ctrldata_data ma mv
                (fun a v -> mop ac a v ii)
            end else if morello then
              (* additional ctrl dep on address and data *)
              do_insert_commit (ma >>| mv)
                (fun (a,v) -> mop ac a v ii)
                ii
            else
              (ma >>| mv) >>= fun (a,v) -> mop ac a v ii)
          (to_perms "w" sz) ma mv an ii

(***********************)
(* Memory instructions *)
(***********************)

      (* Compute shifts, signed and unsigned extension, etc. *)
      let do_shift op k =
        match k with
        | 0 -> M.unitT
        | _ -> M.op1 op

      let  lsl_op k = do_shift (Op.LeftShift k) k
      and lsr_op sz k v =
        uxt_op sz v >>= do_shift (Op.LogicalRightShift k) k
      and asr_op sz k v =
        sxt_op sz v >>= do_shift (Op.ArithRightShift k) k

      let ror_op sz k v =
        let n = MachSize.nbits sz in
        let m = k mod n in
        begin lsr_op sz m v >>| lsl_op (n-m) v end
        >>= fun (v1,v2) -> M.op Op.Or v1 v2

      let opext_shift sz =
        let open AArch64Base.OpExt in
        function
        | LSL s -> lsl_op s
        | LSR s -> lsr_op sz s
        | ASR s -> asr_op sz s
        | ROR s -> ror_op sz s

      let ext_sext e ko v =
        let k = match ko with None -> 0 | Some k -> k in
        lsl_op k v
        >>=
          M.op1
            begin
              let open AArch64.Ext in
              let open MachSize in
              match e with
              | UXTB -> Op.Mask  Byte
              | UXTH -> Op.Mask Short
              | UXTW -> Op.Mask Word
              | UXTX ->  Op.Mask Quad
              | SXTB -> Op.Sxt  Byte
              | SXTH -> Op.Sxt Short
              | SXTW -> Op.Sxt Word
              | SXTX ->  Op.Sxt Quad
            end

(* Apply a shift as monadic op *)
      let shift sz s =
        let open AArch64Base in
        match s with
          | S_NOEXT   -> M.unitT
          | S_LSL(n)
          | S_MSL(n)
            -> lsl_op n
          | S_LSR(n)  -> lsr_op sz n
          | S_ASR(n)  -> asr_op sz n

      let memext_sext sext s v =
        let open AArch64Base.MemExt in
        let m_shift = lsl_op s
        and m_sext =
          match sext with
          | UXTW -> uxtw_op
          | SXTW -> sxtw_op
          | LSL|SXTX -> M.unitT in
        m_sext v >>= m_shift


(* Complete effective adress computation *)
      let get_ea rs kr s ii =
        let open AArch64Base in
        match kr, s with
        | K 0, S_NOEXT -> (* Immediate with no shift*)
            read_reg_addr rs ii
        | K k, s -> (* Immediate with offset, with shift *)
            read_reg_addr rs ii
            >>= fun v -> shift MachSize.Quad s (V.intToV k)
            >>= M.add v
        | RV(v,r), S_NOEXT -> (* register, no shift *)
            (read_reg_addr rs ii >>| read_reg_addr_sz (tr_variant v) r ii)
            >>= fun (v1,v2) -> M.add v2 v1
        | RV(v,r), s -> (* register, with shift *)
            let sz = tr_variant v in
            (read_reg_addr rs ii >>| read_reg_addr_sz sz r ii)
            >>= fun (v1,v2) -> shift sz s v2
            >>= fun v2 -> M.add v1 v2

      let get_ea_idx rs k ii = get_ea rs (AArch64.K k) AArch64.S_NOEXT ii

      let get_ea_preindexed  rs k ii =
        get_ea_idx rs k ii >>== fun v -> write_reg_dest rs v ii

      let get_ea_reg rs _v ri sext s ii =
        read_reg_addr rs ii >>| (read_reg_addr ri ii >>= memext_sext sext s)
        >>= fun (v1,v2) -> M.add v1 v2

      let add_size a sz = M.add a (V.intToV (MachSize.nbytes sz))

      let post_kr rA addr kr ii =
        let open AArch64Base in
        let get_k = match kr with
        | K k -> M.unitT (V.intToV k)
        | RV(v,rO) -> read_reg_ord_sz (tr_variant v) rO ii in
        get_k >>= fun k ->
        if V.is_var_determined k && V.is_zero k then M.unitT() else
        M.add addr k >>= fun new_addr ->
        write_reg rA new_addr ii

      let ldr0 op sz rd rs e ii =
(* Ordinary loads *)
        let open AArch64Base in
        let open MemExt in
        let mop ac a =
          do_read_mem_op op sz Annot.N aexp ac rd a ii in
        match e with
        | Imm (k,Idx) ->
           do_ldr rs sz Annot.N mop (get_ea_idx rs k ii) ii
        | Imm (k,PreIdx) ->
            do_ldr rs sz Annot.N mop (get_ea_preindexed rs k ii) ii
        | Reg (v,ri,sext,s) ->
           do_ldr rs sz Annot.N mop (get_ea_reg rs v ri sext s ii) ii
        | Imm (k,PostIdx) ->
           (* This case differs signicantly from others,
            * as update of base address register is part
            * of the "read memory" monad, which thus departs
            * from the ordinary `do_read_mem`.
            *)
           M.delay_kont "ldr_postindex"
             (read_reg_addr rs ii)
             (fun a_virt ma ->
               do_ldr rs sz Annot.N
                 (fun ac a ->
                   read_mem_postindexed
                     a_virt op sz Annot.N aexp ac rd rs k a ii)
                 ma ii)
        | _ -> assert false

      let ldr sz = ldr0 (uxt_op sz) sz
      and ldrsw rd rs e ii =
        let sz = MachSize.Word in
        ldr0 (sxt_op sz) sz rd rs e ii
      and ldrs sz var =
        (*
         * Load signed - sign extends to either 32 or 64 bit value
         * load either 8 or 16 bit value (sz),
         * then sign extend based on register size (var)
         *)
        let op = match var with
          | MachSize.Quad -> sxt_op sz
          | MachSize.Word ->
             fun v -> sxt_op sz v >>=  uxt_op MachSize.Word
          | _ -> assert false in
        ldr0 op sz

      module LoadPair
          (Read:
             sig
               val read_mem :
                   MachSize.sz -> AArch64.lannot -> AArch64.explicit -> Access.t ->
                     AArch64.reg -> V.v -> M.A.inst_instance_id -> B.t M.t
             end) =
        struct

          let ldp_wback sz an rd1 rd2 rs k post ii =
            let m =
              M.delay_kont "ldp_wback"
                (read_reg_addr rs ii >>= add_if (not post) k)
                (fun a_virt ma ->
                  do_ldr rs sz Annot.N
                    (fun ac a ->
                      (add_if post k a_virt >>=
                       fun b -> write_reg rs b ii) >>|
                        let (>>|) =
                          match an with
                          | Annot.Q -> assert post ; M.seq_mem
                          | _ -> (>>|) in
                       (Read.read_mem sz an aexp ac rd1 a ii >>|
                       begin
                         add_size a sz >>=
                         fun a -> Read.read_mem sz an aexp ac rd2 a ii
                       end))
                    ma ii >>=
                  fun _ -> add_if post k a_virt >>=
                    fun a -> M.unitT (B.Next [rs,a])) in
            if kvm then M.upOneRW (is_this_reg rs) m
            else m

          let ldp tnt sz rd1 rd2 rs (k,md) ii =
            let an =
              let open AArch64 in
              let open Annot in
              match tnt with
              | (`PaIQ) -> Q
              | (`PaA) -> A
              | (`Pa) -> N
              | (`PaN) -> NTA in
            let open AArch64 in
            match md with
            | Idx ->
                let (>>|) =
                  match an with
                  | Annot.Q -> M.seq_mem
                  | _ -> (>>|) in
                do_ldr rs sz Annot.N
                  (fun ac a ->
                    Read.read_mem sz an aexp ac rd1 a ii >>|
                begin
                  add_size a sz >>=
                  fun a -> Read.read_mem sz an aexp ac rd2 a ii
                end)
                  (get_ea_idx rs k ii) ii
            | PostIdx ->
                ldp_wback sz an rd1 rd2 rs k true ii
            | PreIdx ->
                ldp_wback sz an rd1 rd2 rs k false ii
        end

      let ldp =
        let module LDP =
          LoadPair
            (struct
              let read_mem = do_read_mem
            end) in
        LDP.ldp

      let ldpsw =
        let module LDPSW =
          LoadPair
            (struct
              let read_mem = do_read_mem_op sxtw_op
            end) in
        LDPSW.ldp AArch64.(`Pa) MachSize.Word

      let ldxp sz t rd1 rd2 rs ii =
        let open AArch64 in
        let open Annot in
        let an = match t with XP -> EX | AXP -> EXA in
        do_ldr rs sz an
          (fun ac a ->
            read_mem_reserve sz an aexp ac rd1 a ii >>||
            begin
              add_size a sz >>= fun a ->
              do_read_mem sz an aexp ac rd2 a ii
            end)
          (read_reg_addr rs ii) ii

      and ldar sz t rd rs ii =
        let open AArch64 in
        let an = match t with
        | XX -> Annot.EX
        | AA -> Annot.A
        | AX -> Annot.EXA
        | AQ -> Annot.Q in
        do_ldr rs sz an
          (fun ac a ->
            let read =
              match t with
              | XX -> read_mem_reserve sz Annot.EX
              | AA -> read_mem_acquire sz
              | AX -> read_mem_reserve sz Annot.EXA
              | AQ -> read_mem_acquire_pc sz in
            read aexp ac rd a ii)
          (read_reg_addr rs ii)  ii

      let str_simple sz rs rd m_ea ii =
        do_str rd
          (fun ac a v ii ->
            M.data_input_next
              (M.unitT v)
              (fun v -> do_write_mem sz Annot.N aexp ac a v ii))
          sz Annot.N
          m_ea (read_reg_data_sz sz rs ii) ii

      let str sz rs rd e ii =
        let open AArch64Base in
        let open MemExt in
        match e with
        | Imm (k,Idx) ->
           str_simple sz rs rd  (get_ea_idx rd k ii)  ii
        | Imm (k,PostIdx) ->
           let m =
             M.delay_kont "str_post"
               (read_reg_addr rd ii)
               (fun a_virt ma ->
                 do_str rd
                   (fun ac a v ii ->
                     M.add a_virt (V.intToV k) >>= fun b -> write_reg rd b ii
                     >>|
                     M.data_input_next
                       (M.unitT v)
                       (fun v -> do_write_mem sz Annot.N aexp ac a v ii))
                   sz Annot.N
                   ma (read_reg_data_sz sz rs ii) ii) in
           if kvm then M.upOneRW (is_this_reg rd) m
           else m
        | Imm (k,PreIdx) ->
           str_simple sz rs rd (get_ea_preindexed rd k ii) ii
        | Reg (v,ri,sext,s) ->
            str_simple sz rs rd (get_ea_reg rd v ri sext s ii) ii
        | _ -> assert false


      let stp_wback =
        let (>>>) = M.data_input_next in
        fun sz an rs1 rs2 rd k post ii ->
          let m =
            M.delay_kont "stp_wback"
              (read_reg_addr rd ii >>= add_if (not post) k)
              (fun a_virt ma ->
                do_str rd
                  (fun ac a _ ii ->
                    (add_if post k a_virt >>=
                       fun b -> write_reg rd b ii) >>|
                      let (>>|) =
                        match an with
                        | Annot.L ->
                           assert (not post) ;
                           fun m1 m2 -> M.seq_mem m2 m1
                        | _ -> (>>|) in
                      ((read_reg_data_sz sz rs1 ii >>> fun v ->
                        do_write_mem sz an aexp ac a v ii) >>|
                         (add_size a sz >>= fun a ->
                          read_reg_data_sz sz rs2 ii >>> fun v ->
                          do_write_mem sz an aexp ac a v ii)))
                  sz Annot.N
                  ma (M.unitT V.zero)
                  ii >>=
                  fun _ -> add_if post k a_virt >>=
                  fun a -> M.unitT (B.Next [rd,a])) in
          if kvm then M.upOneRW (is_this_reg rd) m
          else m

      let stp tnt sz rs1 rs2 rd (k,md) ii =
        let an =
          let open AArch64 in
          let open Annot in
          match tnt with
          | (`PaIL) | (`PaL) -> L
          | (`Pa) -> N
          | (`PaN) -> NTA in
        match md with
        | AArch64.Idx ->
            let (>>|) =
              match tnt with
              | AArch64.(`Pa|`PaN|`PaL) -> (>>|)
              | AArch64.(`PaIL) -> M.seq_mem in
            let (>>>) = M.data_input_next in
            do_str rd
              (fun ac a _ ii ->
                (read_reg_data_sz sz rs1 ii >>> fun v ->
                  do_write_mem sz an aexp ac a v ii) >>|
                  (add_size a sz >>= fun a ->
                    read_reg_data_sz sz rs2 ii >>> fun v ->
                      do_write_mem sz an aexp ac a v ii))
              sz Annot.N
              (get_ea_idx rd k ii)
              (M.unitT V.zero)
              ii
        | AArch64.PostIdx ->
            stp_wback sz an rs1 rs2 rd k true ii
        | AArch64.PreIdx ->
            stp_wback sz an rs1 rs2 rd k false ii

      let stlr sz rs rd ii =
        do_str rd (do_write_mem sz Annot.L aexp) sz Annot.L
          (read_reg_addr rd ii) (read_reg_data_sz sz rs ii) ii

      and do_stxr ms mw sz t rr rd ii  =
        let open AArch64Base in
        let an = match t with
          | YY -> Annot.EX
          | LY -> Annot.EXL in
        lift_memop rd Dir.W true memtag
          (fun ac ma mv ->
            let must_fail =
              begin
                let open AArch64 in
                match ii.env.lx_sz with
                | None -> true (* No LoadExcl at all. always fail *)
                | Some szr ->
                   (* Some, must fail when size differ *)
                   not (MachSize.equal szr sz)
              end in
            M.aarch64_store_conditional must_fail
              (read_reg_ord ResAddr ii)
              mv ma
              (write_reg ResAddr V.zero ii)
              (fun v -> write_reg rr v ii)
              (mw an ac))
          (to_perms "w" sz)
          (read_reg_addr rd ii)
          ms an ii

      let stxr sz t rr rs rd ii =
        do_stxr
          (read_reg_ord_sz sz rs ii)
          (fun an ac ea resa v  -> write_mem_atomic sz an aexp ac ea v resa ii)
          sz t rr rd ii

      let stxp sz t rr rs1 rs2 rd ii =
        let (>>>) = M.data_input_next in
        do_stxr
          (M.unitT (V.zero))
          (fun an ac ea resa _ ->
            begin
              (read_reg_ord_sz sz rs1 ii >>> fun v ->
               write_mem_atomic sz an aexp ac ea v resa ii)
              >>||
                (add_size ea sz >>= fun a ->
                 read_reg_ord_sz sz rs2 ii >>> fun v ->
                 check_morello_for_write
                   (fun a ->
                     check_mixed_write_mem sz an aexp ac a v ii) a v ii)
            end >>!  ())
        sz t rr rd ii

(* AMO instructions *)
      let rmw_amo_read sz rmw =
        let open AArch64 in
        let open Annot in
        match rmw with
        | RMW_A|RMW_AL -> do_read_mem_ret sz XA aexp
        | RMW_L|RMW_P  -> do_read_mem_ret sz X aexp

      and rmw_amo_write sz rmw =
        let open AArch64 in
        let open Annot in
        match rmw with
        | RMW_L|RMW_AL -> do_write_mem sz XL aexp
        | RMW_P|RMW_A  -> do_write_mem sz X aexp

      let rmw_to_read rmw =
        let open AArch64 in
        let open Annot in
        match rmw with
        | RMW_P | RMW_L -> N
        | RMW_A | RMW_AL -> A

      let swp sz rmw r1 r2 r3 ii =
        lift_memop r3 Dir.W true (* swp is a write for the purpose of DB *)
          memtag
          (fun ac ma mv ->
            let noret = match r2 with | AArch64.ZR -> true | _ -> false in
            let r2 = mv
            and w2 v = write_reg_sz sz r2 v ii
            and r1 a =
              if noret then do_read_mem_ret sz Annot.NoRet aexp ac a ii
              else rmw_amo_read sz rmw ac a ii
            and w1 a v = rmw_amo_write sz rmw ac a v ii in
            M.swp
              (Access.is_physical ac)
              ma
              r1 r2 w1 w2)
          (to_perms "rw" sz)
          (read_reg_addr r3 ii)
          (read_reg_data_sz sz r1 ii)
          (rmw_to_read rmw)
          ii

      let do_cas_fail_with lift do_wb sz an rn ma mv mop tagcheck ii =
        let action checked ma =
          let do_action updatedb checked ma =
              (* Dir.W would force check for dbm bit:                  *)
              (* - if set then either update or not db bit per R_TXGHB *)
              (* - if unset raise Permission fault                     *)
              lift ~tag:"FAIL" rn Dir.W updatedb checked mop (to_perms "rw" sz) ma mv an ii
          in
          if do_wb then
            do_action true checked ma
          else begin
            (* When there is no writeback, It is IMPLEMENTATION SPECIFIC *)
            (* if there is an update to the dirty bit of the TTD *)
            let proc = ii.AArch64.proc in
            let tthm = dirty.DirtyBit.tthm proc
            and hd = dirty.DirtyBit.hd proc in
            let may_update_db = tthm && hd in
            if may_update_db then
              M.altT (do_action true checked ma) (do_action false checked ma)
            else
              do_action false checked ma
          end
        in

        if tagcheck && C.mte_store_only then
          (* If FEAT_MTE_STORE_ONLY is implemented it is              *)
          (* CONSTRAINED UNPREDICTABLE whether the Tag Check          *)
          (* operation is performed.                                  *)
          M.altT (
            (* No Tag Check *)
            (* Extract location without a tag from an address *)
            let ma = ma >>= fun a -> loc_extract a in
            action false ma
          )(
            (* Tag Check *)
            action true ma
          )
        else
          action memtag ma

      let do_cas_with lift sz an rn ma mv mop_success mop_fail_with_wb mop_fail_no_wb tagcheck ii =
        let do_cas_fail_with_wb = do_cas_fail_with lift true in
        let do_cas_fail_no_wb = do_cas_fail_with lift false in
        M.altT (
          (* CAS succeeds and generates an Explicit Write Effect *)
          (* there must be an update to the dirty bit of the TTD *)
          lift ~tag:"CAS" rn Dir.W true tagcheck mop_success (to_perms "rw" sz) ma mv an ii
        )( (* CAS fails *)
          M.altT (
            (* CAS generates an Explicit Write Effect              *)
            do_cas_fail_with_wb sz an rn ma mv mop_fail_with_wb tagcheck ii
          )(
            (* CAS does not generate an Explicit Write Effect      *)
            do_cas_fail_no_wb sz an rn ma mv mop_fail_no_wb tagcheck ii
          )
        )

      let do_cas = do_cas_with (fun ~tag -> lift_memop ~tag)

      let cas sz rmw rs rt rn ii =
        let an = rmw_to_read rmw in
        let read_rs = read_reg_data_sz sz rs ii
        and write_rs v = write_reg_sz sz rs v ii in
        let noret = match rs with | AArch64.ZR -> true | _ -> false in
        let branch a =
          let cond = Printf.sprintf "[%s]==%d:%s" (V.pp_v a) ii.A.proc (A.pp_reg rs) in
            commit_pred_txt (Some cond) ii in
        let mop_fail_no_wb ac ma _ =
          (* CAS fails, there is no Explicit Write Effect *)
          let read_mem a =
            if noret then do_read_mem_ret sz Annot.NoRet aexp ac a ii
            else do_read_mem_ret sz an aexp ac a ii in
          let noact _ _ = M.mk_singleton_es Act.NoAction ii in
          M.aarch64_cas_no (Access.is_physical ac) ma read_rs write_rs read_mem
            noact branch neqT
        in
        let mop_fail_with_wb ac ma _ =
          (* CAS fails, there is an Explicit Write Effect writing back *)
          (* the value that is already in memory                       *)
          let read_mem a =
            if noret then do_read_mem_ret sz Annot.NoRet aexp ac a ii
            else rmw_amo_read sz rmw ac a ii
          and write_mem a v = rmw_amo_write sz rmw ac a v ii in
          M.aarch64_cas_no (Access.is_physical ac) ma read_rs write_rs
            read_mem write_mem branch neqT
        in
        let mop_success ac ma mv =
          (* CAS succeeds, there is an Explicit Write Effect *)
           (* mv is read new value from reg, not important
              as this code is not executed in morello mode *)
          let read_rt = mv
          and read_mem a =
            if noret then do_read_mem_ret sz Annot.NoRet aexp ac a ii
            else rmw_amo_read sz rmw ac a ii
          and write_mem a v = rmw_amo_write sz rmw ac a v ii in
          M.aarch64_cas_ok (Access.is_physical ac) ma read_rs read_rt write_rs
                                read_mem write_mem branch M.eqT
        in
        let ma = read_reg_addr rn ii
        and mv = read_reg_data_sz sz rt ii in
        do_cas sz an rn ma mv mop_success mop_fail_with_wb mop_fail_no_wb memtag ii

      let casp sz rmw rs1 rs2 rt1 rt2 rn ii =
        let an = rmw_to_read rmw in
        let (>>>) = M.data_input_next in
        let read_rs = read_reg_data_sz sz rs1 ii
          >>| read_reg_data_sz sz rs2 ii
        and write_rs (v1,v2) = write_reg_sz sz rs1 v1 ii
          >>| write_reg_sz sz rs2 v2 ii
          >>= fun _ -> M.unitT ()
        and branch a =
          let cond = Printf.sprintf "[%s]=={%d:%s,%d:%s}" (V.pp_v a)
            ii.A.proc (A.pp_reg rs1) ii.A.proc (A.pp_reg rs2) in
          commit_pred_txt (Some cond) ii in
        let neqp (v1,v2) (x1,x2) =
            is_eq v1 x1 >>| is_eq v2 x2
            >>= fun (b1,b2) -> M.op Op.And b1 b2
            >>= M.eqT V.zero
        and eqp (v1,v2) (x1,x2) =
            M.eqT v1 x1 >>| M.eqT v2 x2
            >>= fun _ -> M.unitT () in
        let mop_fail_no_wb ac ma _ =
          (* CASP fails, there are no Explicit Write Effects *)
          let read_mem a = do_read_mem_ret sz an aexp ac a ii
                >>| (add_size a sz
                     >>= fun a -> do_read_mem_ret sz an aexp ac a ii) in
          let noact _ _ = M.mk_singleton_es Act.NoAction ii in
          M.aarch64_cas_no (Access.is_physical ac) ma read_rs
              write_rs read_mem noact branch neqp
        in
        let mop_fail_with_wb ac ma _ =
          (* CASP fails, there are Explicit Write Effects writing back *)
          (* the value that is already in memory                       *)
          let read_mem a = rmw_amo_read sz rmw ac a ii
                >>| (add_size a sz
                >>= fun a -> rmw_amo_read sz rmw ac a ii)
          and write_mem a (v1,v2) =
              rmw_amo_write sz rmw ac a v1 ii
              >>| (add_size a sz >>= fun a2 ->
                  rmw_amo_write sz rmw ac a2 v2 ii)
              >>= fun _ -> M.unitT () in
          M.aarch64_cas_no (Access.is_physical ac) ma read_rs
              write_rs read_mem write_mem branch neqp
        in
        let mop_success ac ma _ =
          (* CASP succeeds, there are Explicit Write Effects *)
          let read_rt = read_reg_data_sz sz rt1 ii
                >>| read_reg_data_sz sz rt2 ii
          and read_mem a = rmw_amo_read sz rmw ac a ii
                >>| (add_size a sz
                >>= fun a -> rmw_amo_read sz rmw ac a ii)
          and write_mem a (v1,v2) =
              rmw_amo_write sz rmw ac a v1 ii
              >>| (add_size a sz >>= fun a2 ->
                  rmw_amo_write sz rmw ac a2 v2 ii)
              >>= fun _ -> M.unitT () in
          M.aarch64_cas_ok (Access.is_physical ac) ma read_rs
              read_rt write_rs read_mem write_mem branch eqp
        in
        let ma = read_reg_addr rn ii
        and mv = read_reg_data_sz sz rt1 ii >>> fun _ -> read_reg_data_sz sz rt2 ii in
        do_cas sz an rn ma mv mop_success mop_fail_with_wb mop_fail_no_wb memtag ii

      (* Temporary morello variation of CAS *)
      let cas_morello sz rmw rs rt rn ii =
        (* As morello and kvm are incompatible, all accesses are virtual *)
        lift_morello
          (fun ac ma mv ->
            let read_mem sz = rmw_amo_read sz rmw in
            let mrs = read_reg_data_sz sz rs ii in
            let mrt = mv in
            M.delay ma >>| M.delay mrs >>| M.delay mrt
            >>= fun (((_,ma),(_,mrs)),(_,mrt)) ->
            let muncond = ma >>| mrs >>| mrt in
            let mmem = ma >>= fun a -> read_mem sz ac a ii in
            let write_rs mv =
              mv >>= fun v -> write_reg_sz_non_mixed sz rs v ii in
            let branch = fun mrs mmem mavoid m1 m2 ->
              let (++) = M.bind_ctrl_avoid mavoid in
              (mrs >>| mmem >>= fun (rs,mem) -> (M.op Op.Eq rs mem) >>= fun cond ->
                commit_pred ii >>! cond) ++ fun cond ->
                  M.choiceT cond m1 m2 in
            let mop = fun ma mv mmem ->
              let write_mem a v = rmw_amo_write sz rmw ac a v ii in
              M.aarch64_cas_ok_morello ma mv mmem write_mem in
            M.delay mmem >>= fun (_,mmem) ->
            branch mrs mmem (muncond >>| mmem)
              (mop ma mrt mmem)
              (mrt >>! ())
            >>| write_rs mmem)
          (to_perms "rw" sz)
          (read_reg_addr rn ii)
          (read_reg_data_sz sz rt ii)
          Dir.W (rmw_to_read rmw) ii (fun a -> a >>= M.ignore >>= B.next1T)

      let ldop op sz rmw rs rt rn ii =
        let open AArch64 in

        let tr_input = match op with
          |A_SMIN|A_SMAX ->
            (* For int64 signed comparison to work on int32, int16, int8 *)
            sxt_op sz
          |A_ADD|A_EOR|A_SET|A_CLR|A_UMAX|A_UMIN -> M.unitT in

        let an = rmw_to_read rmw in
        lift_memop rn Dir.W true memtag
          (fun ac ma mv ->
            let noret = match rt with | ZR -> true | _ -> false in
            let op = match op with
            | A_ADD -> Op.Add
            | A_EOR -> Op.Xor
            | A_SET -> Op.Or
            | A_CLR -> Op.AndNot2
            | A_SMAX -> Op.Max
            | A_SMIN -> Op.Min
            | A_UMAX -> Op.UMax
            | A_UMIN -> Op.UMin in
            let read_mem =
              if noret then
                fun sz ->
                do_read_mem_ret sz Annot.NoRet aexp ac
              else fun sz -> rmw_amo_read sz rmw ac
            and write_mem = fun sz -> rmw_amo_write sz rmw ac in
            M.amo_strict (Access.is_physical ac) op
              ma
              (fun a -> read_mem sz a ii >>= tr_input) mv
              (fun a v -> write_mem sz a v ii)
              (fun w ->
                if noret then M.unitT ()
                else  write_reg_sz sz rt w ii))
          (to_perms "rw" sz)
          (read_reg_addr rn ii)
          (read_reg_data_sz sz rs ii >>= tr_input)
          an ii

      (* Neon/SVE/SME instructions *)
      let (let>*) = M.bind_control_set_data_input_first
      let (let>=) = M.(>>=)
      let (let<>=) = M.bind_data_to_output

      (* Utility that performes an `N`-bit load as two independent `N/2`-bit
       * loads. Used by 128-bit Neon LDR.
       *
       * This instruction is endianness-aware (i.e. performing an 128-bit
       * load as two 64-bit loads will take the endianness of the CPU into
       * account). This is, indeed, a difference in semantics with Neon
       * with respect to, e.g., `LDR` vs `LD1`. *)
      let do_read_mem_2_ops_ret sz an anexp ac addr1 ii =
        let open MachSize in
        assert (sz != MachSize.Byte);
        let sz_half = MachSize.pred sz in
        (do_read_mem_ret sz_half an anexp ac addr1 ii >>= promote) >>|
        begin
          M.add addr1 (V.intToV (nbytes sz_half)) >>= fun addr2 ->
          do_read_mem_ret sz_half an anexp ac addr2 ii >>= promote
        end >>= fun (v1, v2) ->
        let v_lo, v_hi = match endian with
          (* Because an 128-bit Neon STR is allowed to be broken up into
           * 64-bit loads, this means that we do need to take endianness into
           * account *)
          | Endian.Little -> v1, v2
          | Endian.Big -> v2, v1 in
        M.op1 (Op.LeftShift (nbits sz_half)) v_hi >>= fun v_hi_shifted ->
        M.op Op.Or v_lo v_hi_shifted

      (* Utility that performes an `N`-bit store as two independent `N/2`-bit
       * stores. Used by Neon instructions. *)
      let do_write_mem_2_ops sz an anexp ac addr1 v ii =
        let open MachSize in
        assert (sz != MachSize.Byte);
        let sz_half = MachSize.pred sz in
        let comp_lo = M.op1 (Op.Mask sz_half) v in
        let comp_hi = M.op1 (Op.LogicalRightShift (nbits sz_half)) v in
        let (comp_v1, comp_v2) = match endian with
          (* Because an 128-bit Neon STR is allowed to be broken up into
           * 64-bit loads, this means that we do need to take endianness into
           * account *)
          | Endian.Little -> comp_lo, comp_hi
          | Endian.Big -> comp_hi, comp_lo in
        begin
          comp_v1 >>= demote >>= fun v1 ->
          do_write_mem sz_half an anexp ac addr1 v1 ii
        end >>|
        begin
          M.add addr1 (V.intToV (nbytes sz_half)) >>|
          (comp_v2 >>= demote) >>= fun (addr2, v2) ->
          do_write_mem sz_half an anexp ac addr2 v2 ii
        end

      let write_mem_2_ops sz = do_write_mem_2_ops sz Annot.N

      (* Neon extension, memory accesses return B.Next, as they cannot fail *)
      let do_simd_ldr an sz addr rd ii =
        (* 128-bit Neon LDR/STR and friends are split into two 64-bit
         * single-copy atomic accesses. *)
        let mem_op = begin
          if sz == MachSize.S128 then do_read_mem_2_ops_ret else do_read_mem_ret
        end in
        mem_op sz an aexp Access.VIR addr ii >>= fun v ->
        write_reg_neon_sz sz rd v ii

      let simd_ldr = do_simd_ldr  Annot.N
      let simd_ldar = do_simd_ldr  Annot.Q

      let do_simd_str an sz ma rd ii =
        ma >>|
        read_reg_neon Port.Data rd ii >>= fun (addr,v) ->
        if sz == MachSize.S128 then
          do_write_mem_2_ops sz an aexp Access.VIR addr v ii >>= B.next2T
        else
          demote v >>= fun v ->
          do_write_mem sz an aexp Access.VIR addr v ii >>= B.next1T

      let simd_str = do_simd_str Annot.N
      let simd_stlr = do_simd_str Annot.L

      let simd_str_p sz ma rd rs k ii =
        ma >>|
        read_reg_neon Port.Data rd ii >>= fun (addr,v) ->
        if sz == MachSize.S128 then
          (* 128-bit Neon LDR/STR and friends are split into two 64-bit
           * single-copy atomic accesses. *)
          write_mem_2_ops sz aexp Access.VIR addr v ii >>|
          post_kr rs addr k ii >>= B.next3T
        else
          demote v >>= fun v ->
          write_mem sz aexp Access.VIR addr v ii >>|
          post_kr rs addr k ii >>= B.next2T

      let simd_ldp tnt var addr1 rd1 rd2 ii =
        let an = tnt2annot tnt in
        let open AArch64Base in
        let sz = tr_simd_variant var in
        do_simd_ldr an sz addr1 rd1 ii >>|
        begin
          M.add addr1 (neon_sz_k var) >>= fun addr2 ->
          do_simd_ldr an sz addr2 rd2 ii
        end >>= B.next2T

      let simd_stp tnt var addr1 rd1 rd2 ii =
        let an = tnt2annot tnt in
        let open AArch64Base in
        let sz = tr_simd_variant var in
        if sz == MachSize.S128 then
          (* 128-bit Neon LDR/STR are not single-copy atomic, but they
           * are single-copy atomic for each of the two 64-bit quantities
           * they access. This means that a 2x128-bit LDP/STP with Neon
           * registers results in 4 single-copy atomic accesses. *)
          begin
            read_reg_neon Port.Data rd1 ii >>= fun v1 ->
            do_write_mem_2_ops sz an aexp Access.VIR addr1 v1 ii
          end >>|
          begin
            M.add addr1 (neon_sz_k var) >>|
            read_reg_neon Port.Data rd2 ii >>= fun (addr2, v2) ->
            do_write_mem_2_ops sz an aexp Access.VIR addr2 v2 ii
          end >>= fun ((a, b), (c, d)) -> B.next4T (((a, b), c), d)
        else
          begin
            read_reg_neon Port.Data rd1 ii >>= fun v1 ->
            write_mem sz aexp Access.VIR addr1 v1 ii
          end >>|
          begin
            M.add addr1 (neon_sz_k var) >>|
            read_reg_neon Port.Data rd2 ii >>= fun (addr2, v2) ->
            write_mem sz aexp Access.VIR addr2 v2 ii
          end >>= B.next2T

      let m128 k = promote (V.intToV k)

      let movi_v r k shift ii =
        let open AArch64Base in
        let sz = neon_sz r and
        esize = neon_esize r in
        begin match esize, shift with
        | 8, S_NOEXT | 16, S_NOEXT | 32, S_NOEXT | 64, S_NOEXT | 128, S_NOEXT ->
           m128 k
        | 8, S_LSL(0 as amount)
        | 16, S_LSL(0|8 as amount)
        | 32, S_LSL(0|8|16|24 as amount)
        | 32, S_MSL(8|16 as amount) ->
           m128 k >>= M.op1 (Op.LeftShift amount)
        | _, S_LSL(n) ->
          Warn.fatal
            "illegal shift immediate %d in %d-bit instruction movi"
            n
            esize
        | _, s ->
          Warn.fatal
            "illegal shift operand %s in %d-bit instruction movi"
            (pp_barrel_shift "," s pp_imm)
            esize
        end
          >>= fun v ->  write_reg_neon_rep sz r v ii


      let movi_s var r k ii =
        let open AArch64Base in
        begin match var with
        | VSIMD64 -> m128 k
        | _ ->
          Warn.fatal
          "illegal scalar register size in instruction movi"
        end
          >>= (fun v -> write_reg_neon_sz (tr_simd_variant var) r v ii)

      let sum_elems (v1,v2) = M.add v1 v2

      let simd_add r1 r2 r3 ii =
        let nelem = neon_nelem r1 in
        let esize = neon_esize r1 in
        read_reg_neon Port.No r3 ii >>|
        read_reg_neon Port.No r2 ii >>= fun (v1,v2) ->
          let aux cur_val idx =
            neon_getlane v1 idx esize >>|
            neon_getlane v2 idx esize >>= sum_elems
            >>= fun v -> neon_setlane cur_val idx esize v
          in
          let rec reduce idx op =
            match idx with
            | 0 -> op >>= fun old_val -> aux old_val idx
            | _ -> reduce (idx-1) (op >>= fun old_val -> aux old_val idx)
          in
          reduce (nelem-1) mzero >>= fun v ->
            write_reg_neon r1 v ii

      let addv var r1 r2 ii =
        let open AArch64Base in
        let nelem = neon_nelem r2 in
        let sz = tr_simd_variant var in
        let rec reduce n op =
          match n with
          | 0 -> op >>| read_reg_neon_elem Port.No r2 0 ii >>= sum_elems
          | _ ->
             reduce (n-1)
               (op >>| read_reg_neon_elem Port.No r2 n ii >>= sum_elems)
        in
        reduce (nelem-1) mzero >>=
          fun v -> write_reg_neon_sz sz r1 v ii

      let uaddv var r1 p src ii =
        let nelem = predicate_nelem src in
        let psize = predicate_psize src in
        let esize = scalable_esize src in
        read_reg_predicate p ii >>= fun pred ->
          get_predicate_any pred psize nelem >>= fun any ->
            M.choiceT
            any
            (read_reg_scalable Port.No src ii >>= fun src ->
              let read_active_elem_or_zero idx cur_val =
                get_predicate_last pred psize idx >>= fun last ->
                  M.choiceT
                    last
                    (scalable_getlane cur_val idx esize)
                    mzero
                in
                let rec reduce cur_val n op =
                  match n with
                  | 0 -> op >>| read_active_elem_or_zero n cur_val >>= sum_elems
                  | _ -> reduce cur_val (n-1) (op >>| read_active_elem_or_zero n cur_val  >>= sum_elems)
                in
                reduce src (nelem-1) mzero)
            mzero >>= fun v ->
            let sz = AArch64Base.tr_simd_variant var in
            write_reg_neon_sz sz r1 v ii

      let add_sv r1 r2 r3 ii =
        let nelem = scalable_nelem r1 in
        let esize = scalable_esize r1 in
        read_reg_scalable Port.No r3 ii >>|
        read_reg_scalable Port.No r2 ii >>= fun (v1,v2) ->
          let add cur_val idx =
            scalable_getlane v1 idx esize >>|
            scalable_getlane v2 idx esize >>=
            sum_elems >>= scalable_setlane cur_val idx esize
          in
          let rec reduce idx op =
            match idx with
            | 0 -> op >>= fun old_val -> add old_val idx
            | _ -> reduce (idx-1) (op >>= fun old_val -> add old_val idx)
          in
          reduce (nelem-1) mzero >>= fun v ->
            write_reg_scalable r1 v ii

      let movprfx dst pg src ii =
        let nelem = predicate_nelem src in
        let psize = predicate_psize src in
        let esize = scalable_esize dst in
        let orig = match pg with
        | AArch64Base.PMreg (_,AArch64Base.Zero)
          -> mzero
        | AArch64Base.PMreg (_,AArch64Base.Merge)
          -> read_reg_scalable Port.No dst ii
        | _ -> assert false
        in
        orig >>|
        read_reg_predicate pg ii >>= fun (orig,pred) ->
          get_predicate_any pred psize nelem >>= fun any ->
            M.choiceT
            any
            (read_reg_scalable Port.No src ii >>= fun src ->
              let copy orig cur_val idx =
                get_predicate_last pred psize idx >>= fun last ->
                  M.choiceT
                  last
                  (scalable_getlane cur_val idx esize)
                  (scalable_getlane orig idx esize)
                  >>= fun v ->
                    scalable_setlane cur_val idx esize v
              in
              let rec reduce orig n op =
                match n with
                | 0 -> op >>= fun old_val -> copy orig old_val n
                | _ -> reduce orig (n-1) (op >>= fun old_val -> copy orig old_val n)
              in
              reduce orig (nelem-1) (M.unitT src))
            (M.unitT orig) >>= fun v ->
              write_reg_scalable dst v ii

      let neg dst pg src ii =
        let nelem = predicate_nelem src in
        let psize = predicate_psize src in
        let esize = scalable_esize dst in
        read_reg_scalable Port.No dst ii >>|
        read_reg_predicate pg ii >>= fun (orig,pred) ->
          get_predicate_any pred psize nelem >>= fun any ->
            M.choiceT
            any
            (read_reg_scalable Port.No src ii >>= fun src ->
              let negate orig cur_val idx =
                get_predicate_last pred psize idx >>= fun last ->
                M.choiceT
                  last
                  (scalable_getlane cur_val idx esize
                   >>= subtraction V.zero)
                  (scalable_getlane orig idx esize)
                >>= fun v ->
                  scalable_setlane cur_val idx esize v
              in
              let rec reduce orig n op =
              match n with
              | 0 -> op >>= fun old_val -> negate orig old_val n
              | _ -> reduce orig (n-1) (op >>= fun old_val -> negate orig old_val n)
              in
              reduce orig (nelem-1) (M.unitT src))
            (M.unitT orig) >>= fun v ->
              write_reg_scalable dst v ii

      let while_op compare unsigned p var r1 r2 ii =
        let psize = predicate_psize p in
        let nelem = predicate_nelem p in
        let sz = AArch64Base.tr_variant var  in
        let extend = if unsigned then uxt_op sz else sxt_op sz in
        read_reg_ord_sz sz r1 ii >>|
        read_reg_ord_sz sz r2 ii >>= fun (v1,v2) ->
          let rec repeat old_val idx v1 v2 last =
            if idx < nelem then
              extend v1 >>|
              extend v2 >>= fun (v1,v2) ->
                compare v1 v2 >>= fun (cond) ->
                  M.op Op.And last cond >>= fun last ->
                    predicate_setlane old_val idx psize last >>|
                    M.add v1 V.one >>= fun (old_val, v1) ->
                      repeat old_val (idx+1) v1 v2 last
            else M.unitT old_val
          in
          repeat V.zero 0 v1 v2 V.one >>= fun (new_val) ->
          write_reg_predicate p new_val ii >>|
          ( let last idx = get_predicate_last new_val psize idx in
            (* Fisrt active *)
            let>= n = last 0 
            and* z =
              let rec reduce idx op = match idx with
              | 0 ->  op >>| last idx >>= fun (v1,v2) -> M.op Op.Or v1 v2
              | _ -> reduce (idx-1) (op >>| last idx  >>= fun (v1,v2) -> M.op Op.Or v1 v2)
              in
              reduce (nelem-1) mzero >>= M.op1 Op.Not
            and* c = last (nelem-1) >>= M.op1 Op.Not
            and* v = mzero in
            write_nzcv (n, z, c, v) ii
          ) >>= fun ((), nzcv_val) -> M.unitT ((p, new_val) :: nzcv_val)

      let ptrue p pattern ii =
        let psize = predicate_psize p in
        let nelem = predicate_nelem p in
        let count = predicate_count pattern nelem in
        let rec repeat old_val idx =
          if idx < nelem then
            let v =
              if idx < count then AArch64.one_promoted
              else AArch64.zero_promoted in
            predicate_setlane old_val idx psize v >>= fun old_val ->
              repeat old_val (idx+1)
          else M.unitT old_val
        in
        repeat AArch64.zero_promoted 0 >>= fun new_val ->
        write_reg_predicate p new_val ii >>! new_val

      let mov_sv r k shift ii =
        let open AArch64Base in
        begin match shift with
        | S_NOEXT
        | S_LSL(0)  ->
          M.unitT (AArch64.promote_int k)
        | S_LSL(8 as amount) ->
          M.op1 (Op.LeftShift amount) (AArch64.promote_int k)
        | S_LSL(n) ->
          Warn.fatal
            "illegal shift immediate %d in instruction mov"
            n
        | s ->
          Warn.fatal
            "illegal shift operand %s in in instruction mov"
            (pp_barrel_shift "," s pp_imm)
        end
          >>= fun v -> write_reg_scalable_rep r v ii

      let index r v1 v2 ii =
        let nelem = scalable_nelem r in
        let esize = scalable_esize r in
        let increment cur_val idx o =
          M.add v1 o >>=  promote >>= scalable_setlane cur_val idx esize in
        let rec reduce n op =
          let i = V.op Op.Mul (V.intToV n) v2 in
          match n with
          | 0 -> op >>= fun old_val -> increment old_val n i
          | _ -> reduce (n-1) (op >>= fun old_val -> increment old_val n i)
        in
        reduce (nelem-1) mzero
        >>= fun v -> write_reg_scalable r v ii
        >>! v

      let cnt_inc (op,v) r pat k ii =
        let open AArch64 in
        let nelem = scalable_nbytes / simd_variant_nbytes v in
        let off = predicate_count pat nelem * k in
        let sz = MachSize.Quad in
        (match op with
         | CNT -> mzero
         | INC -> read_reg_ord_sz sz r ii)
        >>= M.op1 (Op.AddK off)
        >>= fun v -> write_reg_sz_dest sz r v ii

      let reset_sm v ii =
        let pstate_sm = AArch64.(PState PSTATE.SM) in
        let z = AArch64.zero_promoted in
        let zop = List.map (fun r -> write_reg_scalable r z ii) AArch64.zregs in
        let pop = List.map (fun r -> write_reg_predicate r z ii) AArch64.pregs in
        let zval = List.map (fun r -> r,z) AArch64.zregs in
        let pval = List.map (fun r -> r,z) AArch64.pregs in
        let ops = zop@pop@[write_reg pstate_sm v ii] in
        let vals = zval@pval@[pstate_sm,v] in
        ops,vals

      let reset_za v ii =
        let pstate_za = AArch64.(PState PSTATE.ZA) in
        let z = AArch64.zero_promoted in
        let r = AArch64.ZAreg(0,None,0) in
        let ops = [write_reg_za r z ii; write_reg pstate_za v ii] in
        let vals = [r,z;pstate_za,v] in
        ops,vals

      let mova_vt r ri k pg src ii =
        let dst,tile,dir = match r with
        | AArch64Base.ZAreg (tile,Some dir,_) -> r,tile,dir
        | _ -> assert false in
        let psize = predicate_psize src in
        let esize = scalable_esize src in
        let dim = scalable_nbits / esize; in
        read_reg_ord ri ii >>= fun index ->
          M.add index (V.intToV k) >>= fun slice ->
            M.op Op.Rem slice (V.intToV dim) >>= fun slice ->
              read_reg_za dst ii >>|
                read_reg_predicate pg ii >>|
                  read_reg_scalable Port.No src ii >>= fun ((orig,pred),src) ->
                    let mova cur_val idx =
                      get_predicate_last pred psize idx >>= fun last ->
                        M.choiceT
                        last
                        (scalable_getlane src idx esize)
                        (za_getlane_dir dir orig tile slice (V.intToV idx) esize)
                        >>= fun v ->
                          za_setlane_dir dir cur_val tile slice (V.intToV idx) esize v
                    in
                    let rec reduce n op =
                      match n with
                      | 0 -> op >>= fun old_val -> mova old_val n
                      | _ -> reduce (n-1) (op >>= fun old_val -> mova old_val n)
                    in
                    reduce (dim-1) (M.unitT orig) >>= fun v ->
                      write_reg_za dst v ii >>! v

      let mova_tv dst pg r ri k ii =
        let src,tile,dir = match r with
        | AArch64Base.ZAreg (tile,Some dir,_) -> r,tile,dir
        | _ -> assert false in
        let psize = predicate_psize dst in
        let esize = scalable_esize dst in
        let dim = scalable_nbits / esize; in
        read_reg_ord ri ii >>= fun index ->
          M.add index (V.intToV k) >>= fun slice ->
            M.op Op.Rem slice (V.intToV dim) >>= fun slice ->
              read_reg_za src ii >>|
                read_reg_predicate pg ii >>|
                  read_reg_scalable Port.No dst ii >>= fun ((src,pred),orig) ->
                    let mova cur_val idx =
                      get_predicate_last pred psize idx >>= fun last ->
                        M.choiceT
                        last
                        (za_getlane_dir dir src tile slice (V.intToV idx) esize)
                        (scalable_getlane orig idx esize)
                        >>= fun v ->
                          scalable_setlane cur_val idx esize v
                    in
                    let rec reduce n op =
                      match n with
                      | 0 -> op >>= fun old_val -> mova old_val n
                      | _ -> reduce (n-1) (op >>= fun old_val -> mova old_val n)
                    in
                    reduce (dim-1) mzero_promoted >>= fun v ->
                      write_reg_scalable dst v ii >>! v

      let adda dir dst pslice pelem src ii =
        let acc,tile,dir = match dst with
        | AArch64Base.ZAreg (tile,None,_) -> dst,tile,dir
        | _ -> assert false in
        let psize = predicate_psize src in
        let esize = scalable_esize src in
        let dim = scalable_nbits / esize; in
        read_reg_za acc ii >>|
          read_reg_predicate pslice ii >>|
            read_reg_predicate pelem ii >>|
              read_reg_scalable Port.No src ii >>= fun (((acc,p1),p2),src) ->
                let add cur_val slice idx =
                  get_predicate_last p1 psize slice >>|
                    get_predicate_last p2 psize idx >>= fun (v1,v2) ->
                      M.op Op.And v1 v2 >>= fun last ->
                        M.choiceT
                          last
                          (let slice_v = V.intToV slice
                           and idx_v = V.intToV idx in
                           begin
                            scalable_getlane src idx esize
                            >>|
                            za_getlane_dir dir acc tile slice_v idx_v esize
                           end >>=
                            sum_elems
                            >>= fun v ->
                              za_setlane_dir
                                dir cur_val tile slice_v idx_v esize v)
                            (M.unitT cur_val)
                in
                let rec repeat_row old_val slice idx =
                  if idx < dim then
                    add old_val slice idx >>= fun old_val ->
                      repeat_row old_val slice (idx+1)
                  else M.unitT old_val in
                let rec repeat_col old_val slice =
                  if slice < dim then
                    repeat_row old_val slice 0 >>= fun old_val ->
                      repeat_col old_val (slice+1)
                  else
                    M.unitT old_val
                in
                repeat_col acc 0 >>= fun v ->
                  write_reg_za dst v ii >>! v

(******************************)
(* Move constant instructions *)
(******************************)

      let movzn inv sz rd k os ii =
        let open AArch64Base in
        assert (MachSize.is_imm16 k);
        begin match sz, os with
        | V32, S_NOEXT | V64, S_NOEXT ->
          (* Or'ing zero with value should zero out what's left *)
          M.unitT (V.intToV k)
        | V32, S_LSL(0|16 as s)
        | V64, S_LSL((0|16|32|48 as s)) ->
          M.op1 (Op.LeftShift s) (V.intToV k)
        | _, S_LSL(_) | _, _ ->
            Warn.fatal
              "illegal instruction %s"
              (AArch64.dump_instruction (I_MOVZ (sz, rd, k, os)))
        end >>=
        begin
          if inv then M.op1 Op.Inv
          else M.unitT
        end >>=
        fun v -> write_reg_dest rd v ii

      let movz = movzn false
      and movn = movzn true

      let m_movk msk v1 v2 =
        M.op Op.AndNot2 v2 msk >>= M.op Op.Or v1

      let movk var rd k os ii =
        let open AArch64Base in
        let msk =
          let v = V.op1 (Op.LeftShift 16) V.one in
          V.op Op.Sub v V.one in
        assert (MachSize.is_imm16 k);
        let sz = tr_variant var in
        begin match var, os with
        | V32, S_NOEXT | V64, S_NOEXT ->
            read_reg_ord_sz sz rd ii >>= m_movk msk (V.intToV k)
        | V32, S_LSL(0|16 as s)
        | V64, S_LSL((0|16|32|48 as s)) ->
            let msk = V.op1 (Op.LeftShift s) msk in
            let v1 = V.op1 (Op.LeftShift s) (V.intToV k) in
            read_reg_ord_sz sz rd ii >>= m_movk msk v1
        | _, S_LSL(n) ->
          Warn.fatal
            "illegal shift immediate %d in %s instruction movk"
            n
            (pp_variant var)
        | _, s ->
          Warn.fatal
            "illegal shift operand %s in %s instruction movk"
            (pp_barrel_shift "," s pp_imm)
            (pp_variant var)
        end
        >>= fun v -> write_reg_dest rd v ii

(*
 * "Sign"-extend high-order bit of pattern.\
 * Notice that computation can be performed on 64bits,
 * masking is performed later, while writing
 * into register.
 *)

      let xtmsb imms v =
        let hsb = 63 in
        let msk =
          String.concat ""
            ("0b1"::Misc.replicate imms "0") in
        M.op1 (Op.AndK msk) v >>=
        M.op1 (Op.LeftShift (hsb-imms)) >>=
        M.op1 (Op.ArithRightShift (hsb-imms)) >>=
        M.op Op.Or v

      let xbfm signed v rd rn kr ks ii =
        let open AArch64Base in
        let sz = tr_variant v in
        let regsize = match v with
        | V32 -> 32
        | V64 -> 64
        | _ -> assert false in
        let hex_mask = begin
          let f = if ks >= kr then
            (fun v -> if v < kr || v > ks then "0" else "1")
            else
            (fun v -> if v > ks then "0" else "1") in
          let bitmask = List.rev (List.init regsize f) in
          let dec_mask = Int64.of_string
            (Printf.sprintf "0b%s" (String.concat "" bitmask)) in
          Printf.sprintf "0x%Lx" dec_mask
        end in
        let shift_sz = if ks >= kr then kr else regsize-kr in
        let shift_op = if ks >= kr then Op.ShiftRight else Op.ShiftLeft in
        read_reg_ord_sz sz rn ii
        >>= M.op1 (Op.AndK hex_mask)
        >>= fun v -> M.op shift_op v (V.intToV shift_sz)
        >>=
          begin
            if signed then
              xtmsb
                (if ks >= kr then ks-kr else regsize-kr+ks)
            else fun v -> M.unitT v
          end
        >>= fun v -> write_reg rd v ii
        >>= B.next1T

      let csel_op op v =
        let open AArch64Base in
        match op with
        | Cpy -> M.unitT v
        | Inc -> M.op Op.Add v V.one
        | Neg -> subtraction V.zero v
        | Inv -> M.op1 Op.Inv v

      let do_load_elem an sz i r addr ii =
        let access_size = AArch64.simd_mem_access_size [r] in
        do_read_mem_ret access_size an aexp Access.VIR addr ii
        >>= promote >>= fun v ->
        write_reg_neon_elem sz r i v ii

      let load_elem = do_load_elem Annot.N
      let load_elem_ldar = do_load_elem Annot.Q

      let load_elem_rep sz r addr ii =
        let access_size = AArch64.simd_mem_access_size [r] in
        do_read_mem_ret access_size Annot.N aexp Access.VIR addr ii >>= fun v ->
        write_reg_neon_rep sz r v ii

      let do_store_elem an i r addr ii =
        let access_size = AArch64.simd_mem_access_size [r] in
        read_reg_neon_elem Port.Data r i ii >>= demote >>= fun v ->
        do_write_mem access_size an aexp Access.VIR addr v ii

      let store_elem = do_store_elem Annot.N
      let store_elem_stlr = do_store_elem Annot.L

     (* Single structure memory access *)
      let mem_ss memop addr rs ii =
        let op r o = M.add o addr >>= fun addr -> memop r addr ii in
        let os =
          List.mapi
            (fun i r -> V.intToV (i * neon_esize r / 8)) rs in
        List.fold_right (>>::) (List.map2 op rs os) (M.unitT [()])

      let rec reduce_ord l =
        match l with
        | [] -> M.unitT ()
        | h::t -> h >>= fun () -> reduce_ord t

      let neon_memops memop addr idx rs ii =
        let calc_offset i r =
          (V.intToV ((idx*(List.length rs)+i) * neon_esize r / 8)) in
        let op r o = M.add o addr >>= fun addr -> memop idx r addr ii in
        List.map2 op rs (List.mapi calc_offset rs)

      let load_m addr rlist ii =
        let op i =
          let ops = neon_memops (load_elem MachSize.S128) addr i rlist ii in
          reduce_ord ops in
        let ops = List.map op (Misc.interval 0 (neon_nelem (List.hd rlist))) in
        reduce_ord ops

      let store_m addr rlist ii =
        let op i =
          let ops = neon_memops store_elem addr i rlist ii in
          List.fold_right (>>::) ops (M.unitT [()]) in
        let ops = List.map op (Misc.interval 0 (neon_nelem (List.hd rlist))) in
        List.fold_right (>>::) ops (M.unitT [[()]])

      let neon_memops_contigous memop addr step r ii =
        let op idx =
          let o = (idx + step) * neon_esize r / 8 in
          M.add (V.intToV o) addr >>= fun addr -> memop idx r addr ii in
        List.map op (Misc.interval 0 (neon_nelem r))

      let load_m_contigous addr rlist ii =
        let op i r =
          let step = i*(neon_nelem r) in
          let ops = neon_memops_contigous (load_elem MachSize.S128) addr step r ii in
          reduce_ord ops in
        let ops = List.mapi op rlist in
        reduce_ord ops

      let store_m_contigous addr rlist ii =
        let op i r =
          let step = i*(neon_nelem r) in
          let ops = neon_memops_contigous store_elem addr step r ii in
          List.fold_right (>>::) ops (M.unitT [()]) in
        let ops = List.mapi op rlist in
        List.fold_right (>>::) ops (M.unitT [[()]])

      (** branch on whether [p]'s value [pred] has any active elements.

          add [iico_causality_ctrl] from the predicate read to [mtrue] or
          [mfalse] *)
      let any_active p pred psize nelem ii mtrue mfalse =
        let>= any = get_predicate_any pred psize nelem in
        let>* () =
          let cond = Printf.sprintf "AnyActive(%s)" (A.pp_reg p) in
          commit_pred_txt (Some cond) ii
        in
        M.choiceT any mtrue mfalse

      (** check the element [idx] in predicate [pred] and add [mtrue] if active,
          or [mfalse] otherwise.
          add [iico_causality_ctrl] from the predicate read to [mtrue] or
          [mfalse] *)
      let is_active_element p pred psize idx ii mtrue mfalse =
        let>= last = get_predicate_last pred psize idx in
        let>* () =
          let cond = Printf.sprintf "ActiveElem(%s, %d)" (A.pp_reg p) idx in
          commit_pred_txt (Some cond) ii
        in
        M.choiceT last mtrue mfalse

      let no_action = M.mk_singleton_es Act.NoAction

      (** perform [ops] in parallel and fold right on results *)
      let para_fold_right mbind ops munit =
        let final results =
          List.fold_right
            (fun v macc -> macc >>= mbind v)
            results munit
        in
        M.data_output_union
          (List.fold_right ( >>:: ) ops (M.unitT []))
          final

      let load_predicated_elem_or_zero_m sz p ma rlist ii =
        let r = List.hd rlist in
        let nelem = scalable_nelem r in
        let psize = predicate_psize r in
        let esize = scalable_esize r in
        let nregs = List.length rlist in
        let>= results =
          let<>= base = ma in
          let>= pred = read_reg_predicate p ii in
          let ops i =
            let op idx =
              let load =
                let offset = (idx * nregs + i) * MachSize.nbytes sz in
                let>= addr = M.op1 (Op.AddK offset) base in
                let>= v = do_read_mem_ret sz Annot.N aexp Access.VIR addr ii in
                let>= v = promote v in
                M.op1 (Op.LeftShift (idx * esize)) v
              in
              is_active_element p pred psize idx ii load (no_action ii >>! M.A.V.zero)
            in
            let ops = List.map op (Misc.interval 0 nelem) in
            para_fold_right (M.op Op.Or) ops mzero
          in
          let ops = List.map ops (Misc.interval 0 nregs) in
          List.fold_right ( >>:: ) ops (M.unitT [])
        in
        let f (r, result) macc =
          write_reg_scalable r result ii >>:: macc
        in
        List.fold_right f (List.combine rlist results) (M.unitT [()])

      let store_predicated_elem_or_merge_m sz p ma rlist ii =
        let r = List.hd rlist in
        let nelem = scalable_nelem r in
        let psize = predicate_psize r in
        let esize = scalable_esize r in
        let nregs = List.length rlist in
          let<>= base = ma in
          let>= pred = read_reg_predicate p ii in
          let ops i r =
            let<>= v =
              any_active p pred psize nelem ii
              (read_reg_scalable Port.Data r ii)
              mzero
            in
            let op idx =
              let store =
                let offset = (idx * nregs + i) * MachSize.nbytes sz in
                let>= addr = M.op1 (Op.AddK offset) base
                and* v = scalable_getlane v idx esize >>= demote in
                write_mem sz aexp Access.VIR addr v ii
              in
              is_active_element p pred psize idx ii store (M.unitT ())
            in
            let ops = List.map op (Misc.interval 0 nelem) in
            List.fold_right M.seq_mem_list ops (M.unitT [])
            (* List.fold_right M.seq_mem_list ops (M.unitT [()]) *)
          in
          let ops = List.mapi ops rlist in
          List.fold_right  M.seq_mem_list  ops (M.unitT [])

      let load_gather_predicated_elem_or_zero sz p ma mo rs e k ii =
        let r = List.hd rs in
        let psize = predicate_psize r in
        let nelem = scalable_nelem r in
        let esize = scalable_esize r in
        let>= pred = read_reg_predicate p ii in
        let>= result =
          let<>= (base, offsets) =
            any_active p pred psize nelem ii
              (ma >>| mo)
              (M.unitT M.A.V.(zero, zero))
          in
          let op idx =
            let load =
              let>= lane = scalable_getlane offsets idx esize in
              let>= lane = demote lane in
              let>= o = memext_sext e k lane in
              let>= addr = M.add base o in
              let>= v = do_read_mem_ret sz Annot.N aexp Access.VIR addr ii in
              let>= v = promote v in
              M.op1 (Op.LeftShift (idx * esize)) v
            in
            is_active_element p pred psize idx ii load (no_action ii >>! M.A.V.zero)
          in
          let ops = List.map op (Misc.interval 0 nelem) in
          para_fold_right (M.op Op.Or) ops mzero
        in
        write_reg_scalable r result ii

      let store_scatter_predicated_elem_or_merge sz p ma mo rs e k ii =
        let r = List.hd rs in
        let psize = predicate_psize r in
        let nelem = scalable_nelem r in
        let esize = scalable_esize r in
        let>= pred = read_reg_predicate p ii in
        let<>= ((base, offsets), v) =
          any_active p pred psize nelem ii
            (ma >>| mo >>| read_reg_scalable Port.Data r ii)
            (M.unitT ((M.A.V.zero, M.A.V.zero), M.A.V.zero))
        in
        let op idx =
          let store =
            let>= lane = scalable_getlane offsets idx esize in
            let>= lane = demote lane in
            let>= o = memext_sext e k lane in
            let>= addr = M.add base o in
            let>= v = scalable_getlane v idx esize in
            let>= v = demote v in
            write_mem sz aexp Access.VIR addr v ii in
          is_active_element r pred psize idx ii store (M.unitT ())
        in
        let ops = List.map op (Misc.interval 0 nelem) in
        List.fold_right M.seq_mem_list ops (M.unitT [()])

      let load_predicated_slice sz r ri k p ma ii =
        let dst,tile,dir,esize = match r with
        | AArch64Base.ZAreg (tile,Some(dir),esize) -> r,tile,dir,esize
        | _ -> assert false in
        let psize = predicate_psize dst in
        let dim = scalable_nbits / esize; in
        ma >>|
        read_reg_za dst ii >>|
          read_reg_predicate p ii >>|
            (read_reg_ord ri ii >>= fun index ->
              M.add index (V.intToV k) >>= fun slice ->
                M.op Op.Rem slice (V.intToV dim)) >>= fun ((((base,orig)),pred),slice) ->
            let load idx =
              let offset = idx * MachSize.nbytes sz in
              get_predicate_last pred psize idx >>= fun last ->
                M.choiceT
                last
                (M.op1 (Op.AddK offset) base >>= fun addr ->
                  do_read_mem_ret sz Annot.N aexp Access.VIR addr ii)
                mzero
                >>= promote >>| za_getoffset_dir dir tile slice (V.intToV idx) esize >>= fun (v,amount) ->
                  M.op Op.ShiftLeft v amount
            in
            let rec reduce idx op =
              match idx with
              | 0 -> op >>| load idx >>= fun (v1,v2) -> M.op Op.Or v1 v2
              | _ -> reduce (idx-1) (op >>| load idx >>= fun (v1,v2) -> M.op Op.Or v1 v2)
            in
            reduce (dim-1) mzero_promoted >>|
            ( let mask idx =
                za_getoffset_dir dir tile slice (V.intToV idx) esize >>= fun amount ->
                M.op Op.ShiftLeft (AArch64.scalable_mask esize) amount
              in
              let rec genmask idx op =
                match idx with
                | 0 -> op >>| mask idx >>= fun (v1,v2) -> M.op Op.Or v1 v2
                | _ -> genmask (idx-1) (op >>| mask idx >>= fun (v1,v2) -> M.op Op.Or v1 v2)
              in
              genmask (dim-1) mzero_promoted >>= M.op1 Op.Inv >>= fun invert ->
                M.op Op.And invert orig) >>= fun (new_val,old_val) ->
                  M.op Op.Or new_val old_val >>= fun v ->
                    write_reg_za dst v ii

      let store_predicated_slice sz r ri k p ma ii =
        let src,tile,dir,esize = match r with
        | AArch64Base.ZAreg (tile,Some(dir),esize) -> r,tile,dir,esize
        | _ -> assert false in
        let psize = predicate_psize src in
        let dim = scalable_nbits / esize; in
        ma >>|
        read_reg_za src ii >>|
          read_reg_predicate p ii >>|
            (read_reg_ord ri ii >>= fun index ->
              M.add index (V.intToV k) >>= fun slice ->
                M.op Op.Rem slice (V.intToV dim)) >>= fun ((((base,orig)),pred),slice) ->
            let store idx =
              let offset = idx * MachSize.nbytes sz in
              get_predicate_last pred psize idx >>= fun last ->
                M.choiceT
                last
                (M.op1 (Op.AddK offset) base >>|
                 (za_getlane_dir dir orig tile slice (V.intToV idx) esize >>= demote)
                 >>= fun (addr,v) -> write_mem sz aexp Access.VIR addr v ii)
                (M.unitT ())
            in
            let rec reduce idx op =
              match idx with
              | 0 -> store idx >>:: op
              | _ -> reduce (idx-1) (store idx >>:: op)
            in
            reduce (dim-1) (M.unitT [()])


      (* Data cache operations *)
      let dc_loc op a ii =
        let mk_act loc = Act.CMO (AArch64.CMO.DC op,Some loc) in
        let loc = A.Location_global a in
        M.mk_singleton_es (mk_act loc) ii

      let do_dc op rd ii =
        if AArch64Base.DC.sw op then
          M.mk_singleton_es (Act.CMO (AArch64.CMO.DC op, None)) ii >>= B.next1T
        else begin
            (* TODO: The size for DC should be a cache line *)
            let mop _ac a = dc_loc op a ii in
            let dir = match op.AArch64Base.DC.funct with
              | AArch64Base.DC.I -> Dir.W
              | _ -> Dir.R in
            (* CMO by VA other than DC ZVA are Tag Unchecked *)
            lift_memop rd dir false false
              (fun ac ma _mv -> (* value fake here *)
                if Access.is_physical ac then
                  M.bind_ctrldata ma (mop ac)
                else
                  ma >>= mop ac)
              (to_perms "r" MachSize.Word)
              (read_reg_addr rd ii) mzero Annot.N ii
          end

      let do_ic op rd ii =
        if AArch64Base.IC.all op then (* IC IALLU *)
          M.mk_singleton_es (Act.CMO (AArch64.CMO.IC op, None)) ii >>= B.next1T
        else
        begin (* IC IVAU *)
          read_reg_addr rd ii
          >>= fun a ->
            let loc = A.Location_global a in
            let act = Act.CMO (AArch64.CMO.IC op,Some loc) in
            M.mk_singleton_es act ii
          >>= B.next1T
        end

      let ldg rt rn k ii =
        let ma = get_ea rn (AArch64.K k) AArch64.S_NOEXT ii in
        let mv = read_reg_ord rt ii >>= loc_extract in
        let do_ldg ac ma mv =
          let _do_ldg (a, v) =
            let* atag = M.op1 Op.TagLoc a in
            let* tag = do_read_tag atag ii in
            let* v = M.op Op.SetTag v tag in
            let* () = write_reg rt v ii in
            B.nextT in
          if Access.is_physical ac then
            M.bind_ctrldata (ma >>| mv) _do_ldg
          else
            ma >>| mv >>= _do_ldg in
        lift_memop rn Dir.R false false (fun ac ma mv -> do_ldg ac ma mv)
        (to_perms "w" MachSize.S128) ma mv Annot.N ii

      type double = Once|Twice

      let stg d rt rn k ii =
        let ma = get_ea rn (AArch64.K k) AArch64.S_NOEXT ii
        and mv = read_reg_data rt ii >>= tag_extract in
        let do_stg ac ma mv =
          let __do_stg a v =
            M.op1 Op.TagLoc a >>= fun a -> do_write_tag a v ii in
          let _do_stg =
            match d with
            | Once ->
               fun a v -> __do_stg a v
            | Twice ->
               fun a v ->
                 begin
                   __do_stg a v >>|
                     (M.op1 (Op.AddK MachSize.granule_nbytes) a
                      >>= fun a ->  __do_stg a v)
                 end >>! () in
          if Access.is_physical ac then
            M.bind_ctrldata_data ma mv _do_stg
          else
            (ma >>| mv) >>= fun (a,v) -> _do_stg a v in
        lift_memop rn Dir.W true false (fun ac ma mv -> do_stg ac ma mv)
          (to_perms "w" MachSize.granule) ma mv Annot.N ii

      let stz d rn k ii =
        let sz = MachSize.granule in
        let mop =
          match d with
          | Once ->
             do_write_mem sz Annot.N aexp
          | Twice ->
             fun ac a v ii ->
               let mop1 = do_write_mem sz Annot.N aexp  ac a v ii
               and mop2 =
                 M.op1 (Op.AddK MachSize.granule_nbytes) a
                 >>= fun a -> do_write_mem sz Annot.N aexp  ac a v ii in
               (mop1 >>| mop2) >>! () in
        let ma = get_ea rn (AArch64.K k) AArch64.S_NOEXT ii >>= loc_extract in
        lift_memop rn Dir.W true false (* Unchecked *)
          (fun ac ma mv ->
            if Access.is_physical ac then begin
                (* additional ctrl dep on address *)
                M.bind_ctrldata_data ma mv
                  (fun a v -> mop ac a v ii)
              end else
              (ma >>| mv) >>= fun (a,v) -> mop ac a v ii)
          (to_perms "w" sz) ma mzero Annot.N ii

      let do_stzg d rt rn k ii =
        let do_stz = stz d rn k ii in
        let do_stg = stg d rt rn k ii in
        if kvm then
          (* The two operations include their own translations, if
             there is a fault, it has to be ordered after any other
             event of the instruction *)
          M.altT
            (M.delay_kont "do_stg" do_stg
               (function
                 | B.Next _ ->
                   fun mstg -> M.para_bind_output_right mstg (fun _ -> do_stz)
                 | B.Fault _ ->
                   fun mstg -> mstg
                 | _ -> Warn.fatal "Unexpected return value do_stz"))
            (M.delay_kont "do_stz" do_stz
               (function
                 | B.Next _ ->
                   fun mstz -> M.delay_kont "do_stg" do_stg
                       (function
                         | B.Next _ ->
                           (* Force the solver to drop this, already handled above *)
                           fun _ -> M.assertT V.zero B.nextT
                         | B.Fault _ ->
                           fun mstg -> M.para_bind_output_right mstz (fun _ -> mstg)
                         | _ ->
                           Warn.fatal "Unexpected return value do_stg")
                 | B.Fault _ ->
                   fun mstz -> mstz
                 | _ -> Warn.fatal "Unexpected return value do_stz"))
        else
          do_stg >>| do_stz >>= M.ignore >>= B.next1T

      let stzg = do_stzg Once
      and stz2g = do_stzg Twice
      and st2g = stg Twice

      let irg rd rn rm ii =
        (read_reg_ord rn ii >>= loc_extract) >>|
        (read_reg_ord rm ii >>= fun v ->
          (* We support only 8 colors *)
          M.op Op.Or v (V.intToV 0xff00)) >>= 
        fun (addr,exclude) ->
          let set color =
            let tag = V.Val (Constant.Tag (Misc.tag_of_int color)) in
            M.op Op.SetTag addr tag >>= fun v ->
            write_reg_dest rd v ii
          in
          let select tag =
            M.op1 (Op.ReadBit tag) exclude >>= fun bit ->
            M.choiceT bit (M.assertT V.zero mzero) (set tag) in
          let rec iter_tags = function
            | 0 -> select 0
            | _ as tag -> M.altT (select tag) (iter_tags (tag - 1))
          in
          M.op Op.Eq exclude (V.intToV 0xffff) >>= fun ones ->
            M.choiceT ones (set 0) (iter_tags 7) >>= M.ignore >>= B.next1T

(*********************)
(* Instruction fetch *)
(*********************)

      let read_loc_instr a ac ii =
        M.read_loc Port.No (mk_fetch Annot.N ac) a ii

(*******************************)
(* Pointer Authentication Code *)
(*******************************)

      let do_pac key rd rn ii =
        if key_enable key then begin
          read_reg_ord rd ii >>|
          read_reg_ord rn ii >>= fun (addr, modifier) ->
          M.op
            (Op.ArchOp (AArch64Op.AddPAC (not const_pac_field, key)))
            addr modifier >>= fun v ->
          write_reg_dest rd v ii >>= fun v ->
          B.nextSetT rd v
        end else
          read_reg_ord rd ii >>= fun v ->
          write_reg_dest rd v ii >>= fun v ->
          B.nextSetT rd v

      let authenticate pointer modifier key ii mop mfault =
        let original_pointer md =
          md >>= M.op1 (Op.ArchOp1 AArch64Op.MakeCanonical) in

        (* data_input_next allow to not have a control depedency between the
         * commit event and the register-read event in Xd *)
        let mok md mn =
          (md >>| mn >>= fun _ -> commit_pred ii) >>*= fun _ ->
          (M.data_input_next (original_pointer md) (fun ptr -> mop (M.unitT ptr)))
        in

        let error_code md =
          md >>= M.op1 (Op.ArchOp1 (AArch64Op.AddErrorCode key)) in

        let mfail md mn = if fpac then
            (md >>| mn >>= fun _ -> commit_pred ii) >>*= fun _ -> mfault
          else if pauth1 then
            (md >>| mn >>= fun _ -> commit_pred ii) >>*= fun _ ->
            (M.data_input_next (error_code md) (fun ptr -> mop (M.unitT ptr)))
          else
            md >>| mn >>= fun (xd,xn) ->
            mop (M.op (Op.ArchOp (AArch64Op.AddPAC (false,key))) xd xn)
        in

        let auth_check xd xn =
          M.op (Op.ArchOp (AArch64Op.AddPAC (false,key))) xd xn >>=
          check_canonical
        in

        M.delay_kont "read pointer" pointer (fun xd md ->
          M.delay_kont "read modifier" modifier (fun xn mn ->
            auth_check xd xn >>= fun c ->
            M.choiceT c
              (mok md mn)
              (mfail md mn)
          )
        )

      let do_aut key rd rn ii =
        if key_enable key then begin
          let (>>!) = M.(>>!) in

          let lbl_v = get_instr_label ii.A.proc ii in
          let mfault =
              set_elr_el1 lbl_v ii >>|
              mk_fault None Dir.R Annot.N ii
                (Some (FaultType.AArch64.PacCheck key))
                None
              >>! B.fault [AArch64Base.elr_el1, lbl_v]
          in

          let mop ma =
            ma >>= fun v ->
            write_reg_dest rd v ii >>= fun v ->
            B.nextSetT rd v
          in

          authenticate
            (read_reg_ord rd ii)
            (read_reg_ord rn ii)
            key ii mop mfault
        end else
          read_reg_ord rd ii >>= fun v ->
          write_reg_dest rd v ii >>= fun v ->
          B.nextSetT rd v

      let do_xpac r ii =
        read_reg_ord r ii >>= fun v ->
        M.op1 (Op.ArchOp1 AArch64Op.MakeCanonical) v >>= fun v ->
        write_reg_dest r v ii >>= fun v ->
        B.nextSetT r v

(*************************)
(* Guarded Control Stack *)
(*************************)
      module GCSSem = struct
        let base_mk_fault = mk_fault

        let mk_fault action ft ii =
          emit_fault None action Dir.R Annot.N (Some ft) None ii

        let lift_fault dir txt ft ii =
          let>* () = commit_pred_txt txt ii in
          let lbl_v = get_instr_label ii.A.proc ii in
          let* () = set_elr_el1 lbl_v ii
          and* () = base_mk_fault None dir Annot.N ii ft None in
          M.ignore () >>! B.fault [AArch64Base.elr_el1, lbl_v]

        let get_cap mask v =
          M.op1 Op.Offset v >>= M.op Op.And mask

        let set_cap cap mask v =
          let invert = V.op1 Op.Inv mask in
          M.op1 Op.Offset v >>= fun offset ->
            (* Strip offset *)
            M.op Op.Sub v offset >>|
            (* Extract index *)
            (M.op Op.And offset invert >>|
              (* Make sure cap fits into mask *)
              M.op Op.And cap mask >>= fun (index, cap) ->
                (* Make new offset *)
                M.op Op.Or index cap) >>= fun (v, offset) ->
                (* Write it back *)
                M.op Op.Add v offset

        let reset_cap = set_cap V.zero
        let make_valid = set_cap V.one (V.intToV 0xfff)
        let make_inprogress = set_cap (V.intToV 0x5) (V.intToV 0x7)

        let read ac an a ii = do_read_mem_ret quad an AArch64Explicit.(NExp GCS) ac a ii
        and write ac an a v ii = do_write_mem quad an AArch64Explicit.(NExp GCS) ac a v ii

        let bind_data_gcspr m ii =
          let open AArch64Base in
          let rA = SysReg GCSPR_EL1 in
          let read e = (is_this_reg rA e) && (E.is_reg_load e ii.A.proc)
          and write e = (is_this_reg rA e) && (E.is_reg_store e ii.A.proc) in
          M.short read write m

      end


      let gcsstr r1 r2 ii =
        let an = Annot.N in
        let mop ac a v = GCSSem.write ac an a v ii in
        lift_memop r2 Dir.W true false
        (fun ac ma mv ->
          if is_branching && Access.is_physical ac then
            M.bind_ctrldata_data ma mv (fun a v -> mop ac a v)
          else
            ma >>| mv >>= fun (a,v) -> mop ac a v
        )
        (to_perms "w" quad)
        (read_reg_addr r2 ii)
        (read_reg_data r1 ii)
        an
        ii

      let gcspushm rs ii =
        let open AArch64Base in
        let an = Annot.N
        and rA = SysReg GCSPR_EL1 in
        let ma =
          let off = V.intToV (-MachSize.nbytes quad) in
          let* a = read_reg_addr rA ii in
          M.add a off in
        let* a_virt, ma = M.delay ma in
        let mv = read_reg_data rs ii
        and mop ac ma mv =
          let write_rA = write_reg rA a_virt ii in
          let do_gcs_write a v = GCSSem.write ac an a v ii in
          if is_branching && Access.is_physical ac then
            let mop a =
              let* () = write_rA
              and* () = M.data_input_next mv (do_gcs_write a) in
            B.nextSetT rA a_virt in
            let m = ma >>*= mop in
            M.short E.is_mem_load E.is_mem_store m
          else
            let* a =
              let (let**) = M.(>>==) in
              let** a = ma in
              let* () = write_rA in
              M.unitT a
            and* v = mv in
            let* () = do_gcs_write a v in
            B.nextSetT rA a_virt in
        let m = lift_memop rA Dir.W true false mop (to_perms "w" quad) ma
          mv an ii in
        GCSSem.bind_data_gcspr m ii

      let gcspopm rd ii =
        let open AArch64Base in
        let an = Annot.N
        and rA = SysReg GCSPR_EL1
        and is_reg_write reg e =
          (is_this_reg reg e) && (E.is_reg_store e ii.A.proc) in
        let ma = read_reg_addr rA ii in
        let* a_virt, ma = M.delay ma in
        let do_gcs_read ac a =
          let m =
            let* v = GCSSem.read ac an a ii in
            let mok =
              let>* () = commit_pred_txt (Some "PCAligned") ii in
              let* addr =
                let off = MachSize.nbytes quad in
                M.add a_virt (V.intToV off) in
              let* () = write_reg rd v ii
              and* () = write_reg rA addr ii in
              B.nextSetT rA addr in
            let mno =
              let open FaultType.AArch64 in
              let ft = Some (GCSCheck POPM) in
              GCSSem.lift_fault Dir.R (Some "PCAligned") ft ii in
            let* is_aligned =
              let* cap =
                let mask = V.intToV 0x3 in
                GCSSem.get_cap mask v in
              M.op Op.Eq cap V.zero in
            M.choiceT is_aligned mok mno
          in
          M.short E.is_mem_load (is_reg_write rd) m in
        let mop ac ma _mv =
          if Access.is_physical ac then
            M.bind_ctrldata ma (do_gcs_read ac)
          else
            ma >>= do_gcs_read ac in
        let m = do_lift_memop rA Dir.R false false mop (to_perms "r" quad) ma
          mzero an ii Fun.id DISide.Data in
        GCSSem.bind_data_gcspr m ii

      let blop v_ret branch ii =
        let open AArch64Base in
        let an = Annot.N
        and rA = SysReg GCSPR_EL1 in
        let ma =
          let off = V.intToV (-MachSize.nbytes quad) in
          let* a = read_reg_addr rA ii in
          M.add a off in
        let* a_virt, ma = M.delay ma in
        let check_branch ac ma _mv =
          let write_rA = write_reg rA a_virt ii
          and write_lr = write_reg linkreg v_ret ii
          and write_gcs_mem a = GCSSem.write ac an a v_ret ii
          and bds = [rA, a_virt; AArch64Base.linkreg, v_ret] in
          if is_branching && Access.is_physical ac then
            let (let*=) = M.(>>*=) in
            let*= a = ma in
            let* b =
              let* b = branch bds
              and* () = write_rA
              and* () = write_lr
              and* () = write_gcs_mem a in
              M.unitT b in
            M.unitT b
          else
            let* b = branch bds
            and* () = write_lr
            and* () =
              let* a = ma in
              let* () = write_rA
              and* () = write_gcs_mem a in
              M.unitT () in
            M.unitT b in
        let m = do_lift_memop rA Dir.W true false check_branch
            (to_perms "w" quad) ma mzero an ii Fun.id DISide.Data in
        (* Value writen to GCSPR depends on previous read *)
        let m = GCSSem.bind_data_gcspr m ii in
        M.short E.is_mem_load E.is_mem_store m

      let retop test i r ii =
        let open AArch64Base in
        let an = Annot.N
        and rA = SysReg GCSPR_EL1
        and off = MachSize.nbytes quad in
        let ma = read_reg_addr rA ii
        and mv = read_reg_ord r ii in
        let cond_txt =
          Some (Printf.sprintf "target==%d:%s" ii.A.proc (A.pp_reg r)) in
        let* a_virt, ma = M.delay ma in
        let mop ac ma mv =
          let do_gcs_read ac addr =
            let (and**) = M.para_input_right in
            let* target = mv
            and** gcs_target = GCSSem.read ac an addr ii in
            let* gcs_check = M.op Op.Eq gcs_target target in
            let mok target =
              let>* () = commit_pred_txt cond_txt ii in
              let* new_addr = M.add a_virt (V.intToV off) in
              let* () = write_reg rA new_addr ii
              and* b =
                let bds = [rA, new_addr] in
                do_indirect_jump test bds i ii target in
              M.unitT b
            and mno =
              let open FaultType.AArch64 in
              let ft = Some (GCSCheck PRET) in
              GCSSem.lift_fault Dir.R (Some "GCSCheck PRET") ft ii in
            M.choiceT gcs_check (mok target) mno in
          if Access.is_physical ac then
            M.bind_ctrldata ma (do_gcs_read ac)
          else
            ma >>= do_gcs_read ac
        in
        let m = do_lift_memop rA Dir.R false false mop
          (to_perms "r" quad) ma mv an ii Fun.id DISide.Data in
        let m = GCSSem.bind_data_gcspr m ii in
        let is_reg_read r e =
          (is_this_reg r e) && (E.is_reg_load e ii.A.proc) in
        let is_gcs_mem_read e =
          E.is_mem_load e && Act.is_gcs e.E.action in
        let m = M.short (is_reg_read r) (E.is_pred_txt cond_txt) m in
        let* b, m = M.delay m in
        match b with
          | B.Fault _ ->
              (* only one execution for the case that faults *)
              m
          | _ ->
            (* The destination of RET can be determined by either
            the GCS Memory Read Effect or the Register Read Effect*)
            M.altT
              (M.short is_gcs_mem_read E.is_bcc m)
              (M.short (is_reg_read r) E.is_bcc m)

      let gcsss1 r ii =
        let open AArch64Base in
        let an = Annot.X
        and rA = SysReg GCSPR_EL1 in
        M.delay_kont "gcsss1"
        (read_reg_addr r ii)
        (fun incoming ma ->
          (* Valid cap entry is expected *)
          let cmpoperand = read_reg_data r ii >>= GCSSem.make_valid in (* incoming_pointer[63:12]:'000000000001' *)
          let cond2 = Some "(data==cmpoperand)" in
          let branch = commit_pred_txt cond2 ii in
          let update data =
             GCSSem.make_valid incoming >>= fun v ->
              let(>>*=) = M.bind_control_set_data_input_first in
              let mok =
                branch >>*=
                fun () -> write_reg rA incoming ii >>= fun () -> B.nextSetT rA incoming in
              M.op Op.Eq data v >>= fun cond ->  (* if data == cmpoperand then                             *)
              M.assertT cond mok                (*     SetCurrentGCSPointer(incoming_pointer[63:3]:'000'); *)
          in
          let fault data =
             GCSSem.make_valid incoming >>= fun v ->
              M.delay_kont "gcsss1(fault)"
              (M.op Op.Ne data v)             (* if data != cmpoperand then                   *)
              (fun cond action ->
                let open FaultType.AArch64 in (*     GCSDataCheckException(GCSInstType_SS1);  *)
                let mno = GCSSem.mk_fault action (GCSCheck SS1) ii in
                M.assertT cond mno)
          in
          let branch a =
            let cond1 = Some (Printf.sprintf "Valid([%s])" (V.pp_v a)) in
            commit_pred_txt cond1 ii in
          let shortcut =
            let read_reg e =
              let is_reg = is_this_reg r e
              and is_load = E.is_reg_load e ii.A.proc in
              is_reg && is_load
            in
            M.short read_reg (E.is_pred_txt cond2) in
          let mop_fail_no_wb ac ma _ =
            (* GCSSS1 fails, there is no Explicit Write Effect *)
            let read_mem a = GCSSem.read ac an a ii in
            let noact _ _ = M.mk_singleton_es Act.NoAction ii in
            M.altT (
              M.aarch64_cas_no (Access.is_physical ac) ma cmpoperand update read_mem noact branch M.neqT |> shortcut
            )(
              M.aarch64_cas_no (Access.is_physical ac) ma cmpoperand fault read_mem noact branch M.neqT |> shortcut
            )
          in
          let mop_fail_with_wb ac ma _ =
            (* GCSSS1 fails, there is an Explicit Write Effect writing back *)
            (* the value that is already in memory                          *)
            let read_mem a = GCSSem.read ac Annot.X a ii
            and write_mem a v = GCSSem.write ac Annot.X a v ii in
            M.altT(
                M.aarch64_cas_no (Access.is_physical ac) ma cmpoperand update read_mem write_mem branch M.neqT |> shortcut
              )(
                M.aarch64_cas_no (Access.is_physical ac) ma cmpoperand fault read_mem write_mem branch M.neqT |> shortcut
              )
          in
          let mop_success ac ma mv =
            (* GCSSS1 succeeds, there is an Explicit Write Effect *)
            (* mv is read new value from reg, not important       *)
            (* as this code is not executed in morello mode       *)
            (* In-progress cap entry should be stored if the comparison is successful *)
            let operand = mv >>= GCSSem.make_inprogress (* outgoing_pointer[63:3]:'101' *)
            and read_mem a = GCSSem.read ac Annot.X a ii
            and write_mem a v = GCSSem.write ac Annot.X a v ii in
           M.altT(
             M.aarch64_cas_ok (Access.is_physical ac) ma cmpoperand operand update read_mem write_mem branch M.eqT |> shortcut
            )(
              M.aarch64_cas_ok (Access.is_physical ac) ma cmpoperand operand fault read_mem write_mem branch M.eqT |> shortcut
            )
          in
          let mv = read_reg_data rA ii in
          let lift_memop ~tag rA dir updatedb checked mop perms ma mv an ii =
            do_lift_memop ~tag rA dir updatedb checked mop perms ma mv an ii Fun.id DISide.Data in
          do_cas_with lift_memop quad Annot.N r ma mv mop_success mop_fail_with_wb mop_fail_no_wb false ii)

    let gcsss2 r ii =
      let open AArch64Base in
      let an = Annot.N
      and rA = SysReg GCSPR_EL1
      and off = MachSize.nbytes quad in
      let m =
      M.delay_kont "gcsss2"
      (read_reg_addr rA ii)
      (fun a_virt ma ->
      let mop ac incoming =
        let m = GCSSem.read ac Annot.A incoming ii >>= fun outgoing ->
          let mask = V.intToV 0x7 in
          GCSSem.get_cap mask outgoing >>= fun cap ->
            let(>>*=) = M.bind_control_set_data_input_first in
            let commit =
              let cond = Printf.sprintf "InProgress([%s])" (V.pp_v incoming) in
              commit_pred_txt (Some cond) ii in
            let mok =
              commit >>*= fun () ->
                let mop ac a outgoing =
                  (GCSSem.reset_cap mask outgoing >>= M.add (V.intToV (-off)) >>= fun v -> write_reg r v ii) >>|
                   (M.add a_virt (V.intToV (off)) >>= fun new_addr ->
                      write_reg rA new_addr ii) >>|
                      (GCSSem.make_valid outgoing >>= fun outgoing_value -> GCSSem.write ac Annot.L a outgoing_value ii)
                in
                lift_memop r Dir.W true false
                (fun ac ma mv ->
                  if is_branching && Access.is_physical ac then
                    M.bind_ctrldata_data ma mv (fun a v -> mop ac a v)
                  else
                    ma >>| mv >>= fun (a,v) -> mop ac a v)
                (to_perms "w" quad)
                (GCSSem.reset_cap mask outgoing >>= M.add (V.intToV (-off)))
                (M.unitT outgoing)
                an
                ii in
            let inprogress = V.intToV 0x5 in
            M.delay_kont "gcsss2(fault)"
            (M.op Op.Ne cap inprogress)
            (fun notvalid action ->
              let open FaultType.AArch64 in
              let mno = GCSSem.mk_fault action (GCSCheck SS2) ii in
              let mok = action >>= fun _ -> mok in
              M.choiceT notvalid mno mok)
          in
        (* Register write and write to other stack depend on load from Shadow Stack *)
        let store e = (E.is_mem_store e) || (is_this_reg r e) in
        M.short (E.is_mem_load) store m in
      do_lift_memop rA Dir.R false false
      (fun ac ma _mv ->
        if Access.is_physical ac then
          M.bind_ctrldata ma (mop ac)
        else
          ma >>= mop ac)
      (to_perms "r" quad)
      ma
      mzero
      an
      ii
      Fun.id
      DISide.Data) in
      (* Value writen to GCSPR depends on previous read *)
      let read e = (is_this_reg rA e) && (E.is_reg_load e ii.A.proc)
      and write e = (is_this_reg rA e) && (E.is_reg_store e ii.A.proc) in
      M.short read write m


(********************)
(* Main entry point *)
(********************)
      (*
         Additonal type checking, control over discarded values.
         Namely, discarded value cannot be of type B.t, this would
         mean discarding a control flow result and replacing it
         systematically by B.Next. That way, some exit to end
         of code instructions would be ignored. See issue #287.
       *)

      let (!!!!) (m1:(unit list list * unit) M.t) =
        m1 >>= M.ignore >>= B.next1T
      let (!!!) (m1:(unit list * unit) M.t) =
        m1 >>= M.ignore >>= B.next1T
      let (!!) (m1:(unit * unit) M.t) = m1 >>= B.next2T
      let (!) (m1:unit M.t) = m1 >>= B.next1T
      let nextSet = B.nextSetT
      (* And now, just forget about >>! *)
      let [@warning "-32"](>>!) (_:unit) (_:unit) = ()

      let do_build_semantics test inst ii =
        let open AArch64Base in
        match inst with
        | I_NOP ->(* Instructions nop and branch below do not generate events, use a placeholder *)
           !(M.mk_singleton_es (Act.NoAction) ii)
        (* Branches *)
        | I_B l ->
           M.mk_singleton_es (Act.NoAction) ii
           >>= fun () -> M.unitT (B.Jump (tgt2tgt ii l,[]))
        | I_BC(c,l)->
           condition_holds ii c
           >>= fun v -> commit_bcc ii
           >>= fun () -> M.unitT (B.CondJump (v,tgt2tgt  ii l))
        | I_BL l ->
           let v_ret = get_link_addr test ii in
           if gcs then
             let branch bds =
               M.unitT (B.Jump (tgt2tgt ii l,bds)) in
             blop v_ret branch ii
           else
             let branch =
               let bds = [AArch64Base.linkreg,v_ret] in
               M.unitT (B.Jump (tgt2tgt ii l, bds)) in
             let write_lr = write_reg AArch64Base.linkreg v_ret ii in
             M.para_bind_output_right write_lr (fun () -> branch)
        | I_BR r as i ->
            read_reg_ord r ii >>= do_indirect_jump test [] i ii
        | I_BLR r as i ->
           let v_ret = get_link_addr test ii in
           let read_rn = read_reg_ord r ii in
           if gcs then
             let branch bds =
               read_rn >>= do_indirect_jump test bds i ii in
             blop v_ret branch ii
           else
             let branch =
               let bds = [AArch64Base.linkreg,v_ret] in
               read_rn >>= do_indirect_jump test bds i ii in
             let write_lr = write_reg AArch64Base.linkreg v_ret ii in
             M.para_bind_output_right write_lr (fun () -> branch)
        | I_RET None when C.variant Variant.Telechat ->
           M.unitT B.Exit
        | I_RET ro as i ->
            let r = match ro with
            | None -> AArch64Base.linkreg
            | Some r -> r in
              if gcs then
                retop test i r ii
              else
                read_reg_ord r ii >>= do_indirect_jump test [] i ii
        | I_ERET ->
           let eret_to_addr v =
              match v2tgt v with
              | Some tgt -> B.faultRetT tgt
              | _ ->
                 Warn.fatal "Cannot determine ERET target" in
           let commit_eret ii =
             M.mk_singleton_es (Act.Commit (Act.ExcReturn,None)) ii in
           commit_eret ii >>=
             fun () -> read_reg_ord AArch64.elr_el1 ii >>=
             eret_to_addr

        | I_SVC imm ->
          let (>>!) = M.(>>!) in
          let ft = Some FaultType.AArch64.SupervisorCall in
          let m_fault = mk_fault None Dir.R Annot.N ii ft None in
          let lbl_ret = get_link_addr test ii in
          let esr_val =
            Int64.logor
              (Int64.shift_left 0b0101011L  25) (* EC:IL for SVC, left shifted by ISS size *)
              (Int64.of_int imm)
            |> V.Cst.Scalar.of_int64 |> V.scalarToV in
          m_fault >>| (set_elr_el1 lbl_ret ii >>| set_esr_el1 esr_val ii)
          >>! B.syscall [(elr_el1, lbl_ret); (esr_el1, esr_val);]

        | I_CBZ(_,r,l) ->
            (read_reg_ord r ii)
              >>= is_zero
              >>= fun v -> commit_bcc ii
              >>= fun () -> M.unitT (B.CondJump (v,tgt2tgt ii l))

        | I_CBNZ(_,r,l) ->
            (read_reg_ord r ii)
              >>= is_not_zero
              >>= fun v -> commit_bcc ii
              >>= fun () -> M.unitT (B.CondJump (v,tgt2tgt ii l))

        | I_TBZ(_,r,k,l) ->
            (read_reg_ord r ii)
              >>= M.op1 (Op.ReadBit k)
              >>= is_zero
              >>= fun v -> commit_bcc ii
              >>= fun () -> M.unitT (B.CondJump (v,tgt2tgt ii l))
        | I_TBNZ(_,r,k,l) ->
            (read_reg_ord r ii)
              >>= M.op1 (Op.ReadBit k)
              >>= is_not_zero
              >>= fun v -> commit_bcc ii
              >>= fun () -> M.unitT (B.CondJump (v,tgt2tgt ii l))

        (* Load and Store *)
        | I_LDR(var,rd,rs,e) ->
            let sz = tr_variant var in
            ldr sz rd rs e ii
        | I_LDRSW(rd,rs,e) ->
            ldrsw rd rs e ii
        | I_LDRBH (bh, rd, rs, e) ->
            let sz = bh_to_sz bh in
            ldr sz rd rs e ii
        | I_LDRS ((v, bh), rd, rs, e) ->
            let sz = bh_to_sz bh in
            ldrs sz (tr_variant v) rd rs e ii
        | I_LDUR(var,rd,rs,k) ->
            let sz = tr_variant var in
            ldr sz rd rs (MemExt.k2idx k) ii
        | I_LDAR(var,t,rd,rs) ->
            let sz = tr_variant var in
            ldar sz t rd rs ii
        | I_LDARBH(bh,t,rd,rs) ->
            let sz = bh_to_sz bh in
            ldar sz t rd rs ii
        | I_STR(var,rs,rd,e) ->
            str (tr_variant var) rs rd e ii
        | I_STRBH(bh,rs,rd,e) ->
            str (bh_to_sz bh) rs rd e ii
        | I_STLR(var,rs,rd) ->
            stlr (tr_variant var) rs rd ii

        | I_STLRBH(bh,rs,rd) ->
            stlr (bh_to_sz bh) rs rd ii

        | I_STZG(rt,rn,(k,Idx)) ->
            check_memtag "STZG" ;
            stzg rt rn k ii
        | I_STZ2G(rt,rn,(k,Idx)) ->
            check_memtag "STZ2G" ;
            check_mixed "STZ2G" ;
            stz2g rt rn k ii

        | I_STG(rt,rn,(k,Idx)) ->
            check_memtag "STG" ;
            stg Once rt rn k ii
        | I_ST2G(rt,rn,(k,Idx)) ->
          check_memtag "ST2G" ;
          check_mixed "ST2G" ;
          st2g rt rn k ii
        | I_LDG (rt,rn,k) ->
            check_memtag "LDG" ;
            ldg rt rn k ii
        | I_IRG (rd,rn,rm) ->
            check_memtag "IRG" ;
            irg rd rn rm ii
        | I_STXR(var,t,rr,rs,rd) ->
            stxr (tr_variant var) t rr rs rd ii
        | I_STXRBH(bh,t,rr,rs,rd) ->
            stxr (bh_to_sz bh) t rr rs rd ii

        (* Neon operations *)
        | I_ADDV(var,r1,r2) ->
            check_neon inst;
            !(addv var r1 r2 ii)
        | I_DUP(r1,var,r2) ->
            check_neon inst;
            !(let sz = tr_variant var  in
              read_reg_ord_sz sz r2 ii >>= promote >>=
              fun v -> write_reg_neon_rep (neon_sz r1) r1 v ii)
        | I_FMOV_TG(_,r1,_,r2) ->
            check_neon inst;
            read_reg_neon Port.No r2 ii >>= demote
            >>= fun v -> write_reg_dest r1 v ii >>= nextSet r1
        | I_MOV_VE(r1,i1,r2,i2) ->
            check_neon inst;
            !(read_reg_neon_elem Port.No r2 i2 ii >>=
              fun v -> write_reg_neon_elem MachSize.S128 r1 i1 v ii)
        | I_MOV_FG(r1,i,var,r2) ->
            check_neon inst;
            !(let sz = tr_variant var in
              read_reg_ord_sz sz r2 ii >>= promote >>=
              fun v -> write_reg_neon_elem MachSize.S128 r1 i v ii)
        | I_MOV_TG(_,r1,r2,i) ->
            check_neon inst;
            !(read_reg_neon_elem Port.No r2 i ii >>= demote >>=
              fun v -> write_reg r1 v ii)
        | I_MOV_V(r1,r2) ->
            check_neon inst;
            !(read_reg_neon Port.No r2 ii >>=
              fun v -> write_reg_neon r1 v ii)
        | I_MOV_S(var,r1,r2,i) ->
            check_neon inst;
            !(let sz = tr_simd_variant var in
              read_reg_neon_elem Port.No r2 i ii >>=
              fun v -> write_reg_neon_sz sz r1 v ii)
        | I_MOVI_V(r,k,shift) ->
            check_neon inst;
            !(movi_v r k shift ii)
        | I_MOVI_S(var,r,k) ->
            check_neon inst;
            !(movi_s var r k ii)
        | I_OP3_SIMD(EOR,r1,r2,r3) ->
            check_neon inst;
            let sz = neon_sz r1 in
            !(read_reg_neon Port.No r3 ii >>|
              read_reg_neon Port.No r2 ii >>= fun (v1,v2) ->
                exclusive_or v1 v2 >>= fun v ->
                  write_reg_neon_sz sz r1 v ii)
        | I_ADD_SIMD(r1,r2,r3) ->
            check_neon inst;
            !(simd_add r1 r2 r3 ii)
        | I_ADD_SIMD_S(r1,r2,r3) ->
            check_neon inst;
            let sz = MachSize.Quad in
            !(read_reg_neon Port.No r3 ii >>|
              read_reg_neon Port.No r2 ii >>= sum_elems
              >>= fun v -> write_reg_neon_sz sz r1 v ii)
        (* Neon loads and stores *)
        | I_LDAP1(rs,i,rA,kr) ->
            check_neon inst;
            !!!(read_reg_addr rA ii >>= fun addr ->
            (mem_ss (load_elem_ldar MachSize.S128 i) addr rs ii >>|
            post_kr rA addr kr ii))
        | I_LD1(rs,i,rA,kr)
        | I_LD2(rs,i,rA,kr)
        | I_LD3(rs,i,rA,kr)
        | I_LD4(rs,i,rA,kr) ->
            check_neon inst;
            !!!(read_reg_addr rA ii >>= fun addr ->
            (mem_ss (load_elem MachSize.S128 i) addr rs ii >>|
            post_kr rA addr kr ii))
        | I_LD1R(rs,rA,kr)
        | I_LD2R(rs,rA,kr)
        | I_LD3R(rs,rA,kr)
        | I_LD4R(rs,rA,kr) ->
            check_neon inst;
            !!!(read_reg_addr rA ii >>= fun addr ->
            (mem_ss (load_elem_rep MachSize.S128) addr rs ii >>|
            post_kr rA addr kr ii))
        | I_LD1M(rs,rA,kr) ->
            check_neon inst;
            !!(read_reg_addr rA ii >>= fun addr ->
            (load_m_contigous addr rs ii >>|
            post_kr rA addr kr ii))
        | I_LD2M(rs,rA,kr)
        | I_LD3M(rs,rA,kr)
        | I_LD4M(rs,rA,kr) ->
            check_neon inst;
            !!(read_reg_addr rA ii >>= fun addr ->
            (load_m addr rs ii >>|
            post_kr rA addr kr ii))
        | I_STL1(rs,i,rA,kr) ->
            check_neon inst;
            !!!(read_reg_addr rA ii >>= fun addr ->
            (mem_ss (store_elem_stlr i) addr rs ii >>|
            post_kr rA addr kr ii))
        | I_ST1(rs,i,rA,kr)
        | I_ST2(rs,i,rA,kr)
        | I_ST3(rs,i,rA,kr)
        | I_ST4(rs,i,rA,kr) ->
            check_neon inst;
            !!!(read_reg_addr rA ii >>= fun addr ->
            (mem_ss (store_elem i) addr rs ii >>|
            post_kr rA addr kr ii))
        | I_ST1M(rs,rA,kr) ->
            check_neon inst;
            !!!!(read_reg_addr rA ii >>= fun addr ->
            (store_m_contigous addr rs ii >>|
            post_kr rA addr kr ii))
        | I_ST2M(rs,rA,kr)
        | I_ST3M(rs,rA,kr)
        | I_ST4M(rs,rA,kr) ->
            check_neon inst;
            !!!!(read_reg_addr rA ii >>= fun addr ->
            (store_m addr rs ii >>|
            post_kr rA addr kr ii))
        | I_LDR_SIMD(var,r1,rA,MemExt.Reg(v,kr,sext,s)) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            get_ea_reg rA v kr sext s ii >>= fun addr ->
            simd_ldr access_size addr r1 ii >>= B.next1T
        | I_LDR_SIMD(var,r1,rA,MemExt.Imm (k,Idx)) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            get_ea_idx rA k ii >>= fun addr ->
            simd_ldr access_size addr r1 ii >>= B.next1T
        | I_LDR_SIMD(var,r1,rA,MemExt.Imm (k,PreIdx)) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            get_ea_preindexed rA k ii >>= fun addr ->
            simd_ldr access_size addr r1 ii >>= B.next1T
        | I_LDR_SIMD(var,r1,rA,MemExt.Imm (k,PostIdx)) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            read_reg_addr rA ii >>= fun addr ->
            simd_ldr access_size addr r1 ii >>|
            post_kr rA addr (K k) ii >>= B.next2T
        | I_LDUR_SIMD(var,r1,rA,k) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            get_ea rA (K k) S_NOEXT ii >>= fun addr ->
            simd_ldr access_size addr r1 ii >>= B.next1T
        | I_LDAPUR_SIMD(var,r1,rA,k) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            get_ea rA (K k) S_NOEXT ii >>= fun addr ->
            simd_ldar access_size addr r1 ii >>= B.next1T
        | I_STR_SIMD(var,r1,rA,MemExt.Reg (v,kr,sext,s)) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            let ma = get_ea_reg rA v kr sext s ii in
            simd_str access_size ma r1 ii
        | I_STR_SIMD(var,r1,rA,MemExt.Imm (k,Idx)) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            let ma = get_ea_idx rA k ii in
            simd_str access_size ma r1 ii
        | I_STR_SIMD(var,r1,rA,MemExt.Imm (k,PreIdx)) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            let ma = get_ea_preindexed rA k ii in
            simd_str access_size ma r1 ii
        | I_STR_SIMD(var,r1,rA,MemExt.Imm (k,PostIdx)) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            let ma = read_reg_addr rA ii in
            simd_str_p access_size ma r1 rA (K k) ii
        | I_STUR_SIMD(var,r1,rA,k) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            let ma = get_ea_idx rA k ii in
            simd_str access_size ma r1 ii
        | I_STLUR_SIMD(var,r1,rA,k) ->
            check_neon inst;
            let access_size = tr_simd_variant var in
            let ma = get_ea_idx rA k ii in
            simd_stlr access_size ma r1 ii
        | I_LDP_SIMD(tnt,var,r1,r2,r3,idx) ->
          check_neon inst;
          begin
            match idx with
            | k,Idx ->
                get_ea_idx r3 k ii >>= fun addr ->
                  simd_ldp tnt var addr r1 r2 ii
            | k,PreIdx ->
                get_ea_preindexed r3 k ii >>= fun addr ->
                  simd_ldp tnt var addr r1 r2 ii
            | k,PostIdx ->
                read_reg_addr r3 ii >>= fun addr ->
                  (simd_ldp tnt var addr r1 r2 ii >>|
                  post_kr r3 addr (K k) ii) >>=
                  fun (b,()) -> M.unitT b
          end
        | I_STP_SIMD(tnt,var,r1,r2,r3,idx) ->
          check_neon inst;
          begin
            match idx with
            | k,Idx ->
                get_ea_idx r3 k ii >>= fun addr ->
                  simd_stp tnt var addr r1 r2 ii
            | k,PreIdx ->
                get_ea_preindexed r3 k ii >>= fun addr ->
                  simd_stp tnt var addr r1 r2 ii
            | k,PostIdx ->
                read_reg_addr r3 ii >>= fun addr ->
                  (simd_stp tnt var addr r1 r2 ii >>|
                    post_kr r3 addr (K k) ii) >>=
                  fun (b,()) -> M.unitT b
          end
        (* Scalable vector instructions *)
        | I_LD1SP(var,rs,p,rA,MemExt.Imm (k,Idx))
        | I_LD2SP(var,rs,p,rA,MemExt.Imm (k,Idx))
        | I_LD3SP(var,rs,p,rA,MemExt.Imm (k,Idx))
        | I_LD4SP(var,rs,p,rA,MemExt.Imm (k,Idx)) ->
          check_sve inst;
          !!!(let sz = tr_simd_variant var in
              let ma = get_ea_idx rA k ii in
              load_predicated_elem_or_zero_m sz p ma rs ii >>|
              M.unitT ())
        | I_LD1SP(var,rs,p,rA,MemExt.Reg (V64,rM,MemExt.LSL,s))
        | I_LD2SP(var,rs,p,rA,MemExt.Reg (V64,rM,MemExt.LSL,s))
        | I_LD3SP(var,rs,p,rA,MemExt.Reg (V64,rM,MemExt.LSL,s))
        | I_LD4SP(var,rs,p,rA,MemExt.Reg (V64,rM,MemExt.LSL,s)) ->
          check_sve inst;
          !!!(let sz = tr_simd_variant var in
              let ma = get_ea_reg rA V64 rM MemExt.LSL s ii in
              load_predicated_elem_or_zero_m sz p ma rs ii >>|
              M.unitT ())
        | I_LD1SP (var,rs,p,rA,MemExt.ZReg (rM,sext,s)) ->
          check_sve inst;
          !(let sz = tr_simd_variant var in
            let ma = read_reg_addr rA ii in
            let mo = read_reg_scalable Port.Addr rM ii in
            load_gather_predicated_elem_or_zero sz p ma mo rs sext s ii)
        | I_ST1SP(var,rs,p,rA,MemExt.Imm (k,Idx))
        | I_ST2SP(var,rs,p,rA,MemExt.Imm (k,Idx))
        | I_ST3SP(var,rs,p,rA,MemExt.Imm (k,Idx))
        | I_ST4SP(var,rs,p,rA,MemExt.Imm (k,Idx)) ->
          check_sve inst;
          !!!!(let sz = tr_simd_variant var in
              let ma = get_ea_idx rA k ii in
               store_predicated_elem_or_merge_m sz p ma rs ii >>|
               M.unitT ())
        | I_ST1SP(var,rs,p,rA,MemExt.Reg (V64,rM,MemExt.LSL,s))
        | I_ST2SP(var,rs,p,rA,MemExt.Reg (V64,rM,MemExt.LSL,s))
        | I_ST3SP(var,rs,p,rA,MemExt.Reg (V64,rM,MemExt.LSL,s))
        | I_ST4SP(var,rs,p,rA,MemExt.Reg (V64,rM,MemExt.LSL,s)) ->
          check_sve inst;
          !!!!(let sz = tr_simd_variant var in
              let ma = get_ea_reg rA V64 rM MemExt.LSL s ii in
               store_predicated_elem_or_merge_m sz p ma rs ii >>|
               M.unitT ())
        | I_ST1SP (var,rs,p,rA,MemExt.ZReg (rM,sext,s)) ->
          check_sve inst;
          !!!(let sz = tr_simd_variant var in
              let ma = read_reg_addr rA ii in
              let mo = read_reg_scalable Port.Addr rM ii in
              store_scatter_predicated_elem_or_merge sz p ma mo rs sext s ii >>|
              M.unitT ())
        | I_PTRUE(p,pattern) ->
          check_sve inst;
          ptrue p pattern ii
          >>= nextSet p
        | I_WHILELT(p,var,r1,r2) ->
          check_sve inst;
          while_op (M.op Op.Lt) false p var r1 r2 ii >>= B.nextBdsT
        | I_WHILELO(p,var,r1,r2) ->
          check_sve inst;
          while_op (M.op Op.Lt) true p var r1 r2 ii >>= B.nextBdsT
        | I_WHILELE(p,var,r1,r2) ->
          check_sve inst;
          while_op (M.op Op.Le) false p var r1 r2 ii >>= B.nextBdsT
        | I_WHILELS(p,var,r1,r2) ->
          check_sve inst;
          while_op (M.op Op.Le) true p var r1 r2 ii >>= B.nextBdsT
        |  I_ADD_SV (r1,r2,r3) ->
          check_sve inst;
          !(add_sv r1 r2 r3 ii)
        |  I_OP3_SV (EOR,r1,r2,r3) ->
          check_sve inst;
          !(read_reg_scalable Port.No r3 ii >>|
            read_reg_scalable Port.No r2 ii >>= fun (v1,v2) ->
              exclusive_or v1 v2 >>= fun v ->
                write_reg_scalable r1 v ii)
        | I_UADDV(var,v,p,z) ->
          check_sve inst;
          !(uaddv var v p z ii)
        | I_MOVPRFX(r1,pg,r2) ->
          check_sve inst;
          !(movprfx r1 pg r2 ii)
        | I_NEG_SV(r1,pg,r2) ->
          check_sve inst;
          !(neg r1 pg r2 ii)
        | I_MOV_SV(r,k,shift) ->
          check_sve inst;
          !(mov_sv r k shift ii)
        | I_DUP_SV(r1,var,r2) ->
          check_sve inst;
          !(let sz = tr_variant var  in
            read_reg_ord_sz sz r2 ii >>= promote >>= fun v ->
            write_reg_scalable_rep r1 v ii)
        | I_INDEX_SI (r1,var,r2,k) ->
            check_sve inst;
            let sz = tr_variant var  in
            let v2 = V.intToV k in
            read_reg_ord_sz sz r2 ii >>= fun v1 ->
            index r1 v1 v2 ii >>= nextSet r1
        | I_INDEX_IS (r1,var,k,r2) ->
            check_sve inst;
            let sz = tr_variant var  in
            let v1 = V.intToV k in
            read_reg_ord_sz sz r2 ii >>= fun v2 ->
            index r1 v1 v2 ii >>= nextSet r1
        | I_INDEX_SS (r1,var,r2,r3) ->
            check_sve inst;
            let sz = tr_variant var  in
            read_reg_ord_sz sz r2 ii >>|
            read_reg_ord_sz sz r3 ii >>= fun (v1,v2) ->
            index r1 v1 v2 ii >>= nextSet r1
        | I_INDEX_II (r1,k1,k2) ->
            check_sve inst;
            let v1 = V.intToV k1 in
            let v2 = V.intToV k2 in
            index r1 v1 v2 ii >>= nextSet r1
        | I_RDVL (rd,k) ->
           check_sve inst;
           let v = scalable_nbytes * k |> V.intToV in
           write_reg_sz_dest MachSize.Quad rd v ii
           >>= nextSet rd
        |I_ADDVL (rd,rn,k) ->
           check_sve inst;
           let sz = MachSize.Quad in
           let off = scalable_nbytes * k in
           read_reg_ord_sz sz rn ii
           >>= M.op1 (Op.AddK off)
           >>= fun v -> write_reg_sz_dest sz rd v ii
           >>= nextSet rd
        | I_CNT_INC_SVE (op,r,pat,k) ->
           check_sve inst;
           cnt_inc op r pat k ii >>= nextSet r
        | I_CTERM (cond,v,rn,rm) ->
            check_sve inst;
            let sz = tr_variant v in
            let op =
              let open CTERM in
              match cond with
              | EQ -> Op.Eq
              | NE -> Op.Ne in
            let reg_n = PState PSTATE.N
            and reg_c = PState PSTATE.C
            and reg_v =  PState PSTATE.V in
            (read_reg_ord_sz sz rn ii >>| read_reg_ord_sz sz rm ii)
            >>= fun (v1,v2) -> M.op op v1 v2
            >>= fun v -> M.choiceT v
              (write_reg_dest reg_n V.one ii >>| write_reg_dest reg_v V.zero ii)
              (write_reg_dest reg_n V.zero ii
               >>|
               begin
                 read_reg_ord reg_c ii (* V <- !C *)
                 >>= M.op Op.Xor V.one
                 >>= fun v -> write_reg_dest reg_v v ii
               end)
            >>= fun (n,v) -> B.nextBdsT [ reg_n,n ; reg_v,v; ]
        | I_SMSTART (None) ->
           check_sme inst;
           let pstate_sm = PState PSTATE.SM
           and pstate_za = PState PSTATE.ZA in
           let ops1,vals1 = reset_sm V.one ii in
           let ops2,vals2 = reset_za V.one ii in
           read_reg_ord pstate_sm ii >>|
           read_reg_ord pstate_za ii >>= fun (sm,za) ->
            M.op Op.Ne sm V.one >>|
            M.op Op.Ne za V.one >>= fun (diffsm,diffza) ->
              M.choiceT
              diffsm
              (M.choiceT diffza
               (List.fold_right (>>::) (ops1@ops2) (M.unitT [()]) >>= M.ignore >>= fun () -> M.unitT (B.Next (vals1@vals2)))
               (List.fold_right (>>::) ops1 (M.unitT [()]) >>= M.ignore >>= fun () -> M.unitT (B.Next vals1)))
              (M.choiceT diffza
               (List.fold_right (>>::) ops2 (M.unitT [()]) >>= M.ignore >>= fun () -> M.unitT (B.Next vals2))
              (B.nextT))
        | I_SMSTART (Some(PState PSTATE.SM)) ->
           check_sme inst;
           let pstate_sm = PState PSTATE.SM in
           let ops,vals = reset_sm V.one ii in
           read_reg_ord pstate_sm ii >>= fun sm ->
            M.op Op.Ne sm V.one >>= fun diff ->
              M.choiceT
              diff
              (List.fold_right (>>::) ops (M.unitT [()]) >>= M.ignore >>= fun () -> M.unitT (B.Next vals))
              (B.nextT)
        | I_SMSTART (Some(PState PSTATE.ZA)) ->
           check_sme inst;
           let pstate_za = PState PSTATE.ZA in
           let ops,vals = reset_za V.one ii in
           read_reg_ord pstate_za ii >>= fun sm ->
            M.op Op.Ne sm V.one >>= fun diff ->
              M.choiceT
              diff
              (List.fold_right (>>::) ops (M.unitT [()]) >>= M.ignore >>= fun () -> M.unitT (B.Next vals))
              (B.nextT)
        | I_SMSTOP (None) ->
          let pstate_sm = PState PSTATE.SM
          and pstate_za = PState PSTATE.ZA in
          let ops1,vals1 = reset_sm V.zero ii in
          let ops2,vals2 = reset_za V.zero ii in
          read_reg_ord pstate_sm ii >>|
          read_reg_ord pstate_za ii >>= fun (sm,za) ->
           M.op Op.Ne sm V.zero >>|
           M.op Op.Ne za V.zero >>= fun (diffsm,diffza) ->
             M.choiceT
             diffsm
             (M.choiceT diffza
              (List.fold_right (>>::) (ops1@ops2) (M.unitT [()]) >>= M.ignore >>= fun () -> M.unitT (B.Next (vals1@vals2)))
              (List.fold_right (>>::) ops1 (M.unitT [()]) >>= M.ignore >>= fun () -> M.unitT (B.Next vals1)))
             (M.choiceT diffza
             (List.fold_right (>>::) ops2 (M.unitT [()]) >>= M.ignore >>= fun () -> M.unitT (B.Next vals2))
             (B.nextT))
        | I_SMSTOP (Some(PState PSTATE.SM)) ->
           check_sme inst;
           let pstate_sm = PState PSTATE.SM in
           let ops,vals = reset_sm V.zero ii in
           read_reg_ord pstate_sm ii >>= fun sm ->
            M.op Op.Ne sm V.zero >>= fun diff ->
              M.choiceT
              diff
              (List.fold_right (>>::) ops (M.unitT [()]) >>= M.ignore >>= fun () -> M.unitT (B.Next vals))
              (B.nextT)
        | I_SMSTOP (Some(PState PSTATE.ZA)) ->
           check_sme inst;
           let pstate_za = PState PSTATE.ZA in
           let ops,vals = reset_za V.zero ii in
           read_reg_ord pstate_za ii >>= fun sm ->
            M.op Op.Ne sm V.zero >>= fun diff ->
              M.choiceT
              diff
              (List.fold_right (>>::) ops (M.unitT [()]) >>= M.ignore >>= fun () -> M.unitT (B.Next vals))
              (B.nextT)
        | I_MOVA_VT (za,ri,k,p,z) ->
           check_sme inst;
           mova_vt za ri k p z ii
           >>= nextSet za
        | I_MOVA_TV (z,p,za,ri,k) ->
           check_sme inst;
           mova_tv z p za ri k ii
           >>= nextSet z
        | I_ADDA (dir,za,p1,p2,z) ->
           check_sme inst;
           let pslice, pelem = match dir with
           | AArch64.Vertical -> p2,p1
           | AArch64.Horizontal -> p1,p2 in
           adda dir za pslice pelem z ii >>= nextSet za
        | I_LD1SPT (var,za,ri,k,p,rA,MemExt.Imm(0,Idx)) ->
           check_sme inst;
           !(let sz = tr_simd_variant var in
             let ma = read_reg_addr rA ii in
             load_predicated_slice sz za ri k p ma ii)
        | I_LD1SPT(var,za,ri,k,p,rA,MemExt.Reg (V64,rM,MemExt.LSL,s)) ->
          !(let sz = tr_simd_variant var in
            let ma = get_ea_reg rA V64 rM MemExt.LSL s ii in
            load_predicated_slice sz za ri k p ma ii)
        | I_ST1SPT (var,za,ri,k,p,rA,MemExt.Imm(0,Idx)) ->
           check_sme inst;
           !!!(let sz = tr_simd_variant var in
               let ma = read_reg_addr rA ii in
               store_predicated_slice sz za ri k p ma ii >>|
               M.unitT ())
        | I_ST1SPT (var,za,ri,k,p,rA,MemExt.Reg (V64,rM,MemExt.LSL,s)) ->
          !!!(let sz = tr_simd_variant var in
              let ma = get_ea_reg rA V64 rM MemExt.LSL s ii in
              store_predicated_slice sz za ri k p ma ii >>|
              M.unitT ())
        (* Morello instructions *)
        | I_ALIGND(rd,rn,k) ->
            check_morello inst ;
            !((read_reg_ord_sz MachSize.S128 rn ii >>=
            fun v -> M.op Op.Alignd v (V.intToV k))
            >>= fun v -> write_reg_sz MachSize.S128 rd v ii)
        | I_ALIGNU(rd,rn,k) ->
            check_morello inst ;
            !((read_reg_ord_sz MachSize.S128 rn ii >>=
            fun v -> M.op Op.Alignu v (V.intToV k))
            >>= fun v -> write_reg_sz MachSize.S128 rd v ii)
        | I_BUILD(rd,rn,rm) ->
            check_morello inst ;
            !(begin
              read_reg_ord_sz MachSize.S128 rn ii >>|
              read_reg_ord_sz MachSize.S128 rm ii
            end >>= fun (a,b) ->
            M.op Op.Build a b >>= fun v ->
            write_reg_sz MachSize.S128 rd v ii)
        | I_CHKEQ(rn,rm) ->
            check_morello inst ;
            !(begin
              read_reg_ord_sz MachSize.S128 rn ii >>|
              read_reg_ord_sz MachSize.S128 rm ii
            end >>= fun (v1,v2) ->
            M.op Op.Eq v1 v2 >>= fun v ->
            write_reg (PState PSTATE.N) v ii)
        | I_CHKSLD(rn) ->
            check_morello inst ;
            !(read_reg_ord_sz MachSize.S128 rn ii >>= fun v ->
            M.op1 Op.CheckSealed v >>= fun v -> write_reg (PState PSTATE.V) v ii)
        | I_CHKTGD(rn) ->
            check_morello inst ;
            !(read_reg_ord_sz MachSize.S128 rn ii >>= fun v ->
              M.op1 Op.CapaGetTag v >>= fun v ->
              write_reg (PState PSTATE.C) v ii)
        | I_CLRTAG(rd,rn) ->
            check_morello inst ;
            !(read_reg_ord_sz MachSize.S128 rn ii >>= fun (v) ->
            M.op Op.CapaSetTag v V.zero >>= fun v ->
            write_reg_sz MachSize.S128 rd v ii)
        | I_CPYTYPE(rd,rn,rm) ->
            check_morello inst ;
            !(begin
              read_reg_ord_sz MachSize.S128 rn ii >>|
              read_reg_ord_sz MachSize.S128 rm ii
            end >>= fun (v1,v2) -> M.op Op.CpyType v1 v2 >>= fun v ->
            write_reg_sz MachSize.S128 rd v ii)
        | I_CPYVALUE(rd,rn,rm) ->
            check_morello inst ;
            !(begin
              read_reg_ord_sz MachSize.S128 rn ii >>|
              read_reg_ord_sz MachSize.S128 rm ii
            end >>= fun (v1,v2) -> M.op Op.SetValue v1 v2 >>= fun v ->
            write_reg_sz MachSize.S128 rd v ii)
        | I_CSEAL(rd,rn,rm) ->
            check_morello inst ;
            !(begin
              read_reg_ord_sz MachSize.S128 rn ii >>|
              read_reg_ord_sz MachSize.S128 rm ii
            end >>= fun (v1,v2) ->
            M.op Op.CSeal v1 v2 >>= fun v ->
            (
            write_reg_sz MachSize.S128 rd v ii |||
            (* TODO: PSTATE overflow flag would need to be conditionally set *)
            write_nzcv_no_next M.A.V.(zero, zero, zero, zero) ii))
        | I_GC(op,rd,rn) ->
            check_morello inst ;
            !(read_reg_ord_sz MachSize.S128 rn ii >>= begin fun c -> match op with
            | CFHI -> M.op1 (Op.LogicalRightShift 64) c
            | GCFLGS -> M.op1 (Op.AndK "0xff00000000000000") c
            | GCPERM -> M.op1 (Op.LogicalRightShift 110) c
            | GCSEAL -> M.op1 (Op.LeftShift 18) c >>= fun v ->
                M.op1 (Op.LogicalRightShift 113) v >>= fun v -> is_not_zero v
            | GCTAG -> M.op1 Op.CapaGetTag c
            | GCTYPE -> M.op1 (Op.LeftShift 18) c >>= fun v ->
                M.op1 (Op.LogicalRightShift 113) v
            | GCVALUE -> M.op1 (Op.Mask MachSize.Quad) c
            end >>= fun v -> write_reg_sz MachSize.Quad rd v ii)
        | I_SC(op,rd,rn,rm) ->
            check_morello inst ;
            !(begin
              read_reg_ord_sz MachSize.S128 rn ii >>|
              read_reg_ord rm ii
            end >>=
            begin fun (cn, xm) -> match op with
              | CLRPERM -> M.op Op.ClrPerm cn xm
              | CTHI -> M.op Op.Cthi cn xm
              | SCFLGS ->
                begin
                  M.op1 (Op.AndK "0x00ffffffffffffff") cn >>|
                  M.op1 (Op.AndK "0xff00000000000000") xm
                end >>= fun (v,k) -> M.op Op.Or v k >>= fun v -> M.op Op.SetValue cn v
              | SCTAG -> M.op1 (Op.ReadBit 0) xm >>= fun cond ->
                  M.op Op.CapaSetTag cn cond
              | SCVALUE -> M.op Op.SetValue cn xm
            end >>= fun v ->
            write_reg_sz MachSize.S128 rd v ii)
        | I_SEAL(rd,rn,rm) ->
            check_morello inst ;
            !(begin
              read_reg_ord_sz MachSize.S128 rn ii >>|
              read_reg_ord_sz MachSize.S128 rm ii
            end >>= fun (a,b) ->
            M.op Op.Seal a b >>= fun v ->
            write_reg_sz MachSize.S128 rd v ii)
        | I_STCT(rt,rn) ->
            check_morello inst ;
            (* NB: only 1 access implemented out of the 4 *)
            lift_morello
              (fun _ac ma mv ->
                do_insert_commit
                  (ma >>| mv)
                  (fun (a,v) -> !(do_write_morello_tag a v ii))
                  ii)
              (to_perms "tw" MachSize.S128)
              (read_reg_addr rn ii)
              (read_reg_ord rt ii)
              Dir.W Annot.N ii (fun a -> a >>= M.ignore >>= B.next1T)
        | I_LDCT(rt,rn) ->
            check_morello inst ;
            (* NB: only 1 access implemented out of the 4 *)
            lift_morello
              (fun _ac ma _mv ->
                M.delay_kont "LDCT" ma
                  (fun _a ma ->
                    do_insert_commit ma
                      (fun a -> (* Why check permissions again ? *)
                        M.op (Op.CheckPerms "tr_c") a M.A.V.zero >>= fun v ->
                        M.choiceT v
                          (do_read_morello_tag a ii)
                          mzero
                        >>= fun tag -> !(write_reg_sz quad rt tag ii))
                      ii))
              (to_perms "r" MachSize.S128)
              (read_reg_addr rn ii)
              mzero
              Dir.R Annot.N
              ii (fun a -> a >>= M.ignore >>= B.next1T)
        | I_UNSEAL(rd,rn,rm) ->
            check_morello inst ;
            !(begin
              read_reg_ord_sz MachSize.S128 rn ii >>|
              read_reg_ord_sz MachSize.S128 rm ii
            end >>= fun (a,b) ->
            M.op Op.Unseal a b >>= fun v ->
            write_reg_sz MachSize.S128 rd v ii)

        (* Operations *)
        | I_MOV(var,r,K k) ->
            mask32 var
               (fun k ->
                 write_reg_dest r k ii
                 >>= nextSet r)
               (V.intToV k)
        | I_MOV(var,r1,RV (_,r2)) ->
            let sz = tr_variant var in
            read_reg_ord_sz sz r2 ii
            >>= fun v -> write_reg_dest r1 v ii
            >>= nextSet r1
        | I_MOVZ(var,rd,k,os) ->
           movz var rd k os ii >>= nextSet rd
        | I_MOVN (var,rd,k,os) ->
           movn var rd k os ii >>= nextSet rd
        | I_MOVK(var,rd,k,os) ->
            movk var rd k os ii >>= nextSet rd
        | I_ADR (r,tgt) ->
           let lbl =
             let open BranchTarget in
             match tgt with
             | Lbl lbl -> Some lbl
             | Offset o ->
                begin
                  let a = ii.A.addr + o in
                  let lbls = test.Test_herd.entry_points a in
                  Label.norm lbls
                end in
           begin
             match lbl with
             | Some lbl ->
                let v = ii.A.addr2v ii.A.proc lbl in
                write_reg_dest r v ii >>= nextSet r
             | None ->
                (* Delay error, only a poor fix.
                   A complete possible fix would be
                   having code addresses as values *)
                M.failT
                  (Misc.Fatal "Overwriting  with ADR, cannot handle")
                  B.Exit
           end
        | I_RBIT (v,rd,rn) ->
            let sz = tr_variant v in
            read_reg_ord_sz sz rn ii
            >>= M.op1 (Op.Rbit sz)
            >>= fun v -> write_reg_dest rd v ii
            >>= nextSet rd
        | I_SXTW(rd,rs) ->
            read_reg_ord_sz MachSize.Word rs ii
            >>=  sxtw_op
            >>= fun v -> write_reg_dest rd v ii
            >>= nextSet rd
        | I_ABS (v,rd,rs) ->
           let sz = tr_variant v in
           read_reg_ord_sz sz rs ii
           >>= sxt_op sz
           >>= M.op1 Op.Abs
           >>=fun v -> write_reg_dest rd v ii
           >>= nextSet rd
        | I_REV (rv,rd,rs) ->
           let sz = variant_of_rev rv |> tr_variant in
           read_reg_ord_sz sz rs ii
           >>= M.op1 (Op.RevBytes (container_size rv,sz))
           >>= fun v -> write_reg_dest rd v ii
           >>= nextSet rd
           | I_OP3(v,op,rd,rn,e) ->
           let margs =
             let sz = tr_variant v in
             let mn = read_reg_ord_sz sz rn ii in
             begin
               let open AArch64.OpExt in
               match e with
               | Imm (k,s) ->
                  mn >>| lsl_op s  (V.intToV k)
               | OpExt.Reg (r,s) when AArch64Base.reg_compare rn r = 0
                 ->
                  mn >>= fun v1 -> M.unitT v1 >>| opext_shift sz s v1
               | Reg (r,s) ->
                  mn >>|  (read_reg_ord_sz sz r ii >>= opext_shift sz s)
             end in
           mop3 inst v op rd  margs ii
        | I_EXTR (v,rd,rn,rm,lsb) ->
           let sz = tr_variant v in
           let nbits = MachSize.nbits sz in
           begin
             (read_reg_ord_sz sz rm ii
              >>= M.op1 (Op.LogicalRightShift lsb))
             >>|
               (read_reg_ord_sz sz rn ii
                >>= M.op1  (Op.LeftShift (nbits-lsb)))
           end
           >>= fun (v1,v2) -> M.op Op.Or v1 v2
           >>= fun v -> write_reg_dest rd v ii
           >>= nextSet rd
        | I_ADDSUBEXT (v,op,r1,r2,(v3,r3),(e,ko)) ->
           let op =
             match op with
             | Ext.ADD -> ADD
             | Ext.ADDS -> ADDS
             | Ext.SUB -> SUB
             | Ext.SUBS -> SUBS in
           let sz = tr_variant v in
           let m2 = read_reg_ord_sz sz r2 ii in
           let m3 =
             read_reg_ord_sz (tr_variant v3) r3 ii
             >>= ext_sext e ko in
           mop3 inst v op r1 (m2 >>| m3) ii
        | I_MOPL ((s,op),rd,rn,rm,ra) ->
           let ext =
             match s with
             | MOPLExt.Signed -> sxtw_op
             | MOPLExt.Unsigned -> M.unitT
           and op =
               match op with
               | MOPLExt.ADD -> Op.Add
               | MOPLExt.SUB -> Op.Sub in
           begin
             (read_reg_ord_sz MachSize.Word rn ii >>= ext)
             >>| (read_reg_ord_sz MachSize.Word rm ii >>= ext)
             >>| read_reg_ord ra ii
           end >>= fun ((vn,vm),va) ->
           M.op Op.Mul vn vm
           >>= M.op op va
           >>= fun v -> write_reg_dest rd v ii
           >>= nextSet rd
        | I_MOP (op,v,rd,rn,rm,ra) ->
           let op =
               match op with
               | MOPExt.ADD -> Op.Add
               | MOPExt.SUB -> Op.Sub
           and sz = tr_variant v in
           begin
             (read_reg_ord_sz sz rn ii)
             >>| (read_reg_ord_sz sz rm ii)
             >>| read_reg_ord_sz sz ra ii
           end >>= fun ((vn,vm),va) ->
           M.op Op.Mul vn vm
           >>= M.op op va
           >>= fun v -> write_reg_dest rd v ii
           >>= nextSet rd
        (* Barrier *)
        | I_FENCE b ->
            begin match b with
            | AArch64Base.GCSB -> check_gcs inst
            | _ -> ()
            end;
            !(create_barrier b ii)
              (* Conditional selection *)
        | I_CSEL (var,r1,r2,r3,c,op) ->
            let sz = tr_variant var in
            let mask = match op with
            | Cpy -> fun m -> m
            | Inc|Inv|Neg -> mask32 var in
            !(if not (C.variant Variant.NotWeakPredicated) then
                let(>>*=) = M.bind_control_set_data_input_first in
                let mok = commit_pred_txt (Some (pp_cond c)) ii >>*=
                  fun () -> read_reg_ord_sz sz r2 ii >>=
                  fun v -> write_reg r1 v ii in
                let mno = commit_pred_txt None ii >>*=
                  fun () -> read_reg_ord_sz sz r3 ii >>=
                  csel_op op >>= mask (fun v ->  write_reg r1 v ii) in
                condition_holds ii c >>= fun v -> M.choiceT v mok mno
            else
              begin
                condition_holds ii c
                >>|  read_reg_data_sz sz r2 ii
                >>| read_reg_data_sz sz r3 ii
              end >>= fun ((v,v2),v3) ->
              M.condPredT v
                (M.unitT ())
                (write_reg r1 v2 ii)
                (csel_op op v3 >>= mask (fun v ->  write_reg r1 v ii)))

        | I_SBFM (v,rd,rn,kr,ks) -> xbfm true v rd rn kr ks ii
        | I_UBFM (v,rd,rn,kr,ks) -> xbfm false v rd rn kr ks ii

        (* Swap *)
        | I_SWP (v,rmw,r1,r2,r3) -> swp (tr_variant v) rmw r1 r2 r3 ii
        | I_SWPBH (v,rmw,r1,r2,r3) -> swp (bh_to_sz v) rmw r1 r2 r3 ii
(* Compare & Swap *)
        | I_CAS (v,rmw,rs,rt,rn) ->
            (* TODO: unify cas functions *)
            let cas = if morello then cas_morello else cas in
            cas (tr_variant v) rmw rs rt rn ii
        | I_CASBH (v,rmw,rs,rt,rn) ->
            (* TODO: unify cas functions *)
            let cas = if morello then cas_morello else cas in
            cas (bh_to_sz v) rmw rs rt rn ii
        | I_CASP (v,rmw,rs1,rs2,rt1,rt2,rn) ->
            casp (tr_variant v) rmw rs1 rs2 rt1 rt2 rn ii
(* Fetch and Op *)
        | I_STOP (op,v,w,rs,rn) ->
            ldop op (tr_variant v) (w_to_rmw w) rs ZR rn ii
        | I_LDOP (op,v,rmw,rs,rt,rn) ->
            ldop op (tr_variant v) rmw rs rt rn ii
        | I_STOPBH (op,v,w,rs,rn) ->
            ldop op (bh_to_sz v) (w_to_rmw w) rs ZR rn ii
        | I_LDOPBH (op,v,rmw,rs,rt,rn) ->
            ldop op (bh_to_sz v) rmw rs rt rn ii
(* Address translation operation *)
        | I_AT (op, rd) -> do_at op rd ii
(* Page tables and TLBs *)
        | I_TLBI (op, rd) ->
            !(read_reg_addr rd ii >>= fun a -> do_inv op a ii)
(* Data cache instructions *)
        | I_DC (op,rd) -> do_dc op rd ii
(* Instruction-cache maintenance instruction *)
        | I_IC (op,rd) -> do_ic op rd ii
(* Load/Store pairs *)
        | I_LDP (tnt,v,r1,r2,r3,idx) ->
            ldp tnt (tr_variant v) r1 r2 r3 idx ii
        | I_LDPSW (r1,r2,r3,idx) ->
            ldpsw r1 r2 r3 idx ii
        | I_STP (tnt,v,r1,r2,r3,idx) ->
            stp tnt (tr_variant v) r1 r2 r3 idx ii
        | I_LDXP (v,t,r1,r2,r3) ->
            ldxp (tr_variant v) t r1 r2 r3 ii
        | I_STXP (v,t,r1,r2,r3,r4) ->
            stxp (tr_variant v) t r1 r2 r3 r4 ii
(*
 * Read/Write system registers.
 * Notice thar NZCV is special:
 * Our NZCV register is a direct representation of
 * PSTATE.<N,Z,C,V>, while SYS_NZCV is here only
 * as an argument to the MRS and MSR instructions.
 *)
        | I_MSR (sreg,xt) -> begin
            let sz = MachSize.Quad in
            match sreg with
            | SYS_NZCV ->
              read_reg_ord_sz sz xt ii
              >>= fun v -> M.op1 (Op.LogicalRightShift 28) v
              >>= M.op1 (Op.AndK "0b1111")
              >>= fun v -> write_nzcv_one_val v ii
              >>= fun sets -> M.unitT (B.Next sets)
            | _ -> begin
              let off = AArch64.sysreg_nv2off sreg in
              match C.variant Variant.NV2, off with
              | true, Some off ->
                let rd = SysReg AArch64.VNCR_EL2 in
                str_simple sz xt rd (get_ea_idx rd off ii) ii
              | _, _ ->
                read_reg_ord_sz sz xt ii
                >>= fun v -> write_reg_dest (SysReg sreg) v ii
                >>= nextSet (SysReg sreg)
            end
          end
        | I_MRS (xt,sreg) ->
          begin
            match sreg with
            | SYS_NZCV ->
               read_nzcv ii
               >>= M.op1 (Op.LeftShift 28)
               >>= fun v -> write_reg_dest xt v ii
               >>= nextSet xt
            | _ -> begin
              let sz = MachSize.Quad in
              let off = AArch64.sysreg_nv2off sreg in
              match C.variant Variant.NV2, off with
              | true, Some off ->
                let rs = SysReg AArch64.VNCR_EL2 in
                let e = MemExt.Imm (off, Idx) in
                ldr sz xt rs e ii
              | _, _ ->
                read_reg_ord_sz sz (SysReg sreg) ii
                >>= fun v -> write_reg_dest xt v ii
                >>= nextSet xt
            end
          end
        | I_UDF _ ->
           let (>>!) = M.(>>!) in
           let ft = Some FaultType.AArch64.UndefinedInstruction in
           let m_fault = mk_fault None Dir.R Annot.N ii ft None in
           let lbl_v = get_instr_label ii.A.proc ii in
           m_fault >>| set_elr_el1 lbl_v ii
           >>! B.fault [AArch64Base.elr_el1, lbl_v]
(* Pointer Anthentication Code *)
        | I_PAC (key, rd, rn) ->
            check_pac inst;
            do_pac key rd rn ii
        | I_AUT (key, rd, rn) ->
            check_pac inst;
            do_aut key rd rn ii
        | I_XPACI r | I_XPACD r ->
            check_pac inst;
            do_xpac r ii
(* Guarded Control Stack *)
        | I_GCSPOPM rd ->
          check_gcs inst;
          gcspopm rd ii
        | I_GCSPUSHM rs ->
          check_gcs inst;
          gcspushm rs ii
        | I_GCSSTR (r1,r2) ->
          check_gcs inst;
          gcsstr r1 r2 ii
        | I_GCSSS1 r ->
          check_gcs inst;
          gcsss1 r ii
        | I_GCSSS2 r ->
          check_gcs inst;
          gcsss2 r ii
(*  Cannot handle *)
        (* | I_BL _|I_BLR _|I_BR _|I_RET _ *)
        | (I_STG _|I_ST2G _|I_STZG _|I_STZ2G _
        | I_OP3_SIMD _ | I_OP3_SV _
        | I_LDR_SIMD _| I_STR_SIMD _
        | I_LD1SP _| I_LD2SP _| I_LD3SP _| I_LD4SP _
        | I_ST1SP _|I_ST2SP _|I_ST3SP _|I_ST4SP _
        | I_SMSTART _ | I_SMSTOP _ |I_LD1SPT _ |I_ST1SPT _) as i ->
            Warn.fatal "illegal instruction: %s" (AArch64.dump_instruction i)

(* Compute a safe set of instructions that can
 * overwrite another. By convention, those are
 * instructions pointed to by "exported" labels.
 *)
      let get_overwriting_instrs test =
        AArch64.state_fold
          (fun _ v k ->
            match v with
            | V.Val (Constant.Instruction i) -> i::k
            | _ -> k)
          test.Test_herd.init_state []

      let get_instr_ptevals test =
        let open Constant in
        let open AArch64PteVal in
        AArch64.state_fold
          (fun _ v k ->
            match v with
            | V.Val (PteVal pte_v) -> begin
              let lbl_opt =
                pte_v.oa
                |> OutputAddress.as_physical
                |> fun o -> Option.bind o Misc.str_as_label in
              match lbl_opt with
              | Some lbl -> lbl::k
              | None -> k
              end
            | _ -> k)
          test.Test_herd.init_state []

      let lift_fetch rA (* Base address register *)
            dir updatedb
            mop
            perms ma mv an ii =
        let domain = DISide.Instr in
        do_lift_memop rA dir updatedb false mop perms ma mv an ii Fun.id domain

(* Test all possible instructions, when appropriate *)
      let mk_mop_fetch exposed_page exposed_label test ii =
        let module InstrSet = AArch64.V.Cst.Instr.Set in
        let relevant_pagelbls = get_instr_ptevals test in
       
        let default_cands =
          InstrSet.empty
          |> InstrSet.add ii.A.inst
        in
        let exposed_page_cands =
          (* When an address can get remapped, consider the possibility of
           * fetching instructions from other relevant pages *)
          if exposed_page then
            let offset = (ii.A.addr mod Pseudo.proc_size) mod Pseudo.page_size in
            relevant_pagelbls
            |> List.map (fun (_,lbl) ->
                let base = Label.Map.find lbl test.Test_herd.program in
                let cand_a = base + offset in
                let cand_i = match IntMap.find cand_a test.Test_herd.code_segment with
                | (_,(_,i)::_) -> i.A.CodeInstr.instr
                (* this case means that we have found a relevant page, but it
                does not have an instruction -- currently throws an error, but
                a convention to assume NOP could be envisioned *)
                | _ -> Warn.user_error "Instruction not found by the address %d" cand_a
                in
                cand_i)
             |> InstrSet.of_list
          else InstrSet.empty
        in
        let potentially_exposed_label =
          (* When an address can get remapped, check if the possible remapped
           * addresses needs the ifetch logic *)
          let no_remap_case = exposed_label ii.A.addr in
          if exposed_page then
            let offset = (ii.A.addr mod Pseudo.proc_size) mod Pseudo.page_size in
            relevant_pagelbls
            |> List.map (fun (_,lbl) ->
                let base = Label.Map.find lbl test.Test_herd.program in
                let cand_a = base + offset in
                exposed_label cand_a)
            |> List.fold_left (fun acc a -> acc || a) no_remap_case
          else no_remap_case
        in
        let exposed_label_cands =
          (if potentially_exposed_label then
            get_overwriting_instrs test
            |> InstrSet.of_list (* optimization to consider only possible instruction overwrites *)
            |> InstrSet.filter AArch64.can_overwrite (* for testing purposes *)
          else InstrSet.empty)
        in
        let cands =
          default_cands
          |> InstrSet.union exposed_page_cands
          |> InstrSet.union exposed_label_cands
        in
        (* Shadow default control sequencing operator *)
        let(>>*=) = M.bind_control_set_data_input_first in
        let mop ac a =
          read_loc_instr (A.Location_global a) ac ii
          >>= fun actual_val ->
            InstrSet.fold
              (fun inst k ->
                M.op Op.Eq actual_val (V.instructionToV inst) >>==
                fun cond -> M.choiceT cond
                    (commit_pred_txt (Some "decode") ii >>*=
                      fun () -> do_build_semantics test inst ii)
                    k)
              cands
              begin
              (* Anything else than a legit instruction is a failure *)
                let (>>!) = M.(>>!) in
                let m_fault = mk_fault None Dir.R Annot.N ii
                    (Some FaultType.AArch64.UndefinedInstruction)
                    None in
                let lbl_v = get_instr_label ii.A.proc ii in
                commit_pred_txt (Some "decode") ii
                  >>*= fun () -> m_fault >>| set_elr_el1 lbl_v ii
                  >>! B.Fault (false,[AArch64Base.elr_el1, lbl_v])
              end in
        fun ac ma _ -> (
          if Access.is_physical ac then
            M.bind_ctrldata ma (mop ac)
          else
            ma >>= mop ac
        )

(* Test all possible instructions, when appropriate *)
      let check_self test ii =
        let module InstrSet = AArch64.V.Cst.Instr.Set in
        let exp_pages = get_exposed_codepages test in
        let is_on_exported_page =
          match ii.A.rel_addr with
          | Some (A.V.Val c) -> begin
            let this_lbl = c in 
            List.exists
              (fun ttd_lbl ->
                let this_triple = Constant.unmk_sym_virtual_label_with_offset this_lbl in
                let ttd_triple = Constant.unmk_sym_virtual_label_with_offset ttd_lbl in
                match (this_triple,ttd_triple) with
                | (p1,s1,_),(p2,s2,_) ->
                  (Misc.int_eq p1 p2) && (Misc.string_eq s1 s2)
              ) exp_pages
            end
          | _ -> false
        in

        let lbl_exposed addr =
          let labels = test.Test_herd.entry_points addr in
          Label.Set.exists
            (fun lbl ->
              Label.Full.Set.exists
                (fun (_,lbl0) -> Misc.string_eq lbl lbl0)
                (get_exported_labels test))
            labels in

        let needs_vmsa_for_ifetch = (* checks if the logic for VA remapping needed *)
          kvm && self && is_on_exported_page in
        let needs_ifetch = (* checks if the logic for instruction overwrite needed *)
          (lbl_exposed ii.A.addr) && self in
        if needs_ifetch || needs_vmsa_for_ifetch then
          let mop_fetch = mk_mop_fetch is_on_exported_page lbl_exposed test ii in
          let a_v =
            if needs_vmsa_for_ifetch then begin
              match ii.A.rel_addr with
              | Some v -> v
              | None -> Warn.fatal "Failure to identify the label corresponding to the start of a page holding the instruction %s by the address %d" (A.pp_instruction PPMode.Ascii ii.A.inst) ii.A.addr
            end else get_instr_label ii.A.fetch_proc ii
          in
          lift_fetch AArch64.ZR Dir.R true
            mop_fetch
            (to_perms "r" MachSize.Word)
          (M.unitT a_v) mzero Annot.N ii
        else
          do_build_semantics test ii.A.inst ii

      let build_semantics test ii =
        M.addT (A.next_po_index ii.A.program_order_index)
          begin
            if self then check_self test ii
            else do_build_semantics test ii.A.inst ii
          end

      let can_unset_af_loc e =
        match E.access_of e with
        | Some Access.(PTE _|PHY_PTE)
          ->
            begin
              match E.location_of e,E.written_of e with
              | Some (A.Location_global loc),Some v ->
                  if E.is_explicit e && can_be_pt loc && can_af0 v then Some loc
                  else None
              | _ -> None
            end
        | _ -> None

      let spurious_setaf ~value ~location =
        test_and_set_af_succeeds value location E.IdSpurious DISide.Data

    end

  end
