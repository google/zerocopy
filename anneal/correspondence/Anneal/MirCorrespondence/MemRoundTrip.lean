-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirCorrespondence.Codec
import Anneal.MirCorrespondence.SimHelpers
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.EnumEquiv
import Anneal.MirCorrespondence.MemAlloc
import Anneal.MirCorrespondence.ValidateLocal
import Anneal.MirCorrespondence.ByteCodec
import Anneal.MirCorrespondence.RetPlace
import Anneal.MirCorrespondence.CopyReturnScalar
import Anneal.MirCorrespondence.CopyReturnPair

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Miri.ABI Miri.Memory Miri.Interpreter

/-- Executing `ExecutionControl.hooks.copyReturn` (`copyRuntimePlace` into the
fresh caller-owned `retPlace` allocation) on an initialized Day-1 return value
`v` succeeds, updates only `st.machine.memory` to `mem'`, and satisfies
`refReadReturnVal mem' retTy retPlace = .ok v`. -/
theorem copyReturn_ok (rp : RefProg) (c : Choice) (retTy : MirTy) (v : Val)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, retPlace))
    (h_mem : st.machine.memory = mem)
    (h_dr : st.machine.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_cv : checkVal v retTy = true)
    (h_res : resolveTy rp.types (tyIdFor rp.types retTy) = some retTy) :
    let h := Miri.Interpreter.ExecutionMachine.withValidation
      (refExecutionConfig rp) refLimits
    ∃ mem',
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate (valToMiriImmediate retTy v),
            refLocalLayoutForTy rp.types retTy⟩
          ⟨.memory retPlace.mplace, retPlace.layout⟩ true st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      refReadReturnVal mem' retTy retPlace = .ok v := by
  let ⟨mem1, rawAlloc, h_raw, _, _, _, _, _, _, h_mem_shape, h_rp_shape⟩ :=
    refInitMemoryAndRetPlace_shape rp.types retTy h_init
  rw [h_mem_shape] at h_mem
  rw [h_rp_shape]
  change let h := Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits
    ∃ mem',
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate (valToMiriImmediate retTy v),
            refLocalLayoutForTy rp.types retTy⟩
          ⟨.memory retMemPlace, refLocalLayoutForTy rp.types retTy⟩ true st =
        .ok () { st with machine := { st.machine with memory := mem' } } ∧
      refReadReturnVal mem' retTy ⟨retMemPlace, refLocalLayoutForTy rp.types retTy⟩ = .ok v
  cases checkVal_eq_true_inv h_cv with
  | inl h_i =>
    let ⟨w, s, bits, hty, hv, h_trunc⟩ := h_i
    subst hty hv
    let ⟨after, h_wm, h_rd, h_cp, h_asz, h_amut, _⟩ :=
      writeMemory_retPlace_scalar w (refLocalLayoutForTy rp.types (.int w s))
        (.Initialized (value := .Int (toMiriInteger w) s)
          (validRange := refFullWrappingRangeSize (toMiriSize w)))
        bits mem1 st rfl rfl (by cases w <;> cases s <;> rfl) trivial
        h_raw h_mem h_dr
    let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit :=
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let st1 := { st with machine := { st.machine with memory := mem' } }
    have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
        (refValHooks rp.types) c 8
        ⟨.memory retMemPlace, refLocalLayoutForTy rp.types (.int w s)⟩
        false true st1 = .ok () st1 :=
      validatePlace_mem_scalar_step rp.types c w _ st1 rfl
        (visit_mem_int_ok rp.types c 7 ⟨"", (Array.mk [])⟩ w s _ mem1 after st1 h_res
          rfl h_asz h_amut h_rd h_cp)
    refine ⟨mem',
      copyRuntimePlace_imm_to_mem_step rp c (.int w s) _ retMemPlace st st1 _
        h_pmd h_wm h_val, ?_⟩
    dsimp only [refReadReturnVal, retMemPlace, retPtr, mem']
    rw [singleton_live_find]
    dsimp only
    rw [h_rd]
    dsimp only
    rw [scalar_tryToScalarInt_fromScalarInt]
    dsimp only
    rw [miriScalar_data, h_trunc]
  | inr h_rest =>
    cases h_rest with
    | inl h_b =>
      let ⟨b, hty, hv⟩ := h_b
      subst hty hv
      have h_vimm : valToMiriImmediate .bool (.bool b) =
          .scalar (.fromScalarInt (miriScalar .i8 (if b then 1 else 0))) := by
        dsimp only [valToMiriImmediate]
        rw [scalar_fromBool_eq]
      rw [h_vimm]
      let ⟨after, h_wm, h_rd, h_cp, h_asz, h_amut, _⟩ :=
        writeMemory_retPlace_scalar .i8 (refLocalLayoutForTy rp.types .bool)
          (.Initialized (value := .Int .I8 false)
            (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 1⟩))
          (if b then 1 else 0) mem1 st rfl rfl rfl trivial h_raw h_mem h_dr
      let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
          Miri.TreeBorrows.BorrowTree Unit :=
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let st1 := { st with machine := { st.machine with memory := mem' } }
      have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
          (refValHooks rp.types) c 8
          ⟨.memory retMemPlace, refLocalLayoutForTy rp.types .bool⟩
          false true st1 = .ok () st1 :=
        validatePlace_mem_scalar_step rp.types c .i8 _ st1 rfl
          (visit_mem_bool_ok rp.types c 7 ⟨"", (Array.mk [])⟩ b mem1 after st1 h_res
            rfl h_asz h_amut h_rd h_cp)
      refine ⟨mem',
        copyRuntimePlace_imm_to_mem_step rp c .bool _ retMemPlace st st1 _
          h_pmd h_wm h_val, ?_⟩
      dsimp only [refReadReturnVal, retMemPlace, retPtr, mem']
      rw [singleton_live_find]
      dsimp only
      have h_rd1 : after.readScalar RuntimeTargetDataLayout.default.base
          (allocRange Size.ZERO (Size.ofBytes 1)) false =
          .ok (.fromScalarInt (miriScalar .i8 (if b then 1 else 0))) := h_rd
      rw [h_rd1]
      cases b <;> rfl
    | inr h_rest2 =>
      cases h_rest2 with
      | inl h_u =>
        let ⟨hty, hv⟩ := h_u
        subst hty hv
        have h_wm : Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig
            (fun _ => true) .uninit
            ⟨retMemPlace, refLocalLayoutForTy rp.types .unit⟩ st = .ok () st :=
          Miri.Interpreter.PlaceMachine.writeMemory_zero_uninit refAccessConfig
            (fun _ => true) ⟨retMemPlace, refLocalLayoutForTy rp.types .unit⟩
            retPtr (some (tyIdFor rp.types .unit)) (Size.ofBytes 8)
            rfl rfl rfl (fun _ => rfl) st
        have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
            (refValHooks rp.types) c 8
            ⟨.memory retMemPlace, refLocalLayoutForTy rp.types .unit⟩
            false true st = .ok () st :=
          validatePlace_mem_zst_step rp.types c _ st rfl
            (Miri.Interpreter.ValidityVisitor.visit_fieldless
              (refValHooks rp.types) c 7 _ _ st 0
              (by rw [refValHooks_classify]; dsimp only [refLocalLayoutForTy]; rw [h_res])
              (by rw [refValHooks_opsemInhabited]; dsimp only [refLocalLayoutForTy]; rw [h_res])
              rfl rfl rfl rfl)
        have h_st_eq :
            ({ st with machine := { st.machine with memory := st.machine.memory } } :
              Miri.Interpreter.MachineHooks.State Unit RefUser) = st := by
          cases st with | mk stack machine => cases machine; rfl
        refine ⟨st.machine.memory, ?_, rfl⟩
        rw [h_st_eq]
        exact copyRuntimePlace_imm_to_mem_step rp c .unit .uninit retMemPlace
          st st _ h_pmd h_wm h_val
      | inr h_rest3 =>
      cases h_rest3 with
      | inl h_e =>
        let ⟨ety, variant, hty, hv, h_adm, h_v_lt⟩ := h_e
        subst hty hv
        cases h_tr : ety.tagRepr with
        | zeroSized =>
          have h_zst : isZstEnumTy ety = true := by
            dsimp only [isZstEnumTy]
            rw [h_adm, h_tr]
          have h_len1 : ety.discriminants.length = 1 := by
            let ⟨_, _, h_tag⟩ := enumAdmitted_parts h_adm
            rw [h_tr] at h_tag
            dsimp only at h_tag
            exact Nat.eq_of_beq_eq_true h_tag
          have h_v0 : variant = 0 := by
            rw [h_len1] at h_v_lt
            cases variant with
            | zero => rfl
            | succ n => exact False.elim (Nat.not_lt_zero n (Nat.lt_of_succ_lt_succ h_v_lt))
          subst h_v0
          have h_vimm : valToMiriImmediate (.enum ety) (.enumVal ety 0) = .uninit := by
            dsimp only [valToMiriImmediate]; rw [h_tr]
          rw [h_vimm]
          have h_lml :
              localMemoryLayout (refLocalLayoutForTy rp.types (.enum ety)) =
                ⟨Size.ZERO, Align.ONE, .Memory (sized := true),
                  some (tyIdFor rp.types (.enum ety))⟩ := by
            dsimp only [localMemoryLayout, refLocalLayoutForTy, refLayoutDataForTy,
              refEnumLayoutData]
            rw [h_tr]; rfl
          have h_wm : Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig
              (fun _ => true) .uninit
              ⟨retMemPlace, refLocalLayoutForTy rp.types (.enum ety)⟩ st =
              .ok () st :=
            Miri.Interpreter.PlaceMachine.writeMemory_zero_uninit refAccessConfig
              (fun _ => true) ⟨retMemPlace, refLocalLayoutForTy rp.types (.enum ety)⟩
              retPtr (some (tyIdFor rp.types (.enum ety))) (Size.ofBytes 8)
              h_lml rfl rfl (fun _ => rfl) st
          have h_sz0 : (refLocalLayoutForTy rp.types (.enum ety)).layout.size =
              Size.ZERO := by
            dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
            rw [h_tr]; rfl
          have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
              (refValHooks rp.types) c 8
              ⟨.memory retMemPlace, refLocalLayoutForTy rp.types (.enum ety)⟩
              false true st = .ok () st :=
            validatePlace_mem_zst_step rp.types c _ st h_sz0
              (visit_local_fieldless_enum rp.types c 7 _ _ (.enum ety) ety 0
                st rfl
                (Or.inl ⟨rfl, h_res⟩)
                (by dsimp only [refLocalLayoutForTy, refLayoutDataForTy,
                      refEnumLayoutData]; rw [h_tr]; rfl)
                (by dsimp only [refLocalLayoutForTy, refLayoutDataForTy,
                      refEnumLayoutData]; rw [h_tr]; rfl)
                rfl)
          have h_st_eq :
              ({ st with machine := { st.machine with memory := st.machine.memory } } :
                Miri.Interpreter.MachineHooks.State Unit RefUser) = st := by
            cases st with | mk stack machine => cases machine; rfl
          refine ⟨st.machine.memory, ?_, ?_⟩
          · rw [h_st_eq]
            exact copyRuntimePlace_imm_to_mem_step rp c (.enum ety) .uninit
              retMemPlace st st _ h_pmd h_wm h_val
          · dsimp only [refReadReturnVal]
            rw [h_tr, refIsZstEnumTy_eq, h_zst]
            rfl
        | scalar tagW tagS =>
          let ⟨disc, h_get_d⟩ := mirGetElem?_some_of_lt h_v_lt
          have h_vimm : valToMiriImmediate (.enum ety) (.enumVal ety variant) =
              .scalar (.fromScalarInt (miriScalar tagW (BitVec.ofNat 128 disc))) := by
            dsimp only [valToMiriImmediate]
            rw [h_tr, h_get_d]
          rw [h_vimm]
          have h_lsz : (refLocalLayoutForTy rp.types (.enum ety)).layout.size =
              toMiriSize tagW := by
            dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
            rw [h_tr]; rfl
          rw [h_lsz] at h_raw h_mem
          let ⟨after, h_wm, h_rd, h_cp, h_asz, h_amut, _⟩ :=
            writeMemory_retPlace_scalar tagW (refLocalLayoutForTy rp.types (.enum ety))
              (.Union (value := .Int (toMiriInteger tagW) tagS))
              (BitVec.ofNat 128 disc) mem1 st
              (by dsimp only [localMemoryLayout, refLocalLayoutForTy,
                    refLayoutDataForTy, refEnumLayoutData]; rw [h_tr]; rfl)
              h_lsz
              (by cases tagW <;> cases tagS <;> rfl)
              trivial h_raw h_mem h_dr
          let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
              Miri.TreeBorrows.BorrowTree Unit :=
            { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
          let st1 := { st with machine := { st.machine with memory := mem' } }
          have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
              (refValHooks rp.types) c 8
              ⟨.memory retMemPlace, refLocalLayoutForTy rp.types (.enum ety)⟩
              false true st1 = .ok () st1 :=
            validatePlace_mem_scalar_step rp.types c tagW _ st1 h_lsz
              (visit_mem_scalar_enum_ok rp.types c 7 6 rfl (.enum ety) ety
                tagW tagS variant disc mem1 after st1 h_tr h_adm
                (Or.inl ⟨rfl, h_res⟩) h_get_d
                h_pmd rfl
                h_asz h_amut h_rd h_cp)
          refine ⟨mem',
            copyRuntimePlace_imm_to_mem_step rp c (.enum ety) _ retMemPlace
              st st1 _ h_pmd h_wm h_val, ?_⟩
          have h_ref_adm : refEnumAdmitted ety = true := by
            rw [refEnumAdmitted_eq]; exact h_adm
          let ⟨_, _, h_tag_all⟩ := enumAdmitted_parts h_adm
          rw [h_tr] at h_tag_all
          have h_tag_ok : tagBitsToDiscrBits tagW tagS ety.discrWidth
              (truncateBits tagW (BitVec.ofNat 128 disc)) = BitVec.ofNat 128 disc :=
            eq_of_beq (list_all_mirGetElem?
              (p := fun d =>
                tagBitsToDiscrBits tagW tagS ety.discrWidth
                  (truncateBits tagW (BitVec.ofNat 128 d)) == BitVec.ofNat 128 d)
              h_tag_all h_get_d)
          dsimp only [refReadReturnVal, retMemPlace, retPtr, mem']
          rw [h_tr]
          dsimp only
          rw [h_ref_adm, mem_ite_not_true_eq, singleton_live_find]
          dsimp only
          rw [h_rd]
          dsimp only
          rw [scalar_tryToScalarInt_fromScalarInt]
          dsimp only
          rw [miriScalar_data, refMiriTagToDiscrBits_eq, h_tag_ok]
          dsimp only
          rw [refFindDiscrVariant?_eq,
            findDiscrVariant?_of_enumAdmitted h_adm h_get_d]
      | inr h_rest4 =>
      cases h_rest4 with
      | inl h_c =>
        let ⟨ch, hty, hv⟩ := h_c
        subst hty hv
        have h_vimm : valToMiriImmediate .char (.char ch) =
            .scalar (.fromScalarInt
              (miriScalar .i32 (BitVec.ofNat 128 ch.toNat))) := by
          dsimp only [valToMiriImmediate, Scalar.fromChar]
          rw [scalarInt_ofChar_eq_miriScalar]
        rw [h_vimm]
        have h_lsz : (refLocalLayoutForTy rp.types .char).layout.size =
            toMiriSize .i32 := rfl
        rw [h_lsz] at h_raw h_mem
        let ⟨after, h_wm, h_rd, h_cp, h_asz, h_amut, _⟩ :=
          writeMemory_retPlace_scalar .i32 (refLocalLayoutForTy rp.types .char)
            (.Initialized (value := .Int .I32 false)
              (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 0x10ffff⟩))
            (BitVec.ofNat 128 ch.toNat) mem1 st rfl h_lsz rfl trivial
            h_raw h_mem h_dr
        let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
            Miri.TreeBorrows.BorrowTree Unit :=
          { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        let st1 := { st with machine := { st.machine with memory := mem' } }
        have h_char : (Scalar.fromScalarInt (Prov := Miri.Memory.Provenance)
            (miriScalar .i32 (BitVec.ofNat 128 ch.toNat))).toChar = .ok ch := by
          rw [← scalarInt_ofChar_eq_miriScalar]
          exact scalar_toChar_fromChar ch
        have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
            (refValHooks rp.types) c 8
            ⟨.memory retMemPlace, refLocalLayoutForTy rp.types .char⟩
            false true st1 = .ok () st1 :=
          validatePlace_mem_scalar_step rp.types c .i32 _ st1 h_lsz
            (visit_mem_char_ok rp.types c 7 ⟨"", (Array.mk [])⟩ ch _ mem1 after
              st1 h_res h_char rfl h_asz h_amut h_rd h_cp)
        refine ⟨mem',
          copyRuntimePlace_imm_to_mem_step rp c .char _ retMemPlace st st1 _
            h_pmd h_wm h_val, ?_⟩
        dsimp only [refReadReturnVal, retMemPlace, retPtr, mem']
        rw [singleton_live_find]
        dsimp only
        have h_rd4 : after.readScalar RuntimeTargetDataLayout.default.base
            (allocRange Size.ZERO (Size.ofBytes 4)) false =
            .ok (.fromScalarInt
              (miriScalar .i32 (BitVec.ofNat 128 ch.toNat))) :=
          h_rd
        rw [h_rd4]
        dsimp only
        rw [scalar_tryToScalarInt_fromScalarInt]
        dsimp only
        rw [← scalarInt_ofChar_eq_miriScalar, scalarInt_toChar_ofChar]
      | inr h_rest5 =>
      cases h_rest5 with
      | inl h_o =>
        let ⟨o, hty, hv⟩ := h_o
        subst hty hv
        let ⟨variant, h_get_d⟩ := ordering_variant o
        rw [mem_valToMiriImmediate_ordering]
        have h_lsz : (refLocalLayoutForTy rp.types .ordering).layout.size =
            toMiriSize .i8 := rfl
        rw [h_lsz] at h_raw h_mem
        let ⟨after, h_wm, h_rd, h_cp, h_asz, h_amut, _⟩ :=
          writeMemory_retPlace_scalar .i8
            (refLocalLayoutForTy rp.types .ordering)
            (.Union (value := .Int (toMiriInteger .i8) true))
            (BitVec.ofNat 128 (orderingTagBits o)) mem1 st rfl h_lsz rfl trivial
            h_raw h_mem h_dr
        let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
            Miri.TreeBorrows.BorrowTree Unit :=
          { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
        let st1 := { st with machine := { st.machine with memory := mem' } }
        have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
            (refValHooks rp.types) c 8
            ⟨.memory retMemPlace, refLocalLayoutForTy rp.types .ordering⟩
            false true st1 = .ok () st1 :=
          validatePlace_mem_scalar_step rp.types c .i8 _ st1 h_lsz
            (visit_mem_scalar_enum_ok rp.types c 7 6 rfl .ordering
              refOrderingEnumTy .i8 true variant (orderingTagBits o) mem1 after
              st1 rfl mem_refOrderingEnumTy_admitted (Or.inr ⟨rfl, rfl, h_res⟩)
              h_get_d h_pmd rfl h_asz h_amut h_rd h_cp)
        refine ⟨mem',
          copyRuntimePlace_imm_to_mem_step rp c .ordering _ retMemPlace st st1 _
            h_pmd h_wm h_val, ?_⟩
        dsimp only [refReadReturnVal, retMemPlace, retPtr, mem']
        rw [singleton_live_find]
        dsimp only
        have h_rd1 : after.readScalar RuntimeTargetDataLayout.default.base
            (allocRange Size.ZERO (Size.ofBytes 1)) false =
            .ok (.fromScalarInt
              (miriScalar .i8 (BitVec.ofNat 128 (orderingTagBits o)))) :=
          h_rd
        rw [h_rd1]
        dsimp only
        rw [scalar_tryToScalarInt_fromScalarInt]
        dsimp only
        rw [miriScalar_data]
        cases o <;> rfl
      | inr h_p =>
        let ⟨w, s, bits, b, hty, hv, h_trunc⟩ := h_p
        subst hty hv
        exact copyReturn_pair_ok rp c w s bits b mem1 st h_raw h_mem h_dr h_pmd
          h_trunc h_res

/-- Executing `ExecutionControl.hooks.copyReturn` on an uninitialized non-ZST
return local `_0` fails with `.undefinedBehavior`. -/
theorem copyReturn_uninit_ub (rp : RefProg) (c : Choice) (retTy : MirTy)
    (mem : Miri.Memory.MemoryState Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (retPlace : MPlaceTy Miri.Memory.Provenance)
    (st : Miri.Interpreter.MachineHooks.State Unit RefUser)
    (h_init : refInitMemoryAndRetPlace rp.types retTy = .ok (mem, retPlace))
    (h_mem : st.machine.memory = mem)
    (h_dr : st.machine.dataRace = none)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_sm : SlotMatchesTy retTy (.immediate none))
    (h_supp : isSupportedScalarOrUnitTy retTy = true)
    (h_res : resolveTy rp.types (tyIdFor rp.types retTy) = some retTy) :
    let h := Miri.Interpreter.ExecutionMachine.withValidation
      (refExecutionConfig rp) refLimits
    ∃ msg st',
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate .uninit, refLocalLayoutForTy rp.types retTy⟩
          ⟨.memory retPlace.mplace, retPlace.layout⟩ true st =
        .error (.undefinedBehavior msg) st' := by
  let ⟨mem1, rawAlloc, h_raw, _, _, _, _, _, _, h_mem_shape, h_rp_shape⟩ :=
    refInitMemoryAndRetPlace_shape rp.types retTy h_init
  rw [h_mem_shape] at h_mem
  rw [h_rp_shape]
  change let h := Miri.Interpreter.ExecutionMachine.withValidation (refExecutionConfig rp) refLimits
    ∃ msg st',
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks h).place h.copy c
          ⟨.immediate .uninit, refLocalLayoutForTy rp.types retTy⟩
          ⟨.memory retMemPlace, refLocalLayoutForTy rp.types retTy⟩ true st =
        .error (.undefinedBehavior msg) st'
  let initSess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance := {
    path := ⟨"", (Array.mk [])⟩, flags := ⟨true, false⟩, ctfeMode := none,
    refTracking := none, dataBytes := some .empty
  }
  cases retTy with
  | unit => exact False.elim (h_sm.1 rfl)
  | never =>
    have h_wm : Miri.Interpreter.PlaceMachine.writeMemory refAccessConfig
        (fun _ => true) .uninit
        ⟨retMemPlace, refLocalLayoutForTy rp.types .never⟩ st = .ok () st :=
      Miri.Interpreter.PlaceMachine.writeMemory_zero_uninit refAccessConfig
        (fun _ => true) ⟨retMemPlace, refLocalLayoutForTy rp.types .never⟩
        retPtr (some (tyIdFor rp.types .never)) (Size.ofBytes 8)
        rfl rfl rfl (fun _ => rfl) st
    let ⟨msg, h_vis⟩ := visit_local_never_ub rp.types c 7 initSess
      ⟨.memory retMemPlace, refLocalLayoutForTy rp.types .never⟩ st rfl h_res
    exact ⟨msg, st, copyRuntimePlace_imm_to_mem_step rp c .never .uninit
      retMemPlace st st _ h_pmd h_wm
      (validatePlace_mem_ub_step rp.types c _ st st msg h_vis)⟩
  | bool =>
    let ⟨after, info, h_wm, h_rd, h_asz, _, _⟩ :=
      writeMemory_retPlace_uninit .i8 (refLocalLayoutForTy rp.types .bool)
        mem1 st rfl rfl h_raw h_mem h_dr
    let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit :=
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let st1 := { st with machine := { st.machine with memory := mem' } }
    let ⟨msg, h_vis⟩ := visit_mem_bool_uninit_ub rp.types c 7 initSess info
      mem1 after st1 h_res rfl h_asz h_rd
    exact ⟨msg, st1, copyRuntimePlace_imm_to_mem_step rp c .bool .uninit
      retMemPlace st st1 _ h_pmd h_wm
      (validatePlace_mem_ub_step rp.types c _ st1 st1 msg h_vis)⟩
  | int w s =>
    let ⟨after, info, h_wm, h_rd, h_asz, _, _⟩ :=
      writeMemory_retPlace_uninit w (refLocalLayoutForTy rp.types (.int w s))
        mem1 st (by cases w <;> cases s <;> rfl) rfl h_raw h_mem h_dr
    let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit :=
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let st1 := { st with machine := { st.machine with memory := mem' } }
    let ⟨msg, h_vis⟩ := visit_mem_int_uninit_ub rp.types c 7 initSess w s info
      mem1 after st1 h_res rfl h_asz h_rd
    exact ⟨msg, st1, copyRuntimePlace_imm_to_mem_step rp c (.int w s) .uninit
      retMemPlace st st1 _ h_pmd h_wm
      (validatePlace_mem_ub_step rp.types c _ st1 st1 msg h_vis)⟩
  | enum ety =>
    cases h_tr : ety.tagRepr with
    | zeroSized =>
      have h_zst := h_sm.2 ety rfl
      dsimp only [isZstEnumTy] at h_zst
      rw [h_tr] at h_zst
      dsimp only [isSupportedScalarOrUnitTy] at h_supp
      rw [h_supp] at h_zst
      cases h_zst
    | scalar tagW tagS =>
      have h_lsz : (refLocalLayoutForTy rp.types (.enum ety)).layout.size =
          toMiriSize tagW := by
        dsimp only [refLocalLayoutForTy, refLayoutDataForTy, refEnumLayoutData]
        rw [h_tr]; rfl
      have h_uns :
          (localMemoryLayout (refLocalLayoutForTy rp.types (.enum ety))).backendRepr.isUnsized =
            false := by
        dsimp only [localMemoryLayout, refLocalLayoutForTy, refLayoutDataForTy,
          refEnumLayoutData]
        rw [h_tr]; rfl
      rw [h_lsz] at h_raw h_mem
      let ⟨after, info, h_wm, h_rd, h_asz, _, _⟩ :=
        writeMemory_retPlace_uninit tagW (refLocalLayoutForTy rp.types (.enum ety))
          mem1 st h_uns h_lsz h_raw h_mem h_dr
      let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
          Miri.TreeBorrows.BorrowTree Unit :=
        { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
      let st1 := { st with machine := { st.machine with memory := mem' } }
      let ⟨msg, h_vis⟩ := visit_mem_scalar_enum_uninit_ub rp.types c 7 6 rfl
        (.enum ety) ety tagW tagS info mem1 after st1 h_tr (Or.inl ⟨rfl, h_res⟩)
        rfl h_asz h_rd
      exact ⟨msg, st1, copyRuntimePlace_imm_to_mem_step rp c (.enum ety) .uninit
        retMemPlace st st1 _ h_pmd h_wm
        (validatePlace_mem_ub_step rp.types c _ st1 st1 msg h_vis)⟩
  | char =>
    have h_lsz : (refLocalLayoutForTy rp.types .char).layout.size =
        toMiriSize .i32 := rfl
    rw [h_lsz] at h_raw h_mem
    let ⟨after, info, h_wm, h_rd, h_asz, _, _⟩ :=
      writeMemory_retPlace_uninit .i32 (refLocalLayoutForTy rp.types .char)
        mem1 st rfl h_lsz h_raw h_mem h_dr
    let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit :=
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let st1 := { st with machine := { st.machine with memory := mem' } }
    let ⟨msg, h_vis⟩ := visit_mem_char_uninit_ub rp.types c 7 initSess info
      mem1 after st1 h_res rfl h_asz h_rd
    exact ⟨msg, st1, copyRuntimePlace_imm_to_mem_step rp c .char .uninit
      retMemPlace st st1 _ h_pmd h_wm
      (validatePlace_mem_ub_step rp.types c _ st1 st1 msg h_vis)⟩
  | ordering =>
    have h_lsz : (refLocalLayoutForTy rp.types .ordering).layout.size =
        toMiriSize .i8 := rfl
    rw [h_lsz] at h_raw h_mem
    let ⟨after, info, h_wm, h_rd, h_asz, _, _⟩ :=
      writeMemory_retPlace_uninit .i8 (refLocalLayoutForTy rp.types .ordering)
        mem1 st rfl h_lsz h_raw h_mem h_dr
    let mem' : Miri.Memory.MemoryState Miri.Memory.Provenance
        Miri.TreeBorrows.BorrowTree Unit :=
      { mem1 with live := (Array.mk [(retAllocId, ⟨.stack, after⟩)]) }
    let st1 := { st with machine := { st.machine with memory := mem' } }
    let ⟨msg, h_vis⟩ := visit_mem_scalar_enum_uninit_ub rp.types c 7 6 rfl
      .ordering refOrderingEnumTy .i8 true info mem1 after st1 rfl
      (Or.inr ⟨rfl, rfl, h_res⟩) rfl h_asz h_rd
    exact ⟨msg, st1, copyRuntimePlace_imm_to_mem_step rp c .ordering .uninit
      retMemPlace st st1 _ h_pmd h_wm
      (validatePlace_mem_ub_step rp.types c _ st1 st1 msg h_vis)⟩
  | tuple fs =>
    let ⟨w, s, h_fs⟩ := isOverflowPairTy_inv h_supp
    subst h_fs
    exact copyReturn_pair_uninit_ub rp c w s mem1 st h_raw h_mem h_dr h_pmd
      h_res
  | ref _ _ | rawPtr _ _ | unsupported => cases h_supp

end Anneal.MirCorrespondence
