-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.List.TakeDrop
import Init.Data.Nat.Basic
import Init.Omega
import VendorX86GccRef
import ByteX86Gcc
import ByteX86GccDecodeBase

/-!
# `ByteX86GccDecodePass2`

Exact 16-byte fetch-window decoder commutation (`parseExactBody_eq` and
`decodeRef_commutes_of_len16`, `0` `sorry`, `0` `isPartial`) built on
`ByteX86GccDecodeBase`.
-/

namespace ByteX86GccPass2

theorem parseExactBody_eq (ps : VendorX86GccRef.PrefixState) (slice : List (BitVec 8)) :
    ByteX86Gcc.parseExactBody (mapPrefixState ps) slice =
      mapExcept (VendorX86GccRef.parseExactBody ps slice) := by
  cases slice with
  | nil => rfl
  | cons op0 rest0 =>
    by_cases hc5 : op0 == 0xC5#8
    · unfold ByteX86Gcc.parseExactBody VendorX86GccRef.parseExactBody
      dsimp only [mapPrefixState]
      simp only [hc5, ite_true, repNeNone_eq]
      split
      · rfl
      · cases rest0 with
        | nil => rfl
        | cons b1 r1 =>
          cases r1 with
          | nil => rfl
          | cons opc afterOpc => exact parseSimdOpc_eq _ _ _ _ _ _ _ _ _ _ _
    · by_cases hc4 : op0 == 0xC4#8
      · unfold ByteX86Gcc.parseExactBody VendorX86GccRef.parseExactBody
        dsimp only [mapPrefixState]
        simp only [hc5, Bool.false_eq_true, ite_false, hc4, ite_true, repNeNone_eq]
        split
        · rfl
        · cases rest0 with
          | nil => rfl
          | cons b1 r1 =>
            cases r1 with
            | nil => rfl
            | cons b2 r2 =>
              cases r2 with
              | nil => rfl
              | cons opc afterOpc => exact parseSimdOpc_eq _ _ _ _ _ _ _ _ _ _ _
      · by_cases hlock : ps.hasLock = true
        · unfold ByteX86Gcc.parseExactBody VendorX86GccRef.parseExactBody
          dsimp only [mapPrefixState]
          simp only [hc5, hc4, Bool.false_eq_true, ite_false, hlock, ite_true]
          rfl
        · have hlockf := Bool.eq_false_iff.mpr hlock
          by_cases h0f : op0 == 0x0F#8
          · have h0feq : op0 = 0x0F#8 := eq_of_beq h0f
            subst h0feq
            exact parseExactBody_0f_eq ps rest0 hlockf
          · have h0ff : (op0 == 0x0F#8) = false := Bool.eq_false_iff.mpr h0f
            unfold ByteX86Gcc.parseExactBody VendorX86GccRef.parseExactBody
            have hsz := opSizeOf_eq ps
            dsimp only
            rw [hsz]
            dsimp only [mapPrefixState]
            simp only [rexR_eq, rexX_eq, rexB_eq, rexW_eq,
                       hc5, hc4, hlockf, h0ff, Bool.false_eq_true, ite_false]
            rw [readLe32?_eq, readLe64?_eq, readLe16?_eq, parseModRm_eq]
            by_cases he9 : op0 == 0xE9#8
            · have he9eq : op0 = 0xE9#8 := eq_of_beq he9
              subst he9eq
              cases VendorX86GccRef.readLe32? rest0 with
              | none => rfl
              | some p => cases p; rfl
            · have he9f : (op0 == 0xE9#8) = false := Bool.eq_false_iff.mpr he9
              simp only [he9f, Bool.false_eq_true, ite_false]
              by_cases hb8 : (decide (op0.toNat ≥ 0xB8) && decide (op0.toNat ≤ 0xBF)) = true
              · have hb8' : op0.toNat ≥ 0xB8 ∧ op0.toNat ≤ 0xBF := by
                  simpa [Bool.and_eq_true, decide_eq_true_eq] using hb8
                have hneByte : ∀ (k : BitVec 8), k.toNat < 0xB8 ∨ k.toNat > 0xBF → (op0 == k) = false := by
                  intro k hk
                  cases h : op0 == k
                  · rfl
                  · have heq := eq_of_beq h; subst heq; omega
                have hn90 : (op0 == 0x90#8) = false := hneByte 0x90#8 (by decide)
                have hnc3 : (op0 == 0xC3#8) = false := hneByte 0xC3#8 (by decide)
                have hnc9 : (op0 == 0xC9#8) = false := hneByte 0xC9#8 (by decide)
                have hnfa : (op0 == 0xFA#8) = false := hneByte 0xFA#8 (by decide)
                have hn50 : (decide (op0.toNat ≥ 0x50) && decide (op0.toNat ≤ 0x57)) = false := by
                  cases h : decide (op0.toNat ≥ 0x50) && decide (op0.toNat ≤ 0x57)
                  · rfl
                  · simp [Bool.and_eq_true, decide_eq_true_eq] at h; omega
                have hn58 : (decide (op0.toNat ≥ 0x58) && decide (op0.toNat ≤ 0x5F)) = false := by
                  cases h : decide (op0.toNat ≥ 0x58) && decide (op0.toNat ≤ 0x5F)
                  · rfl
                  · simp [Bool.and_eq_true, decide_eq_true_eq] at h; omega
                have hneb : (op0 == 0xEB#8) = false := hneByte 0xEB#8 (by decide)
                have hn70 : (decide (op0.toNat ≥ 0x70) && decide (op0.toNat ≤ 0x7F)) = false := by
                  cases h : decide (op0.toNat ≥ 0x70) && decide (op0.toNat ≤ 0x7F)
                  · rfl
                  · simp [Bool.and_eq_true, decide_eq_true_eq] at h; omega
                have hna8 : (op0 == 0xA8#8) = false := hneByte 0xA8#8 (by decide)
                have hnb0 : (decide (op0.toNat ≥ 0xB0) && decide (op0.toNat ≤ 0xB7)) = false := by
                  cases h : decide (op0.toNat ≥ 0xB0) && decide (op0.toNat ≤ 0xB7)
                  · rfl
                  · simp [Bool.and_eq_true, decide_eq_true_eq] at h; omega
                simp only [hn90, hnc3, hnc9, hnfa, hn50, hn58, hneb, hn70, hna8, hnb0,
                           Bool.false_eq_true, ite_false, hb8, ite_true]
                cases VendorX86GccRef.rexW ps.rex with
                | true =>
                  simp only [ite_true]
                  cases VendorX86GccRef.readLe64? rest0 with
                  | none => rfl
                  | some p => cases p; dsimp only [mapExcept, mapInstr]; rw [mapGpr_gprOfNat]; rfl
                | false =>
                  cases ps.has66 with
                  | true =>
                    simp only [Bool.false_eq_true, ite_false, ite_true]
                    cases VendorX86GccRef.readLe16? rest0 with
                    | none => rfl
                    | some p => cases p; dsimp only [mapExcept, mapInstr]; rw [mapGpr_gprOfNat]; rfl
                  | false =>
                    simp only [Bool.false_eq_true, ite_false]
                    cases VendorX86GccRef.readLe32? rest0 with
                    | none => rfl
                    | some p => cases p; dsimp only [mapExcept, mapInstr]; rw [mapGpr_gprOfNat]; rfl
              · have hb8f : (decide (op0.toNat ≥ 0xB8) && decide (op0.toNat ≤ 0xBF)) = false :=
                  Bool.eq_false_iff.mpr hb8
                simp only [hb8f, Bool.false_eq_true, ite_false]
                cases rest0 with
                | nil =>
                  dsimp only [Option.map, VendorX86GccRef.parseModRm]
                  (repeat rw [mapExcept_if])
                  dsimp only [mapExcept, mapInstr, mapFaultKind]
                  (try simp only [mapGpr_gprOfNat])
                  (try rfl)
                | cons d0 tail0 =>
                  cases VendorX86GccRef.parseModRm (VendorX86GccRef.rexR ps.rex) (VendorX86GccRef.rexX ps.rex) (VendorX86GccRef.rexB ps.rex) (d0 :: tail0) with
                  | none =>
                    dsimp only [Option.map]
                    (repeat rw [mapExcept_if])
                    dsimp only [mapExcept, mapInstr, mapFaultKind, mapRm8, mapRm]
                    (try simp only [mapGpr_gprOfNat])
                    (try simp only [mapReg8_reg8OfIdx])
                    (try simp only [condOfNib_eq])
                    (try rfl)
                  | some q =>
                    rcases q with ⟨rIdx, rm, mrm, tl⟩
                    dsimp only [Option.map]
                    rw [rmToRm8_eq,
                        aluOpOfIdx_eq (BitVec.extractLsb' 3 3 mrm).toNat,
                        shiftOpOfIdx_eq (BitVec.extractLsb' 3 3 mrm).toNat,
                        aluOpOfIdx_eq (op0.toNat / 8),
                        readLe16?_eq tl, readLe32?_eq tl]
                    simp only [opSizeEqS16_eq, ite_self, ← mapGpr_gprOfNat, ← mapReg8_reg8OfIdx, condOfNib_eq]
                    -- Push `mapExcept` across the outer 35-branch `if` chain ONCE before case-splitting!
                    (repeat rw [mapExcept_if])
                    by_cases h80 : op0 == 0x80#8
                    · have h := eq_of_beq h80; subst h
                      cases VendorX86GccRef.aluOpOfIdx (BitVec.extractLsb' 3 3 mrm).toNat <;> cases tl <;>
                        ((try dsimp only [Option.map, mapExcept, mapInstr, mapFaultKind]); rfl)
                    · by_cases h83 : op0 == 0x83#8
                      · have h := eq_of_beq h83; subst h
                        cases VendorX86GccRef.aluOpOfIdx (BitVec.extractLsb' 3 3 mrm).toNat <;> cases tl <;>
                          ((try dsimp only [Option.map, mapExcept, mapInstr, mapFaultKind]); rfl)
                      · by_cases h81 : op0 == 0x81#8
                        · have h := eq_of_beq h81; subst h
                          cases VendorX86GccRef.aluOpOfIdx (BitVec.extractLsb' 3 3 mrm).toNat <;>
                            rcases tl with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, tl4⟩⟩⟩⟩ <;>
                            ((try dsimp only [Option.map, VendorX86GccRef.readLe16?, VendorX86GccRef.readLe32?]);
                             (repeat rw [mapExcept_if]);
                             (try dsimp only [mapExcept, mapInstr, mapFaultKind]); rfl)
                        · by_cases hc0 : op0 == 0xC0#8
                          · have h := eq_of_beq hc0; subst h
                            cases VendorX86GccRef.shiftOpOfIdx (BitVec.extractLsb' 3 3 mrm).toNat <;> cases tl <;>
                              ((try dsimp only [Option.map, mapExcept, mapInstr, mapFaultKind]); rfl)
                          · by_cases hc1 : op0 == 0xC1#8
                            · have h := eq_of_beq hc1; subst h
                              cases VendorX86GccRef.shiftOpOfIdx (BitVec.extractLsb' 3 3 mrm).toNat <;> cases tl <;>
                                ((try dsimp only [Option.map]); (repeat rw [mapExcept_if]);
                                 (try dsimp only [mapExcept, mapInstr, mapFaultKind]); rfl)
                            · by_cases hd1 : op0 == 0xD1#8
                              · have h := eq_of_beq hd1; subst h
                                cases VendorX86GccRef.shiftOpOfIdx (BitVec.extractLsb' 3 3 mrm).toNat <;>
                                  ((try dsimp only [Option.map, mapExcept, mapInstr, mapFaultKind]); rfl)
                              · by_cases hc6 : op0 == 0xC6#8
                                · have h := eq_of_beq hc6; subst h
                                  cases tl <;> ((repeat rw [mapExcept_if]); (try dsimp only [mapExcept, mapInstr, mapFaultKind]); rfl)
                                · by_cases hc7 : op0 == 0xC7#8
                                  · have h := eq_of_beq hc7; subst h
                                    rcases tl with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, tl4⟩⟩⟩⟩ <;>
                                      ((try dsimp only [VendorX86GccRef.readLe16?, VendorX86GccRef.readLe32?]);
                                       (repeat rw [mapExcept_if]);
                                       (try dsimp only [mapExcept, mapInstr, mapFaultKind]); rfl)
                                  · by_cases h8d : op0 == 0x8D#8
                                    · have h := eq_of_beq h8d; subst h
                                      cases rm <;> rfl
                                    · by_cases hf6 : op0 == 0xF6#8
                                      · have h := eq_of_beq hf6; subst h
                                        cases tl <;> ((repeat rw [mapExcept_if]); (try dsimp only [mapExcept, mapInstr, mapFaultKind]); rfl)
                                      · by_cases h6b : op0 == 0x6B#8
                                        · have h := eq_of_beq h6b; subst h
                                          cases tl <;> rfl
                                        · by_cases h69 : op0 == 0x69#8
                                          · have h := eq_of_beq h69; subst h
                                            rcases tl with _ | ⟨t0, _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, tl4⟩⟩⟩⟩ <;>
                                              ((try dsimp only [VendorX86GccRef.readLe16?, VendorX86GccRef.readLe32?]);
                                               (repeat rw [mapExcept_if]);
                                               (try dsimp only [mapExcept, mapInstr, mapFaultKind]); rfl)
                                          · simp only [Bool.eq_false_iff.mpr h80, Bool.eq_false_iff.mpr h83,
                                                       Bool.eq_false_iff.mpr h81, Bool.eq_false_iff.mpr hc0,
                                                       Bool.eq_false_iff.mpr hc1, Bool.eq_false_iff.mpr hd1,
                                                       Bool.eq_false_iff.mpr hc6, Bool.eq_false_iff.mpr hc7,
                                                       Bool.eq_false_iff.mpr h8d, Bool.eq_false_iff.mpr hf6,
                                                       Bool.eq_false_iff.mpr h6b, Bool.eq_false_iff.mpr h69,
                                                       Bool.false_eq_true, Bool.false_and, Bool.false_or, ite_false]
                                            cases VendorX86GccRef.aluOpOfIdx (op0.toNat / 8) <;>
                                              ((try dsimp only [Option.map]);
                                               (repeat rw [mapExcept_if]);
                                               (try dsimp only [mapExcept, mapInstr, mapFaultKind, mapRm8, mapRm]);
                                               rfl)

theorem scanPrefixes_ref_count_inv (fuel : Nat) :
    ∀ (st : VendorX86GccRef.PrefixState) (bs : List (BitVec 8)),
      let (ps, rem) := VendorX86GccRef.scanPrefixes fuel st bs
      ps.count + rem.length = st.count + bs.length := by
  intro st bs
  have hcomm := scanPrefixes_commutes fuel st bs
  have hinv := ByteX86Gcc.scanPrefixes_count_inv fuel (mapPrefixState st) bs
  rw [hcomm] at hinv
  cases h : VendorX86GccRef.scanPrefixes fuel st bs with
  | mk ps rem =>
    rw [h] at hinv
    dsimp [mapPrefixState] at hinv ⊢
    exact hinv

/-- **Exact 16-Byte Fetch-Window Decoder Agreement (`decodeRef_commutes_of_len16`):**
    On every 16-byte instruction fetch window `w16` (`w16.length = 16`), `ByteX86Gcc.decodeX64`
    and `VendorX86GccRef.decodeRef` produce the exact same instruction AST, byte length,
    and fault classification. -/
theorem decodeRef_commutes_of_len16 (w16 : List (BitVec 8)) (hw : w16.length = 16) :
    ByteX86Gcc.decodeX64 w16 = mapOutcome (VendorX86GccRef.decodeRef w16) := by
  unfold ByteX86Gcc.decodeX64 VendorX86GccRef.decodeRef
  have hcomm := scanPrefixes_commutes 16 {} w16
  have hinv  := scanPrefixes_ref_count_inv 16 {} w16
  have hinit : mapPrefixState {} = ({} : ByteX86Gcc.PrefixState) := rfl
  rw [hinit] at hcomm
  rw [hcomm]
  cases hscan : VendorX86GccRef.scanPrefixes 16 {} w16 with
  | mk ps body =>
    rw [hscan] at hinv
    dsimp only at hinv ⊢
    have hcnt : (mapPrefixState ps).count = ps.count := rfl
    rw [hcnt]
    by_cases hc15 : (ps.count >= 15 && body.isEmpty) = true
    · simp only [hc15, ite_true]; rfl
    · have hc15f := Bool.eq_false_iff.mpr hc15
      simp only [hc15f, Bool.false_eq_true, ite_false]
      by_cases hc14 : ps.count > 14
      · rw [ByteX86Gcc.ifTrue hc14, ByteX86Gcc.ifTrue hc14]; rfl
      · rw [ByteX86Gcc.ifFalse hc14, ByteX86Gcc.ifFalse hc14]
        have hne : body.isEmpty = false := by
          cases body with
          | nil => simp [hw] at hinv; omega
          | cons _ _ => rfl
        simp only [hne, Bool.false_eq_true, ite_false]
        rw [ildBodyLen_eq ps body]
        cases VendorX86GccRef.ildBodyLen ps body with
        | none => rfl
        | some bLen =>
          dsimp only
          by_cases hgt15 : ps.count + bLen > 15
          · rw [ByteX86Gcc.ifTrue hgt15, ByteX86Gcc.ifTrue hgt15]; rfl
          · rw [ByteX86Gcc.ifFalse hgt15, ByteX86Gcc.ifFalse hgt15]
            have hnotTrunc : ¬ ((body.take bLen).length < bLen) := by
              rw [List.length_take]; simp [hw] at hinv; omega
            rw [ByteX86Gcc.ifFalse hnotTrunc]
            rw [parseExactBody_eq ps (body.take bLen)]
            cases VendorX86GccRef.parseExactBody ps (body.take bLen) <;> rfl


end ByteX86GccPass2