/-!
Standalone Lean 4.34.1 verification probe for the unified `MiniMach` backend IR.
All theorems rely solely on kernel-checked constructive and algebraic proofs:
zero `sorry`, zero `bv_decide`, zero `native_decide`, zero `partial def`,
zero `@[extern]`, and zero `Lean.ofReduceBool`.
-/

namespace MiniMachProbe

/-! ## 1. Eliminating `bv_decide` from Sail-to-RV64 Shift Equivalence -/

def extractShamt6 (shamt : BitVec 6) : BitVec 6 :=
  BitVec.extractLsb 5 0 shamt

theorem extractShamt6_eq_self (shamt : BitVec 6) :
    extractShamt6 shamt = shamt := by
  apply BitVec.eq_of_toNat_eq
  simp [extractShamt6, BitVec.extractLsb_toNat, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt shamt.isLt]

theorem srai_equiv_no_bv_decide (a : BitVec 64) (shamt : BitVec 6) :
    a.sshiftRight' (extractShamt6 shamt) = a.sshiftRight shamt.toNat := by
  rw [extractShamt6_eq_self]
  exact BitVec.sshiftRight_eq' a

/-! ## 2. Sub-Register `LaneView` Framing Algebra -/

inductive LaneView where
  | full64
  | lo32Zext
  | lo16Keep
  | lo8Keep
  | hi8Keep
  deriving DecidableEq, Repr

def maskLo32   : BitVec 64 := 0x0000_0000_FFFF_FFFF#64
def maskLo16   : BitVec 64 := 0x0000_0000_0000_FFFF#64
def maskLo8    : BitVec 64 := 0x0000_0000_0000_00FF#64
def maskHi8    : BitVec 64 := 0x0000_0000_0000_FF00#64
def keepHi16   : BitVec 64 := 0xFFFF_FFFF_FFFF_0000#64
def keepHi8    : BitVec 64 := 0xFFFF_FFFF_FFFF_FF00#64
def keepExHi8  : BitVec 64 := 0xFFFF_FFFF_FFFF_00FF#64

def readLane (lv : LaneView) (r : BitVec 64) : BitVec 64 :=
  match lv with
  | .full64   => r
  | .lo32Zext => r &&& maskLo32
  | .lo16Keep => r &&& maskLo16
  | .lo8Keep  => r &&& maskLo8
  | .hi8Keep  => (r &&& maskHi8) >>> 8

def writeLane (lv : LaneView) (r v : BitVec 64) : BitVec 64 :=
  match lv with
  | .full64   => v
  | .lo32Zext => v &&& maskLo32
  | .lo16Keep => (r &&& keepHi16) ||| (v &&& maskLo16)
  | .lo8Keep  => (r &&& keepHi8) ||| (v &&& maskLo8)
  | .hi8Keep  => (r &&& keepExHi8) ||| ((v &&& maskLo8) <<< 8)

theorem readLane_writeLane_lo32Zext (r v : BitVec 64) :
    readLane .lo32Zext (writeLane .lo32Zext r v) = v &&& maskLo32 := by
  simp only [readLane, writeLane, BitVec.and_assoc]
  have hm : maskLo32 &&& maskLo32 = maskLo32 := rfl
  rw [hm]

theorem writeLane_lo32Zext_clears_upper (r v : BitVec 64) :
    (writeLane .lo32Zext r v) >>> 32 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [writeLane, BitVec.toNat_ushiftRight, BitVec.toNat_and]
  rw [show maskLo32.toNat = 4294967295 from rfl]
  have hlt : v.toNat &&& 4294967295 < 2 ^ 32 :=
    Nat.and_lt_two_pow v.toNat (by decide : 4294967295 < 2 ^ 32)
  exact Nat.shiftRight_eq_zero (v.toNat &&& 4294967295) 32 hlt

theorem disjoint_lo8_writes_preserve_hi8 (r v : BitVec 64) :
    readLane .hi8Keep (writeLane .lo8Keep r v) = readLane .hi8Keep r := by
  simp only [readLane, writeLane, BitVec.and_or_distrib_right, BitVec.and_assoc]
  have hm1 : keepHi8 &&& maskHi8 = maskHi8 := rfl
  have hm2 : maskLo8 &&& maskHi8 = 0#64 := rfl
  rw [hm1, hm2, BitVec.and_zero, BitVec.or_zero]

theorem disjoint_hi8_writes_preserve_lo8 (r v : BitVec 64) :
    readLane .lo8Keep (writeLane .hi8Keep r v) = readLane .lo8Keep r := by
  simp only [readLane, writeLane, BitVec.and_or_distrib_right, BitVec.and_assoc]
  have hm1 : keepExHi8 &&& maskLo8 = maskLo8 := rfl
  rw [hm1]
  have hz : ((v &&& maskLo8) <<< 8) &&& maskLo8 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft]
    rw [show maskLo8.toNat = 255 from rfl]
    have hlt : v.toNat &&& 255 < 2 ^ 8 :=
      Nat.and_lt_two_pow v.toNat (by decide : 255 < 2 ^ 8)
    have hsh : ((v.toNat &&& 255) <<< 8) % 2 ^ 64 = (v.toNat &&& 255) * 256 := by
      rw [Nat.shiftLeft_eq]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hsh]
    have hmod := Nat.and_two_pow_sub_one_eq_mod ((v.toNat &&& 255) * 256) 8
    have hzero : ((v.toNat &&& 255) * 256) % 2 ^ 8 = 0 := by omega
    rw [show (2 ^ 8 - 1 : Nat) = 255 from rfl] at hmod
    rw [hmod, hzero]
    rfl
  rw [hz, BitVec.or_zero]

theorem lo32Zext_clobbers_upper_canary :
    let r : BitVec 64 := 0x0000_0001_0000_0000#64
    let v : BitVec 64 := 0#64
    writeLane .lo32Zext r v ≠ r := by
  decide

/-! ## 3. Unified Direct x86-64 Instruction Codec -/

structure Gpr4 where
  rex : Bool
  lo3 : BitVec 3
  deriving DecidableEq, Repr

inductive Cond4 where
  | o | no | b | ae | e | ne | be | a | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, Repr

def Cond4.toBitVec : Cond4 → BitVec 4
  | .o => 0 | .no => 1 | .b => 2 | .ae => 3
  | .e => 4 | .ne => 5 | .be => 6 | .a => 7
  | .s => 8 | .ns => 9 | .p => 10 | .np => 11
  | .l => 12 | .ge => 13 | .le => 14 | .g => 15

def Cond4.ofNibble (n : BitVec 4) : Cond4 :=
  match n.toNat with
  | 0 => .o | 1 => .no | 2 => .b | 3 => .ae
  | 4 => .e | 5 => .ne | 6 => .be | 7 => .a
  | 8 => .s | 9 => .ns | 10 => .p | 11 => .np
  | 12 => .l | 13 => .ge | 14 => .le | _ => .g

inductive X64Inst where
  | add64RR (dst src : Gpr4)
  | xor32RRZext (dst src : Gpr4)
  | push64 (reg : Gpr4)
  | pop64 (reg : Gpr4)
  | callRel32 (rel : BitVec 32)
  | jccRel8 (cc : Cond4) (rel : BitVec 8)
  | jccRel32 (cc : Cond4) (rel : BitVec 32)
  | ret
  deriving DecidableEq, Repr

private def rexByte (w r b : Bool) : UInt8 :=
  UInt8.ofNat (0x40 + (if w then 8 else 0) + (if r then 4 else 0) + (if b then 1 else 0))

private def modrmRegReg (reg rm : BitVec 3) : UInt8 :=
  UInt8.ofNat (0xC0 + reg.toNat * 8 + rm.toNat)

private def le32Bytes (imm : BitVec 32) : List UInt8 :=
  [ UInt8.ofNat (imm.toNat % 256),
    UInt8.ofNat ((imm.toNat / 256) % 256),
    UInt8.ofNat ((imm.toNat / 65536) % 256),
    UInt8.ofNat ((imm.toNat / 16777216) % 256) ]

private def ofLe32Bytes (b0 b1 b2 b3 : UInt8) : BitVec 32 :=
  BitVec.ofNat 32 (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216)

def encodeInst : X64Inst → List UInt8
  | .add64RR dst src =>
      [rexByte true src.rex dst.rex, 0x01, modrmRegReg src.lo3 dst.lo3]
  | .xor32RRZext dst src =>
      [rexByte false src.rex dst.rex, 0x31, modrmRegReg src.lo3 dst.lo3]
  | .push64 reg =>
      [rexByte false false reg.rex, UInt8.ofNat (0x50 + reg.lo3.toNat)]
  | .pop64 reg =>
      [rexByte false false reg.rex, UInt8.ofNat (0x58 + reg.lo3.toNat)]
  | .callRel32 rel =>
      0xE8 :: le32Bytes rel
  | .jccRel8 cc rel =>
      [UInt8.ofNat (0x70 + cc.toBitVec.toNat), UInt8.ofNat rel.toNat]
  | .jccRel32 cc rel =>
      [0x0F, UInt8.ofNat (0x80 + cc.toBitVec.toNat)] ++ le32Bytes rel
  | .ret =>
      [0xC3]

def decodeOne : List UInt8 → Option (X64Inst × List UInt8)
  | 0xC3 :: rest =>
      some (.ret, rest)
  | 0xE8 :: b0 :: b1 :: b2 :: b3 :: rest =>
      some (.callRel32 (ofLe32Bytes b0 b1 b2 b3), rest)
  | 0x0F :: op :: b0 :: b1 :: b2 :: b3 :: rest =>
      if 0x80 ≤ op.toNat && op.toNat ≤ 0x8F then
        let cc := Cond4.ofNibble (BitVec.ofNat 4 (op.toNat - 0x80))
        some (.jccRel32 cc (ofLe32Bytes b0 b1 b2 b3), rest)
      else none
  | op :: rel :: rest =>
      if 0x70 ≤ op.toNat && op.toNat ≤ 0x7F then
        let cc := Cond4.ofNibble (BitVec.ofNat 4 (op.toNat - 0x70))
        some (.jccRel8 cc (BitVec.ofNat 8 rel.toNat), rest)
      else if 0x40 ≤ op.toNat && op.toNat ≤ 0x4F then
        let w := (op.toNat / 8) % 2 == 1
        let r := (op.toNat / 4) % 2 == 1
        let b := op.toNat % 2 == 1
        if !w && !r && 0x50 ≤ rel.toNat && rel.toNat ≤ 0x57 then
          some (.push64 ⟨b, BitVec.ofNat 3 (rel.toNat - 0x50)⟩, rest)
        else if !w && !r && 0x58 ≤ rel.toNat && rel.toNat ≤ 0x5F then
          some (.pop64 ⟨b, BitVec.ofNat 3 (rel.toNat - 0x58)⟩, rest)
        else
          match rest with
          | modrm :: tail =>
              if modrm.toNat ≥ 0xC0 then
                let src : Gpr4 := ⟨r, BitVec.ofNat 3 ((modrm.toNat / 8) % 8)⟩
                let dst : Gpr4 := ⟨b, BitVec.ofNat 3 (modrm.toNat % 8)⟩
                if w && rel == 0x01 then
                  some (.add64RR dst src, tail)
                else if !w && rel == 0x31 then
                  some (.xor32RRZext dst src, tail)
                else none
              else none
          | [] => none
      else none
  | _ => none

private theorem ofLe32_le32 (imm : BitVec 32) :
    ofLe32Bytes
      (UInt8.ofNat (imm.toNat % 256))
      (UInt8.ofNat ((imm.toNat / 256) % 256))
      (UInt8.ofNat ((imm.toNat / 65536) % 256))
      (UInt8.ofNat ((imm.toNat / 16777216) % 256)) = imm := by
  apply BitVec.eq_of_toNat_eq
  have hlt : imm.toNat < 4294967296 := imm.isLt
  simp only [ofLe32Bytes, BitVec.toNat_ofNat, UInt8.toNat_ofNat']
  omega

private theorem gpr4_modrm_roundtrip (reg rm : BitVec 3) :
    ((modrmRegReg reg rm).toNat / 8) % 8 = reg.toNat ∧
    (modrmRegReg reg rm).toNat % 8 = rm.toNat ∧
    (modrmRegReg reg rm).toNat ≥ 0xC0 := by
  have h1 := reg.isLt
  have h2 := rm.isLt
  simp only [modrmRegReg, UInt8.toNat_ofNat']
  omega

theorem decodeOne_encodeInst_append (i : X64Inst) (rest : List UInt8) :
    decodeOne (encodeInst i ++ rest) = some (i, rest) := by
  cases i with
  | ret => rfl
  | callRel32 rel =>
      simp only [encodeInst, le32Bytes, List.cons_append, List.nil_append, decodeOne, ofLe32_le32]
  | jccRel8 cc rel =>
      cases cc <;>
      · simp only [encodeInst, Cond4.toBitVec, List.cons_append, List.nil_append, decodeOne]
        have hbv : BitVec.ofNat 8 (UInt8.ofNat rel.toNat).toNat = rel := by
          rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt rel.isLt]
          exact BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt rel.isLt])
        simp [hbv, Cond4.ofNibble]
  | jccRel32 cc rel =>
      cases cc <;>
      · simp only [encodeInst, Cond4.toBitVec, le32Bytes, List.cons_append, List.nil_append, decodeOne,
          ofLe32_le32, Cond4.ofNibble]
        rfl
  | push64 reg =>
      rcases reg with ⟨rb, ⟨rn, hrn⟩⟩
      cases rb <;> rcases rn with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
        first | (exfalso; simp only [Nat.reducePow] at hrn; omega)
              | (simp [encodeInst, rexByte, decodeOne]; try rfl)
  | pop64 reg =>
      rcases reg with ⟨rb, ⟨rn, hrn⟩⟩
      cases rb <;> rcases rn with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
        first | (exfalso; simp only [Nat.reducePow] at hrn; omega)
              | (simp [encodeInst, rexByte, decodeOne]; try rfl)
  | add64RR dst src =>
      rcases dst with ⟨db, dlo⟩
      rcases src with ⟨sb, slo⟩
      have hd := dlo.isLt; have hs := slo.isLt
      have hmr := gpr4_modrm_roundtrip slo dlo
      cases db <;> cases sb <;>
      · simp only [encodeInst, rexByte, List.cons_append, List.nil_append, decodeOne]
        have hd' : BitVec.ofNat 3 ((modrmRegReg slo dlo).toNat % 8) = dlo :=
          BitVec.eq_of_toNat_eq (by rw [hmr.2.1]; simp only [BitVec.toNat_ofNat]; omega)
        have hs' : BitVec.ofNat 3 (((modrmRegReg slo dlo).toNat / 8) % 8) = slo :=
          BitVec.eq_of_toNat_eq (by rw [hmr.1]; simp only [BitVec.toNat_ofNat]; omega)
        simp [hmr.2.2, hd', hs']
  | xor32RRZext dst src =>
      rcases dst with ⟨db, dlo⟩
      rcases src with ⟨sb, slo⟩
      have hd := dlo.isLt; have hs := slo.isLt
      have hmr := gpr4_modrm_roundtrip slo dlo
      cases db <;> cases sb <;>
      · simp only [encodeInst, rexByte, List.cons_append, List.nil_append, decodeOne]
        have hd' : BitVec.ofNat 3 ((modrmRegReg slo dlo).toNat % 8) = dlo :=
          BitVec.eq_of_toNat_eq (by rw [hmr.2.1]; simp only [BitVec.toNat_ofNat]; omega)
        have hs' : BitVec.ofNat 3 (((modrmRegReg slo dlo).toNat / 8) % 8) = slo :=
          BitVec.eq_of_toNat_eq (by rw [hmr.1]; simp only [BitVec.toNat_ofNat]; omega)
        simp [hmr.2.2, hd', hs']

def encodeStream (xs : List X64Inst) : List UInt8 :=
  xs.foldr (fun i acc => encodeInst i ++ acc) []

def decodeStream : Nat → List UInt8 → Option (List X64Inst)
  | 0, [] => some []
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, bs =>
      match decodeOne bs with
      | some (i, rest) =>
          match decodeStream fuel rest with
          | some tail => some (i :: tail)
          | none => none
      | none => none

private theorem decodeStream_succ (fuel : Nat) (b : UInt8) (bs : List UInt8) :
    decodeStream (fuel + 1) (b :: bs) =
      match decodeOne (b :: bs) with
      | some (i, rest) =>
          match decodeStream fuel rest with
          | some tail => some (i :: tail)
          | none => none
      | none => none := rfl

theorem decodeStream_encodeStream_id (xs : List X64Inst) :
    decodeStream xs.length (encodeStream xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change decodeStream (xs.length + 1) (encodeInst x ++ encodeStream xs) = some (x :: xs)
      have hne : encodeInst x ++ encodeStream xs ≠ [] := by
        cases x <;> simp [encodeInst]
      cases hcons : encodeInst x ++ encodeStream xs with
      | nil => exact absurd hcons hne
      | cons b bs =>
          rw [decodeStream_succ, ← hcons, decodeOne_encodeInst_append]
          change (match decodeStream xs.length (encodeStream xs) with
            | some tail => some (x :: tail) | none => none) = some (x :: xs)
          rw [ih]

/-! ## 4. Monotone Branch-Span Relaxation Fixed Point -/

inductive LayoutItem where
  | bytes (len : Nat)
  | label (id : Nat)
  | condBr (cc : Cond4) (target : Nat) (isWide : Bool)
  deriving DecidableEq, Repr

def LayoutItem.size : LayoutItem → Nat
  | .bytes n => n
  | .label _ => 0
  | .condBr _ _ false => 2
  | .condBr _ _ true  => 6

def totalSize (xs : List LayoutItem) : Nat :=
  xs.foldr (fun it acc => it.size + acc) 0

def inSigned8 (disp : Int) : Bool :=
  -128 ≤ disp && disp ≤ 127

def labelPosAux (pc : Nat) (tgt : Nat) : List LayoutItem → Option Nat
  | [] => none
  | it :: rest =>
      if it == .label tgt then some pc
      else labelPosAux (pc + it.size) tgt rest

def relaxItem (pc : Nat) (all : List LayoutItem) (it : LayoutItem) : LayoutItem × Bool :=
  match it with
  | .condBr cc tgt false =>
      match labelPosAux 0 tgt all with
      | some tgtPc =>
          let disp : Int := Int.ofNat tgtPc - Int.ofNat (pc + 2)
          if inSigned8 disp then (.condBr cc tgt false, false)
          else (.condBr cc tgt true, true)
      | none => (.condBr cc tgt true, true)
  | other => (other, false)

def relaxPassAux (pc : Nat) (all : List LayoutItem) : List LayoutItem → List LayoutItem × Bool
  | [] => ([], false)
  | it :: rest =>
      let (it', ch1) := relaxItem pc all it
      let (rest', ch2) := relaxPassAux (pc + it.size) all rest
      (it' :: rest', ch1 || ch2)

def narrowCount : List LayoutItem → Nat
  | [] => 0
  | .condBr _ _ false :: rest => 1 + narrowCount rest
  | _ :: rest => narrowCount rest

def isNarrow : LayoutItem → Nat
  | .condBr _ _ false => 1
  | _ => 0

private theorem narrowCount_cons (it : LayoutItem) (xs : List LayoutItem) :
    narrowCount (it :: xs) = isNarrow it + narrowCount xs := by
  cases it with
  | bytes _ => simp [narrowCount, isNarrow]
  | label _ => simp [narrowCount, isNarrow]
  | condBr _ _ w => cases w <;> simp [narrowCount, isNarrow]

private theorem relaxItem_size_ge (pc : Nat) (all : List LayoutItem) (it : LayoutItem) :
    (relaxItem pc all it).1.size ≥ it.size := by
  cases it with
  | bytes n => simp [relaxItem, LayoutItem.size]
  | label k => simp [relaxItem, LayoutItem.size]
  | condBr cc tgt wide =>
      cases wide
      · simp only [relaxItem]
        cases h1 : labelPosAux 0 tgt all with
        | none => simp [LayoutItem.size]
        | some tgtPc =>
            dsimp only
            split <;> simp [LayoutItem.size]
      · simp [relaxItem, LayoutItem.size]

private theorem relaxItem_isNarrow_le (pc : Nat) (all : List LayoutItem) (it : LayoutItem) :
    isNarrow (relaxItem pc all it).1 ≤ isNarrow it := by
  cases it with
  | bytes _ => simp [relaxItem]
  | label _ => simp [relaxItem]
  | condBr cc tgt wide =>
      cases wide
      · simp only [relaxItem]
        cases labelPosAux 0 tgt all with
        | none => simp [isNarrow]
        | some _ => dsimp only; split <;> simp [isNarrow]
      · simp [relaxItem]

private theorem relaxItem_isNarrow_lt (pc : Nat) (all : List LayoutItem) (it : LayoutItem)
    (hch : (relaxItem pc all it).2 = true) :
    isNarrow (relaxItem pc all it).1 < isNarrow it := by
  cases it with
  | bytes _ => simp [relaxItem] at hch
  | label _ => simp [relaxItem] at hch
  | condBr cc tgt wide =>
      cases wide
      · cases h1 : labelPosAux 0 tgt all with
        | none =>
            simp only [relaxItem, h1] at hch ⊢
            simp [isNarrow]
        | some tgtPc =>
            simp only [relaxItem, h1] at hch ⊢
            split at hch
            · simp at hch
            · rename_i hneg
              have hneg' : ¬inSigned8 (↑tgtPc - (↑pc + 2)) = true := by simpa using hneg
              simp [hneg', isNarrow]
      · simp [relaxItem] at hch

theorem relaxPassAux_size_ge (pc : Nat) (all xs : List LayoutItem) :
    totalSize (relaxPassAux pc all xs).1 ≥ totalSize xs := by
  induction xs generalizing pc with
  | nil => simp [relaxPassAux, totalSize]
  | cons it rest ih =>
      simp only [relaxPassAux, totalSize, List.foldr_cons]
      have h1 := relaxItem_size_ge pc all it
      have h2 := ih (pc + it.size)
      change (relaxItem pc all it).1.size + totalSize (relaxPassAux (pc + it.size) all rest).1 ≥
        it.size + totalSize rest
      omega

theorem relaxPassAux_narrow_le (pc : Nat) (all xs : List LayoutItem) :
    narrowCount (relaxPassAux pc all xs).1 ≤ narrowCount xs := by
  induction xs generalizing pc with
  | nil => simp [relaxPassAux, narrowCount]
  | cons it rest ih =>
      simp only [relaxPassAux, narrowCount_cons]
      have h1 := relaxItem_isNarrow_le pc all it
      have h2 := ih (pc + it.size)
      omega

theorem relaxPassAux_narrow_lt (pc : Nat) (all xs : List LayoutItem)
    (hch : (relaxPassAux pc all xs).2 = true) :
    narrowCount (relaxPassAux pc all xs).1 < narrowCount xs := by
  induction xs generalizing pc with
  | nil => simp [relaxPassAux] at hch
  | cons it rest ih =>
      simp only [relaxPassAux, narrowCount_cons] at hch ⊢
      have h1_le := relaxItem_isNarrow_le pc all it
      have h2_le := relaxPassAux_narrow_le (pc + it.size) all rest
      cases hA : (relaxItem pc all it).2 with
      | true =>
          have hlt := relaxItem_isNarrow_lt pc all it hA
          omega
      | false =>
          have hB : (relaxPassAux (pc + it.size) all rest).2 = true := by
            rw [hA, Bool.false_or] at hch
            exact hch
          have hlt := ih (pc + it.size) hB
          omega

def relaxLoop : Nat → List LayoutItem → List LayoutItem
  | 0, xs => xs
  | fuel + 1, xs =>
      let (xs', changed) := relaxPassAux 0 xs xs
      if changed then relaxLoop fuel xs' else xs'

def allNarrowBranchesInRangeAux (pc : Nat) (all : List LayoutItem) : List LayoutItem → Bool
  | [] => true
  | .condBr _ tgt false :: rest =>
      (match labelPosAux 0 tgt all with
       | some tgtPc => inSigned8 (Int.ofNat tgtPc - Int.ofNat (pc + 2))
       | none => false) &&
      allNarrowBranchesInRangeAux (pc + 2) all rest
  | it :: rest => allNarrowBranchesInRangeAux (pc + it.size) all rest

theorem relaxPassAux_unchanged_eq (pc : Nat) (all xs : List LayoutItem)
    (hunch : (relaxPassAux pc all xs).2 = false) :
    (relaxPassAux pc all xs).1 = xs := by
  induction xs generalizing pc with
  | nil => rfl
  | cons it rest ih =>
      simp only [relaxPassAux] at hunch ⊢
      have hA : (relaxItem pc all it).2 = false := by
        cases h1 : (relaxItem pc all it).2 <;> simp_all
      have hB : (relaxPassAux (pc + it.size) all rest).2 = false := by
        rw [hA, Bool.false_or] at hunch; exact hunch
      have h_it : (relaxItem pc all it).1 = it := by
        cases it with
        | bytes _ => rfl
        | label _ => rfl
        | condBr cc tgt wide =>
            cases wide
            · cases h1 : labelPosAux 0 tgt all with
              | none => simp [relaxItem, h1] at hA
              | some tgtPc =>
                  simp only [relaxItem, h1] at hA ⊢
                  split at hA
                  · rename_i hpos
                    have hpos' : inSigned8 (↑tgtPc - (↑pc + 2)) = true := by simpa using hpos
                    simp [hpos']
                  · simp at hA
            · rfl
      rw [h_it, ih (pc + it.size) hB]

theorem relaxPassAux_unchanged_valid (pc : Nat) (all xs : List LayoutItem)
    (hunch : (relaxPassAux pc all xs).2 = false) :
    allNarrowBranchesInRangeAux pc all xs = true := by
  induction xs generalizing pc with
  | nil => rfl
  | cons it rest ih =>
      simp only [relaxPassAux] at hunch
      have hA : (relaxItem pc all it).2 = false := by
        cases h1 : (relaxItem pc all it).2 <;> simp_all
      have hB : (relaxPassAux (pc + it.size) all rest).2 = false := by
        rw [hA, Bool.false_or] at hunch; exact hunch
      have hrest := ih (pc + it.size) hB
      cases it with
      | bytes n => simpa [allNarrowBranchesInRangeAux, LayoutItem.size] using hrest
      | label k => simpa [allNarrowBranchesInRangeAux, LayoutItem.size] using hrest
      | condBr cc tgt wide =>
          cases wide with
          | true => simpa [allNarrowBranchesInRangeAux, LayoutItem.size] using hrest
          | false =>
              cases h1 : labelPosAux 0 tgt all with
              | none => simp [relaxItem, h1] at hA
              | some tgtPc =>
                  simp only [relaxItem, h1] at hA
                  have hpos : inSigned8 (Int.ofNat tgtPc - Int.ofNat (pc + 2)) = true := by
                    split at hA
                    · assumption
                    · simp at hA
                  simp only [allNarrowBranchesInRangeAux, h1, Bool.and_eq_true]
                  refine ⟨?_, ?_⟩
                  · simpa using hpos
                  · simpa [LayoutItem.size] using hrest

theorem relaxLoop_converges_valid (fuel : Nat) (xs : List LayoutItem)
    (hfuel : narrowCount xs < fuel) :
    allNarrowBranchesInRangeAux 0 (relaxLoop fuel xs) (relaxLoop fuel xs) = true := by
  induction fuel generalizing xs with
  | zero => omega
  | succ f ih =>
      simp only [relaxLoop]
      cases hch : (relaxPassAux 0 xs xs).2 with
      | false =>
          have heq := relaxPassAux_unchanged_eq 0 xs xs hch
          have hval := relaxPassAux_unchanged_valid 0 xs xs hch
          simpa [heq] using hval
      | true =>
          have hlt := relaxPassAux_narrow_lt 0 xs xs hch
          simpa using ih (relaxPassAux 0 xs xs).1 (by omega)

/-! ## 5. Non-Tautological Machine Outliner + Unwind CFA Restoration -/

structure MachState where
  regs : Gpr4 → BitVec 64
  sp : BitVec 64
  stack : BitVec 64 → BitVec 64

inductive FrameOp where
  | addImm (dst : Gpr4) (imm : BitVec 64)
  | loadSp (dst : Gpr4) (off : BitVec 64)
  | storeSp (src : Gpr4) (off : BitVec 64)
  deriving Repr

def FrameOp.shiftSp (delta : BitVec 64) : FrameOp → FrameOp
  | .addImm dst imm => .addImm dst imm
  | .loadSp dst off => .loadSp dst (off + delta)
  | .storeSp src off => .storeSp src (off + delta)

def execFrameOp (op : FrameOp) (st : MachState) : MachState :=
  match op with
  | .addImm dst imm =>
      { st with regs := fun r => if r == dst then st.regs dst + imm else st.regs r }
  | .loadSp dst off =>
      { st with regs := fun r => if r == dst then st.stack (st.sp + off) else st.regs r }
  | .storeSp src off =>
      { st with stack := fun a => if a == st.sp + off then st.regs src else st.stack a }

def execInline (ops : List FrameOp) (st : MachState) : MachState :=
  ops.foldl (fun s op => execFrameOp op s) st

def execOutlinedCall (retAddr : BitVec 64) (thunkOps : List FrameOp) (st : MachState) : MachState :=
  let sp' := st.sp - 8#64
  let pushed : MachState :=
    { st with
      sp := sp'
      stack := fun a => if a == sp' then retAddr else st.stack a }
  let after := execInline thunkOps pushed
  { after with sp := after.sp + 8#64 }

def nonAliasingWithReturnSlot (ops : List FrameOp) : Prop :=
  ∀ op ∈ ops, match op with
    | .addImm _ _ => True
    | .loadSp _ off => off + 8#64 ≠ 0#64
    | .storeSp _ off => off + 8#64 ≠ 0#64

private def statesAgree (sp0 : BitVec 64) (s1 s2 : MachState) : Prop :=
  s1.regs = s2.regs ∧
  s1.sp = sp0 - 8#64 ∧
  s2.sp = sp0 ∧
  ∀ a, a ≠ sp0 - 8#64 → s1.stack a = s2.stack a

private theorem addr_shift_eq (sp off : BitVec 64) :
    (sp - 8#64) + (off + 8#64) = sp + off := by
  rw [BitVec.add_comm off 8#64, ← BitVec.add_assoc, BitVec.sub_add_cancel]

private theorem addr_shift_ne_retSlot (sp off : BitVec 64) (hne : off + 8#64 ≠ 0#64) :
    sp + off ≠ sp - 8#64 := by
  intro heq
  apply hne
  have h1 := congrArg (· + 8#64) heq
  rw [BitVec.sub_add_cancel, BitVec.add_assoc, BitVec.add_comm sp (off + 8#64)] at h1
  have h2 := congrArg (· - sp) h1
  rw [BitVec.add_sub_cancel, BitVec.sub_self] at h2
  exact h2

theorem outlined_thunk_simulates_inline
    (retAddr : BitVec 64) (ops : List FrameOp) (st : MachState)
    (hnoalias : nonAliasingWithReturnSlot ops) :
    let outSt := execOutlinedCall retAddr (ops.map (FrameOp.shiftSp 8#64)) st
    let inSt  := execInline ops st
    outSt.regs = inSt.regs ∧
    outSt.sp = inSt.sp ∧
    ∀ a, a ≠ st.sp - 8#64 → outSt.stack a = inSt.stack a := by
  have hfold : ∀ (xs : List FrameOp) (s1 s2 : MachState),
      nonAliasingWithReturnSlot xs →
      statesAgree st.sp s1 s2 →
      statesAgree st.sp
        (execInline (xs.map (FrameOp.shiftSp 8#64)) s1)
        (execInline xs s2) := by
    intro xs
    induction xs with
    | nil =>
        intro s1 s2 _ hagr
        exact hagr
    | cons op xs ih =>
        intro s1 s2 hna ⟨hregs, hsp1, hsp2, hstk⟩
        apply ih
        · intro x hx; exact hna x (List.mem_cons_of_mem op hx)
        · have hop := hna op List.mem_cons_self
          cases op with
          | addImm dst imm =>
              refine ⟨?_, hsp1, hsp2, hstk⟩
              funext r
              simp only [FrameOp.shiftSp, execFrameOp, hregs]
          | loadSp dst off =>
              have hne_off : off + 8#64 ≠ 0#64 := hop
              have haddr : s1.sp + (off + 8#64) = s2.sp + off := by
                rw [hsp1, hsp2]; exact addr_shift_eq st.sp off
              have hnot : s2.sp + off ≠ st.sp - 8#64 := by
                rw [hsp2]; exact addr_shift_ne_retSlot st.sp off hne_off
              refine ⟨?_, hsp1, hsp2, hstk⟩
              funext r
              simp only [FrameOp.shiftSp, execFrameOp, hregs, haddr]
              split <;> simp [hstk _ hnot]
          | storeSp src off =>
              have hne_off : off + 8#64 ≠ 0#64 := hop
              have haddr : s1.sp + (off + 8#64) = s2.sp + off := by
                rw [hsp1, hsp2]; exact addr_shift_eq st.sp off
              refine ⟨hregs, hsp1, hsp2, ?_⟩
              intro a ha
              simp only [FrameOp.shiftSp, execFrameOp, haddr, hregs]
              by_cases heq : a = s2.sp + off
              · simp [heq]
              · simp [heq, hstk a ha]
  have hinit : statesAgree st.sp
      { st with sp := st.sp - 8#64, stack := fun a => if a == st.sp - 8#64 then retAddr else st.stack a }
      st := by
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro a ha
    have hbeq : (a == st.sp - 8#64) = false := beq_false_of_ne ha
    simp [hbeq]
  rcases hfold ops _ st hnoalias hinit with ⟨hr, hs1, hs2, hmem⟩
  refine ⟨hr, ?_, hmem⟩
  dsimp only [execOutlinedCall]
  rw [hs1, hs2, BitVec.sub_add_cancel]

/-- DWARF FDE unwinding evaluates caller CFA (`sp + cfaOffset`) and caller return
    address (`stack (cfa - raSlotOffset)`). -/
def evalFdeUnwind (cfaOffset raSlotOffset : BitVec 64) (st : MachState) :
    BitVec 64 × BitVec 64 :=
  let cfa := st.sp + cfaOffset
  (cfa, st.stack (cfa - raSlotOffset))

theorem fde_unwind_restores_caller
    (retAddr : BitVec 64) (ops : List FrameOp) (st : MachState)
    (hnoalias : nonAliasingWithReturnSlot ops) :
    let sp' := st.sp - 8#64
    let pushed : MachState :=
      { st with
        sp := sp'
        stack := fun a => if a == sp' then retAddr else st.stack a }
    let midSt := execInline (ops.map (FrameOp.shiftSp 8#64)) pushed
    evalFdeUnwind 8#64 8#64 midSt = (st.sp, retAddr) := by
  have hfold : ∀ (xs : List FrameOp) (s : MachState),
      nonAliasingWithReturnSlot xs →
      s.sp = st.sp - 8#64 →
      s.stack (st.sp - 8#64) = retAddr →
      (execInline (xs.map (FrameOp.shiftSp 8#64)) s).sp = st.sp - 8#64 ∧
      (execInline (xs.map (FrameOp.shiftSp 8#64)) s).stack (st.sp - 8#64) = retAddr := by
    intro xs
    induction xs with
    | nil => intro s _ h1 h2; exact ⟨h1, h2⟩
    | cons op xs ih =>
        intro s hna hsp hret
        apply ih
        · intro x hx; exact hna x (List.mem_cons_of_mem op hx)
        · cases op <;> exact hsp
        · have hop := hna op List.mem_cons_self
          cases op with
          | addImm _ _ => exact hret
          | loadSp _ _ => exact hret
          | storeSp src off =>
              simp only [FrameOp.shiftSp, execFrameOp]
              have hne : (st.sp - 8#64) ≠ s.sp + (off + 8#64) := by
                rw [hsp, addr_shift_eq st.sp off]
                exact Ne.symm (addr_shift_ne_retSlot st.sp off hop)
              have hbeq : (st.sp - 8#64 == s.sp + (off + 8#64)) = false := beq_false_of_ne hne
              simp [hbeq, hret]
  let pushed0 : MachState :=
    { st with sp := st.sp - 8#64, stack := fun a => if a == st.sp - 8#64 then retAddr else st.stack a }
  have hmid := hfold ops pushed0 hnoalias rfl (by simp [pushed0])
  simp only [evalFdeUnwind]
  rw [hmid.1, BitVec.sub_add_cancel, hmid.2]

end MiniMachProbe

#print axioms MiniMachProbe.srai_equiv_no_bv_decide
#print axioms MiniMachProbe.readLane_writeLane_lo32Zext
#print axioms MiniMachProbe.writeLane_lo32Zext_clears_upper
#print axioms MiniMachProbe.disjoint_lo8_writes_preserve_hi8
#print axioms MiniMachProbe.disjoint_hi8_writes_preserve_lo8
#print axioms MiniMachProbe.lo32Zext_clobbers_upper_canary
#print axioms MiniMachProbe.decodeOne_encodeInst_append
#print axioms MiniMachProbe.decodeStream_encodeStream_id
#print axioms MiniMachProbe.relaxPassAux_size_ge
#print axioms MiniMachProbe.relaxLoop_converges_valid
#print axioms MiniMachProbe.outlined_thunk_simulates_inline
#print axioms MiniMachProbe.fde_unwind_restores_caller

