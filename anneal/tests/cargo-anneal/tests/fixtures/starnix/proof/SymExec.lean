-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import SourceInputs
import Init.ByCases
import Init.Classical
import Init.Data.BitVec.Bootstrap
import Init.Data.BitVec.Lemmas
import Init.Data.Option.Lemmas

@[expose] public section

namespace SymExec

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Endianness

/-!
Kernel-evaluated symbolic execution of one captured body. Control flow and
every non-`u64` value must be concrete; `u64` words may depend on a single
symbolic input word. `symRun_sound` transfers every symbolic step to the
trusted `evalStep`, so no proof names a MIR local, block or statement index.
Anything outside this fragment makes the evaluator stop, which fails closed.
-/

/-- `u64` word expressions over the single symbolic input word. -/
inductive Sym where
  | input
  | lit (w : Word)
  | and (l r : Sym)
  | or (l r : Sym)
  | shl (l : Sym) (k : Nat)
  | shr (l : Sym) (k : Nat)

/-- The word that an expression denotes when the input is `x`. -/
def Sym.eval (x : Word) : Sym → Word
  | .input => x
  | .lit w => w
  | .and l r => l.eval x &&& r.eval x
  | .or l r => l.eval x ||| r.eval x
  | .shl l k => l.eval x <<< k
  | .shr l k => l.eval x >>> k

/-- A local's value: concrete, or a `u64` word over the input. -/
inductive SVal where
  | conc (v : Val)
  | word (s : Sym)

/-- The value denoted when the input is `x`. -/
def SVal.val (x : Word) : SVal → Val
  | .conc v => v
  | .word s => u64Val (s.eval x)

/-- A local slot whose value may depend on the input. -/
inductive SSlot where
  | dead
  | immediate (v : Option SVal)
  | indirect (place : MemPlace)

/-- The slot denoted when the input is `x`. -/
def SSlot.slot (x : Word) : SSlot → LocalSlot
  | .dead => .dead
  | .immediate v => .immediate (v.map (SVal.val x))
  | .indirect place => .indirect place

/-- Embed a concrete slot. -/
def SSlot.ofSlot : LocalSlot → SSlot
  | .dead => .dead
  | .immediate v => .immediate (v.map .conc)
  | .indirect place => .indirect place

theorem SSlot.slot_ofSlot (x : Word) (s : LocalSlot) :
    (SSlot.ofSlot s).slot x = s := by
  cases s with
  | dead => rfl
  | immediate v => cases v <;> rfl
  | indirect _ => rfl

/-- A single-frame state of body `0` whose locals may depend on the input. -/
structure SState where
  block : Nat
  stmt : Nat
  slots : List SSlot

/-- The frame denoted when the input is `x`. -/
def SState.frame (x : Word) (s : SState) : FrameState :=
  { defId := 0, blockIdx := s.block, stmtIdx := s.stmt,
    locals := s.slots.map (SSlot.slot x) }

/-- The state denoted when the input is `x`. -/
noncomputable def SState.state (x : Word) (s : SState) : State :=
  mkState s.block s.stmt (s.slots.map (SSlot.slot x))

/-- Outcome of one symbolic step. -/
inductive SRes where
  | step (s : SState)
  | ret (v : SVal)
  | stuck

theorem getElem?_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (n : Nat), Trusted.MirSemantics.getElem? (l.map f) n =
      (Trusted.MirSemantics.getElem? l n).map f
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => getElem?_map f l n

theorem setElem?_map {α β : Type} (f : α → β) :
    ∀ (l : List α) (n : Nat) (v : α),
      setElem? (l.map f) n (f v) = (setElem? l n v).map (List.map f)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | y :: l, n + 1, v => by
    have ih := setElem?_map f l n v
    show (match setElem? (l.map f) n (f v) with
      | some xs' => some (f y :: xs')
      | none => none) =
      (match setElem? l n v with
      | some xs' => some (y :: xs')
      | none => none).map (List.map f)
    rw [ih]
    cases setElem? l n v <;> rfl

/-! ### Operands and values -/

/-- Mirror of `evalOperandToSlot`; `none` marks anything unsupported. -/
noncomputable def sOperand (tys : List MirTy) (ls : List SSlot) :
    Operand → Option (MirTy × Option SVal × List SSlot)
  | .copy p =>
    if p.projection.isEmpty then
      match Trusted.MirSemantics.getElem? tys p.localId,
          Trusted.MirSemantics.getElem? ls p.localId with
      | some ty, some (.immediate v) => some (ty, v, ls)
      | _, _ => none
    else none
  | .move p =>
    if p.projection.isEmpty then
      match Trusted.MirSemantics.getElem? tys p.localId,
          Trusted.MirSemantics.getElem? ls p.localId with
      | some ty, some (.immediate v) =>
        (setElem? ls p.localId (SSlot.ofSlot (liveUninitSlot ty))).map
          fun ls' => (ty, v, ls')
      | _, _ => none
    else none
  | .constant c =>
    match evalConstLit c.ty c.lit with
    | .ok v => some (c.ty, some (.conc v), ls)
    | .error _ => none

theorem sOperand_sound {tys : List MirTy} {ls ls' : List SSlot}
    {op : Operand} {ty : MirTy} {v : Option SVal} {tyOk : MirTy → Bool}
    (x : Word) (h : sOperand tys ls op = some (ty, v, ls')) :
    evalOperandToSlot tys (ls.map (SSlot.slot x)) entryMemory tyOk op =
      .ok (ty, v.map (SVal.val x), ls'.map (SSlot.slot x), entryMemory) := by
  cases op with
  | copy p =>
    simp only [sOperand] at h
    split at h
    · rename_i hp
      split at h
      · rename_i ty0 v0 ht hs
        cases h
        simp only [evalOperandToSlot, hp, Bool.not_true, getElem?_map, ht, hs]
        rfl
      · cases h
    · cases h
  | move p =>
    simp only [sOperand] at h
    split at h
    · rename_i hp
      split at h
      · rename_i ty0 v0 ht hs
        obtain ⟨l1, hset, he⟩ := Option.map_eq_some_iff.mp h
        have hmap := setElem?_map (SSlot.slot x) ls p.localId
          (SSlot.ofSlot (liveUninitSlot ty0))
        rw [SSlot.slot_ofSlot, hset] at hmap
        cases he
        simp only [evalOperandToSlot, hp, Bool.not_true, getElem?_map, ht, hs,
          Option.map, SSlot.slot, hmap]
        rfl
      · cases h
    · cases h
  | constant c =>
    simp only [sOperand] at h
    split at h
    · rename_i val hc
      cases h
      simp only [evalOperandToSlot, hc]
      rfl
    · cases h

/-- Mirror of `evalPrimitiveOperand`. -/
noncomputable def sPrim (tys : List MirTy) (ls : List SSlot) (op : Operand) :
    Option (SVal × List SSlot) :=
  match sOperand tys ls op with
  | some (ty, some v, ls') =>
    if isPrimitiveReadableTy ty then some (v, ls') else none
  | _ => none

theorem sPrim_sound {tys : List MirTy} {ls ls' : List SSlot} {op : Operand}
    {v : SVal} (x : Word) (h : sPrim tys ls op = some (v, ls')) :
    evalPrimitiveOperand tys (ls.map (SSlot.slot x)) entryMemory op =
      .ok (v.val x, ls'.map (SSlot.slot x), entryMemory) := by
  simp only [sPrim] at h
  split at h
  · rename_i ty v0 l1 ho
    split at h
    · rename_i hty
      cases h
      simp only [evalPrimitiveOperand, sOperand_sound x ho, hty, Bool.not_true,
        Option.map]
      rfl
    · cases h
  · cases h

/-- View a value as a `u64` word expression, if it is one. -/
noncomputable def SVal.sym? : SVal → Option Sym
  | .word s => some s
  | .conc (.scalar sv) =>
    if IntWidth.beq sv.width .i64 && !sv.signed &&
        BitVec.ofNat 128 (BitVec.ofNat 64 sv.bits.toNat).toNat == sv.bits then
      some (.lit (BitVec.ofNat 64 sv.bits.toNat))
    else none
  | .conc _ => none

theorem SVal.sym?_sound {v : SVal} {s : Sym} (x : Word) (h : v.sym? = some s) :
    v.val x = u64Val (s.eval x) := by
  cases v with
  | word s' =>
    cases h
    rfl
  | conc c =>
    cases c <;> try cases h
    rename_i sv
    obtain ⟨w, sg, b⟩ := sv
    simp only [SVal.sym?] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      obtain ⟨⟨hw, hs⟩, hb⟩ := hc
      subst hs
      cases IntWidth.beq_iff.mp hw
      show Val.scalar ⟨.i64, false, b⟩ = .scalar ⟨.i64, false,
        BitVec.ofNat 128 (BitVec.ofNat 64 b.toNat).toNat⟩
      rw [hb]
    · cases h

/-- The shift amount `evalShiftOp` applies to a `u64` left operand. -/
noncomputable def shiftAmt (k : ScalarVal) : Nat :=
  (intEmod (decodeScalar k) (Int.ofNat 64)).toNat

/-- A concrete scalar right operand's shift amount. -/
noncomputable def SVal.shift? : SVal → Option ScalarVal
  | .conc (.scalar k) => some k
  | _ => none

theorem SVal.shift?_sound {v : SVal} {k : ScalarVal} (x : Word)
    (h : v.shift? = some k) : v.val x = .scalar k := by
  cases v with
  | word _ => cases h
  | conc c => cases c <;> cases h <;> rfl

theorem evalBinOp_and_u64 (a b : Word) :
    evalBinOp .bitAnd (u64Val a) (u64Val b) = .ok (u64Val (a &&& b)) := by
  change Except.ok (.scalar ⟨.i64, false,
      truncateBits .i64 (bvAnd (truncateBits .i64 (bvZeroExtend 128 a))
        (truncateBits .i64 (bvZeroExtend 128 b)))⟩) =
    .ok (u64Val (a &&& b))
  rw [u64BitAnd_sem_eq a b, u64BitAndVal_eq]
  simp only [u64Val, BitVec.toNat_and]
  rfl

theorem evalBinOp_or_u64 (a b : Word) :
    evalBinOp .bitOr (u64Val a) (u64Val b) = .ok (u64Val (a ||| b)) := by
  change Except.ok (.scalar ⟨.i64, false,
      truncateBits .i64 (bvOr (truncateBits .i64 (bvZeroExtend 128 a))
        (truncateBits .i64 (bvZeroExtend 128 b)))⟩) =
    .ok (u64Val (a ||| b))
  rw [u64BitOr_sem_eq a b, u64BitOrVal_eq]
  simp only [u64Val, BitVec.toNat_or]
  rfl

theorem evalBinOp_shl_u64 (a : Word) (k : ScalarVal) :
    evalBinOp .shl (u64Val a) (.scalar k) =
      .ok (u64Val (a <<< shiftAmt k)) := by
  have h :
      evalBinOp .shl (u64Val a) (.scalar k) =
      .ok (.scalar ⟨.i64, false,
        truncateBits .i64 (bvOfInt 128
          (.ofNat (Nat.shiftLeft
            (truncateBits .i64 (bvZeroExtend 128 a)).toNat
            (shiftAmt k))))⟩) := by
    unfold u64Val evalBinOp evalShiftOp truncateScalar
    dsimp only
    rw [ite_bool_true (rfl : BinOp.shl.isShift = true)]
    exact ite_bool_false (and_isUnchecked_false rfl)
  rw [h, u64Shl_sem_eq a (shiftAmt k), u64ShlVal_eq]
  have hshl : BitVec.ofNat 64 (Nat.shiftLeft a.toNat (shiftAmt k)) =
      a <<< shiftAmt k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft]
    rfl
  rw [hshl]
  rfl

theorem evalBinOp_shr_u64 (a : Word) (k : ScalarVal) :
    evalBinOp .shr (u64Val a) (.scalar k) =
      .ok (u64Val (a >>> shiftAmt k)) := by
  have h :
      evalBinOp .shr (u64Val a) (.scalar k) =
      .ok (.scalar ⟨.i64, false,
        truncateBits .i64 (bvOfInt 128
          (.ofNat (Nat.shiftRight
            (truncateBits .i64 (bvZeroExtend 128 a)).toNat
            (shiftAmt k))))⟩) := by
    unfold u64Val evalBinOp evalShiftOp truncateScalar
    dsimp only
    rw [ite_bool_true (rfl : BinOp.shr.isShift = true)]
    exact ite_bool_false (and_isUnchecked_false rfl)
  rw [h, u64Shr_sem_eq a (shiftAmt k), u64ShrVal_eq]
  simp only [u64Val, BitVec.toNat_ushiftRight]
  rfl

/-- `u64` bitwise operations, and shifts by a concrete amount, on words. -/
noncomputable def symBinOp (op : BinOp) (l r : SVal) : Option SVal :=
  match l.sym? with
  | none => none
  | some a =>
    match op with
    | .bitAnd => r.sym?.map fun b => .word (.and a b)
    | .bitOr => r.sym?.map fun b => .word (.or a b)
    | .shl => r.shift?.map fun k => .word (.shl a (shiftAmt k))
    | .shr => r.shift?.map fun k => .word (.shr a (shiftAmt k))
    | _ => none

theorem symBinOp_sound {op : BinOp} {l r v : SVal} (x : Word)
    (h : symBinOp op l r = some v) :
    evalBinOp op (l.val x) (r.val x) = .ok (v.val x) := by
  unfold symBinOp at h
  cases ha : l.sym? with
  | none =>
    rw [ha] at h
    cases h
  | some a =>
    rw [ha] at h
    rw [SVal.sym?_sound x ha]
    cases op <;> try cases h
    all_goals obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    · rw [SVal.sym?_sound x hb]
      exact evalBinOp_and_u64 _ _
    · rw [SVal.sym?_sound x hb]
      exact evalBinOp_or_u64 _ _
    · rw [SVal.shift?_sound x hb]
      exact evalBinOp_shl_u64 _ _
    · rw [SVal.shift?_sound x hb]
      exact evalBinOp_shr_u64 _ _

/-- Mirror of `evalBinOp`: concrete operands use it directly. -/
noncomputable def sBinOp (op : BinOp) (l r : SVal) : Option SVal :=
  match l, r with
  | .conc a, .conc b =>
    match evalBinOp op a b with
    | .ok v => some (.conc v)
    | .error _ => none
  | _, _ => symBinOp op l r

theorem sBinOp_sound {op : BinOp} {l r v : SVal} (x : Word)
    (h : sBinOp op l r = some v) :
    evalBinOp op (l.val x) (r.val x) = .ok (v.val x) := by
  unfold sBinOp at h
  split at h
  · rename_i a b
    split at h
    · rename_i w hw
      cases h
      exact hw
    · cases h
  · exact symBinOp_sound x h

/-- The discriminant `evalRvalue` reads from a scalar-tagged enum value. -/
noncomputable def sDiscr (ety ety' : EnumTy) (n : Nat) : Option Val :=
  match ety.tagRepr with
  | .scalar _ _ =>
    if enumAdmitted ety &&
        (EnumTy.beq ety ety' && Nat.blt n ety.discriminants.length) then
      (Trusted.MirSemantics.getElem? ety.discriminants n).map fun disc =>
        .scalar ⟨ety.discrWidth, ety.discrSigned,
          truncateBits ety.discrWidth (BitVec.ofNat 128 disc)⟩
    else none
  | .zeroSized => none

/-- Mirror of `evalRvalue` for `use`, binary operations and discriminants. -/
noncomputable def sRvalue (tys : List MirTy) (ls : List SSlot) (dst : MirTy) :
    Rvalue → Option (SVal × List SSlot)
  | .use op =>
    match sOperand tys ls op with
    | some (ty, some v, ls') => if MirTy.beq ty dst then some (v, ls') else none
    | _ => none
  | .binaryOp bop a b =>
    match sPrim tys ls a with
    | some (va, l1) =>
      match sPrim tys l1 b with
      | some (vb, l2) => (sBinOp bop va vb).map fun v => (v, l2)
      | none => none
    | none => none
  | .discriminant p =>
    if p.projection.isEmpty then
      match Trusted.MirSemantics.getElem? tys p.localId,
          Trusted.MirSemantics.getElem? ls p.localId with
      | some (.enum ety), some (.immediate (some (.conc (.enumVal ety' n)))) =>
        (sDiscr ety ety' n).map fun d => (.conc d, ls)
      | _, _ => none
    else none
  | _ => none

theorem sRvalue_sound {tys : List MirTy} {ls ls' : List SSlot} {dst : MirTy}
    {rv : Rvalue} {v : SVal} (x : Word)
    (h : sRvalue tys ls dst rv = some (v, ls')) :
    evalRvalue tys (ls.map (SSlot.slot x)) entryMemory dst rv =
      .ok (v.val x, ls'.map (SSlot.slot x), entryMemory) := by
  cases rv with
  | use op =>
    simp only [sRvalue] at h
    split at h
    · rename_i ty v0 l1 ho
      split at h
      · rename_i hty
        cases h
        simp only [evalRvalue, sOperand_sound x ho, hty, Bool.not_true,
          Option.map]
        rfl
      · cases h
    · cases h
  | binaryOp bop a b =>
    simp only [sRvalue] at h
    split at h
    · rename_i va l1 ha
      split at h
      · rename_i vb l2 hb
        obtain ⟨w, hv, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        simp only [evalRvalue, sPrim_sound x ha, sPrim_sound x hb,
          sBinOp_sound x hv]
      · cases h
    · cases h
  | discriminant p =>
    simp only [sRvalue] at h
    split at h
    · rename_i hp
      split at h
      · rename_i ety ety' n ht hs
        obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        simp only [sDiscr] at hd
        split at hd
        · rename_i tw ts htag
          split at hd
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            obtain ⟨hadm, hbeq, hlt⟩ := hc
            obtain ⟨disc, hg, hdisc⟩ := Option.map_eq_some_iff.mp hd
            cases hdisc
            simp only [evalRvalue, evalDiscriminantOfVal, hp, Bool.not_true,
              getElem?_map, ht, hs, Option.map, SSlot.slot, SVal.val, hadm,
              htag, hbeq, hlt, hg, Bool.and_self, Bool.false_eq_true,
              ↓reduceIte]
          · cases hd
        · cases hd
      · cases h
    · cases h
  | unaryOp | cast | ref | addressOf | aggregateTuple | useRetag
  | aggregateRangeTo | aggregateRangeFrom | unsupported => cases h

/-- Whether `writePlace` accepts this value at type `ty`. -/
noncomputable def SVal.check (ty : MirTy) : SVal → Bool
  | .conc v => checkVal v ty
  | .word _ => MirTy.beq (.int .i64 false) ty

theorem SVal.check_sound {v : SVal} {ty : MirTy} (x : Word)
    (h : v.check ty = true) : checkVal (v.val x) ty = true := by
  cases v with
  | conc c => exact h
  | word s =>
    have hty : MirTy.int .i64 false = ty := MirTy.beq_iff.mp h
    subst hty
    exact checkVal_u64_bvZeroExtend _

/-- Mirror of `writePlace`. -/
noncomputable def sWrite (ls : List SSlot) (dst : LocalId) (ty : MirTy)
    (v : SVal) : Option (List SSlot) :=
  if v.check ty then
    match Trusted.MirSemantics.getElem? ls dst with
    | some (.immediate _) => setElem? ls dst (.immediate (some v))
    | _ => none
  else none

theorem sWrite_sound {ls ls' : List SSlot} {dst : LocalId} {ty : MirTy}
    {v : SVal} (x : Word) (h : sWrite ls dst ty v = some ls') :
    writePlace (ls.map (SSlot.slot x)) entryMemory dst ty (v.val x) =
      .ok (ls'.map (SSlot.slot x), entryMemory) := by
  simp only [sWrite] at h
  split at h
  · rename_i hc
    split at h
    · rename_i o hs
      have hmap := setElem?_map (SSlot.slot x) ls dst (.immediate (some v))
      rw [h] at hmap
      simp only [SSlot.slot, Option.map] at hmap
      simp only [writePlace, SVal.check_sound x hc, Bool.not_true, getElem?_map,
        hs, Option.map, SSlot.slot, hmap, Bool.false_eq_true, ↓reduceIte]
    · cases h
  · cases h

/-! ### Statements, terminators and runs -/

/-- Whether a symbolic slot is not `.indirect` (so `deallocateLocal` is a
no-op). -/
def SSlot.isDirect : SSlot → Bool
  | .dead | .immediate _ => true
  | .indirect _ => false

theorem deallocateLocal_slot_of_isDirect {s : SSlot} (x : Word)
    (h : s.isDirect = true) :
    deallocateLocal entryMemory (s.slot x) = .ok entryMemory := by
  cases s with
  | dead | immediate _ => rfl
  | indirect _ => cases h

/-- Mirror of `evalStatement`. -/
noncomputable def sStatement (body : Body) (s : SState) : StatementKind → SRes
  | .nop => .step { s with stmt := s.stmt + 1 }
  | .storageLive l =>
    match Trusted.MirSemantics.getElem? body.locals l,
        Trusted.MirSemantics.getElem? s.slots l with
    | some ty, some old =>
      if old.isDirect then
        match setElem? s.slots l (SSlot.ofSlot (liveUninitSlot ty)) with
        | some ls => .step { s with stmt := s.stmt + 1, slots := ls }
        | none => .stuck
      else .stuck
    | _, _ => .stuck
  | .storageDead l =>
    if Nat.beq l 0 then .stuck else
      match Trusted.MirSemantics.getElem? s.slots l with
      | some old =>
        if old.isDirect then
          match setElem? s.slots l .dead with
          | some ls => .step { s with stmt := s.stmt + 1, slots := ls }
          | none => .stuck
        else .stuck
      | none => .stuck
  | .assign dst rv =>
    if dst.projection.isEmpty then
      match Trusted.MirSemantics.getElem? body.locals dst.localId with
      | some ty =>
        match sRvalue body.locals s.slots ty rv with
        | some (v, l1) =>
          match sWrite l1 dst.localId ty v with
          | some l2 => .step { s with stmt := s.stmt + 1, slots := l2 }
          | none => .stuck
        | none => .stuck
      | none => .stuck
    else .stuck
  | .unsupported => .stuck

theorem sStatement_sound {body : Body} {s s' : SState} {stmt : StatementKind}
    (x : Word) (h : sStatement body s stmt = .step s') :
    evalStatement body (s.frame x) entryMemory ⟨[]⟩ stmt =
      .step (s'.state x) := by
  cases stmt with
  | nop =>
    cases h
    rfl
  | storageLive l =>
    simp only [sStatement] at h
    split at h
    · rename_i ty old ht hold
      split at h
      · rename_i hdir
        have hmap := setElem?_map (SSlot.slot x) s.slots l
          (SSlot.ofSlot (liveUninitSlot ty))
        rw [SSlot.slot_ofSlot] at hmap
        split at h
        · rename_i l1 hset
          rw [hset] at hmap
          cases h
          simp only [evalStatement, ht, SState.frame, getElem?_map, hold,
            Option.map, hmap, deallocateLocal_slot_of_isDirect x hdir]
          rfl
        · cases h
      · cases h
    · cases h
  | storageDead l =>
    simp only [sStatement] at h
    split at h
    · cases h
    · rename_i hl
      split at h
      · rename_i old hold
        split at h
        · rename_i hdir
          split at h
          · rename_i l1 hset
            have hmap := setElem?_map (SSlot.slot x) s.slots l .dead
            rw [hset] at hmap
            simp only [SSlot.slot] at hmap
            cases h
            simp only [evalStatement, hl, SState.frame, getElem?_map, hold,
              Option.map, hmap, deallocateLocal_slot_of_isDirect x hdir,
              Bool.false_eq_true, ↓reduceIte]
            rfl
          · cases h
        · cases h
      · cases h
  | assign dst rv =>
    simp only [sStatement] at h
    split at h
    · rename_i hp
      split at h
      · rename_i ty ht
        split at h
        · rename_i v l1 hr
          split at h
          · rename_i l2 hw
            cases h
            simp only [evalStatement, hp, Bool.not_true, ht, SState.frame,
              sRvalue_sound x hr, sWrite_sound x hw, Bool.false_eq_true,
              ↓reduceIte]
            rfl
          · cases h
        · cases h
      · cases h
    · cases h
  | unsupported => cases h

theorem sStatement_ne_ret {body : Body} {s : SState} {stmt : StatementKind}
    {v : SVal} : sStatement body s stmt ≠ .ret v := by
  intro h
  cases stmt with
  | nop => cases h
  | storageLive l =>
    simp only [sStatement] at h
    split at h <;> (try split at h) <;> (try split at h) <;> cases h
  | storageDead l =>
    simp only [sStatement] at h
    split at h <;> (try split at h) <;> (try split at h) <;>
      (try split at h) <;> cases h
  | assign dst rv =>
    simp only [sStatement] at h
    split at h <;> (try split at h) <;> (try split at h) <;>
      (try split at h) <;> cases h
  | unsupported => cases h

/-- Mirror of `evalTerminator`; switches need concrete operands. -/
noncomputable def sTerminator (body : Body) (bb : BasicBlock) (s : SState) :
    SRes :=
  match bb.terminator with
  | .goto t => .step { s with block := t, stmt := 0 }
  | .return_ =>
    if bb.cleanup then .stuck else
      match Trusted.MirSemantics.getElem? s.slots 0 with
      | some (.immediate (some v)) => .ret v
      | _ => .stuck
  | .switchInt d targets =>
    match sPrim body.locals s.slots d with
    | some (.conc (.scalar sv), ls) =>
      match evalSwitchBranches sv.width sv.bits targets.otherwise
          targets.branches with
      | .ok t => .step { block := t, stmt := 0, slots := ls }
      | .error _ => .stuck
    | some (.conc (.bool b), ls) =>
      match evalBoolSwitchBranches b targets.otherwise targets.branches with
      | .ok t => .step { block := t, stmt := 0, slots := ls }
      | .error _ => .stuck
    | _ => .stuck
  | _ => .stuck

theorem sTerminator_step {body : Body} {bb : BasicBlock} {s s' : SState}
    (x : Word) (h : sTerminator body bb s = .step s') :
    evalTerminator body bb (s.frame x) entryMemory ⟨[]⟩ =
      .step (s'.state x) := by
  simp only [sTerminator] at h
  split at h
  · rename_i t hterm
    cases h
    simp only [evalTerminator, hterm, jumpToBlock, SState.frame]
    rfl
  · split at h
    · cases h
    · split at h <;> cases h
  · rename_i d targets hterm
    split at h
    · rename_i sv ls hd
      split at h
      · rename_i t ht
        cases h
        simp only [evalTerminator, hterm, SState.frame, sPrim_sound x hd,
          SVal.val, ht, jumpToBlock]
        rfl
      · cases h
    · rename_i b ls hd
      split at h
      · rename_i t ht
        cases h
        simp only [evalTerminator, hterm, SState.frame, sPrim_sound x hd,
          SVal.val, ht, jumpToBlock]
        rfl
      · cases h
    · cases h
  · cases h

theorem sTerminator_ret {body : Body} {bb : BasicBlock} {s : SState}
    {v : SVal} (x : Word) (h : sTerminator body bb s = .ret v) :
    evalTerminator body bb (s.frame x) entryMemory ⟨[]⟩ =
      .done (.returned ⟨v.val x, ⟨[]⟩⟩) := by
  simp only [sTerminator] at h
  split at h
  · cases h
  · rename_i hterm
    split at h
    · cases h
    · rename_i hcl
      split at h
      · rename_i v0 hs
        cases h
        simp only [evalTerminator, hterm, hcl, SState.frame, getElem?_map, hs,
          Option.map, SSlot.slot, Bool.false_eq_true, ↓reduceIte]
      · cases h
  · split at h
    · split at h <;> cases h
    · split at h <;> cases h
    · cases h
  · cases h

/-- Mirror of `evalStep` for the single frame of `bodyProg body`. -/
noncomputable def sStep (body : Body) (s : SState) : SRes :=
  match Trusted.MirSemantics.getElem? body.basicBlocks s.block with
  | some bb =>
    match Trusted.MirSemantics.getElem? bb.statements s.stmt with
    | some stmt => sStatement body s stmt
    | none =>
      if Nat.beq s.stmt bb.statements.length then sTerminator body bb s
      else .stuck
  | none => .stuck

theorem evalStep_state (body : Body) (x : Word) (s : SState) :
    evalStep (bodyProg body) 0 (s.state x) =
      match Trusted.MirSemantics.getElem? body.basicBlocks s.block with
      | none => .fault .unsupported
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements s.stmt with
        | some stmt => evalStatement body (s.frame x) entryMemory ⟨[]⟩ stmt
        | none =>
          if Nat.beq s.stmt bb.statements.length then
            evalTerminator body bb (s.frame x) entryMemory ⟨[]⟩
          else .fault .unsupported :=
  rfl

theorem sStep_step {body : Body} {s s' : SState} (x : Word)
    (h : sStep body s = .step s') :
    evalStep (bodyProg body) 0 (s.state x) = .step (s'.state x) := by
  rw [evalStep_state]
  simp only [sStep] at h
  split at h
  · rename_i bb hb
    rw [hb]
    split at h
    · rename_i stmt hst
      simp only [hst]
      exact sStatement_sound x h
    · rename_i hst
      simp only [hst]
      split at h
      · rename_i hn
        simp only [hn, ↓reduceIte]
        exact sTerminator_step x h
      · cases h
  · cases h

theorem sStep_ret {body : Body} {s : SState} {v : SVal} (x : Word)
    (h : sStep body s = .ret v) :
    evalStep (bodyProg body) 0 (s.state x) =
      .done (.returned ⟨v.val x, ⟨[]⟩⟩) := by
  rw [evalStep_state]
  simp only [sStep] at h
  split at h
  · rename_i bb hb
    rw [hb]
    split at h
    · exact absurd h sStatement_ne_ret
    · rename_i hst
      simp only [hst]
      split at h
      · rename_i hn
        simp only [hn, ↓reduceIte]
        exact sTerminator_ret x h
      · cases h
  · cases h

/-- Fuel-bounded symbolic run; `none` unless the body returns in time. -/
noncomputable def symRun (body : Body) : Nat → SState → Option SVal
  | 0, _ => none
  | fuel + 1, s =>
    match sStep body s with
    | .step s' => symRun body fuel s'
    | .ret v => some v
    | .stuck => none

theorem symRun_sound {body : Body} (x : Word) :
    ∀ {fuel : Nat} {s : SState} {v : SVal}, symRun body fuel s = some v →
      Executes body (s.state x) (v.val x)
  | 0, _, _, h => by cases h
  | fuel + 1, s, v, h => by
    simp only [symRun] at h
    split at h
    · rename_i s' hs
      exact .next (sStep_step x hs) (symRun_sound x h)
    · rename_i v' hs
      cases h
      exact .ret (sStep_ret x hs)
    · cases h

/-! ### Entry states -/

/-- Mirror of `initLocalsLoop` over symbolic arguments. -/
noncomputable def sInit (body : Body) (args : List SVal) :
    Nat → List MirTy → List SSlot
  | _, [] => []
  | idx, ty :: rest =>
    (if Nat.beq idx 0 then SSlot.ofSlot (liveUninitSlot ty)
      else if Nat.ble idx body.argumentCount then
        match Trusted.MirSemantics.getElem? args (idx - 1) with
        | some v => .immediate (some v)
        | none => .dead
      else if hasStorageAnnotation body idx then .dead
      else SSlot.ofSlot (liveUninitSlot ty)) :: sInit body args (idx + 1) rest

theorem sInit_map (body : Body) (args : List SVal) (x : Word) :
    ∀ (idx : Nat) (tys : List MirTy),
      (sInit body args idx tys).map (SSlot.slot x) =
        initLocalsLoop body (args.map (SVal.val x)) idx tys
  | _, [] => rfl
  | idx, ty :: rest => by
    simp only [sInit, initLocalsLoop, List.map]
    rw [sInit_map body args x (idx + 1) rest]
    congr 1
    cases Nat.beq idx 0
    · cases Nat.ble idx body.argumentCount
      · cases hasStorageAnnotation body idx
        · exact SSlot.slot_ofSlot x _
        · rfl
      · simp only [getElem?_map]
        cases Trusted.MirSemantics.getElem? args (idx - 1) <;> rfl
    · exact SSlot.slot_ofSlot x _

/-- The entry state on symbolic arguments. -/
noncomputable def sEntry (body : Body) (args : List SVal) : SState :=
  ⟨0, 0, sInit body args 0 body.locals⟩

/-- A symbolic run from the entry state yields a safe actual return for
every input word. -/
theorem symRun_entry {body : Body} {args : List SVal} {fuel : Nat} {v : SVal}
    (x : Word) (h : symRun body fuel (sEntry body args) = some v) :
    Safe body (args.map (SVal.val x)) ∧
      Returns body (args.map (SVal.val x)) (v.val x) := by
  have e := symRun_sound x h
  have hs : (sEntry body args).state x =
      mkState 0 0
        (initLocalsLoop body (args.map (SVal.val x)) 0 body.locals) := by
    show mkState 0 0 ((sInit body args 0 body.locals).map (SSlot.slot x)) = _
    rw [sInit_map]
  rw [hs] at e
  exact ⟨executes_safe e, executes_returns e⟩

/-! ### Bit-level meaning of word expressions

Each result bit is checked against an expected source by kernel evaluation,
so results are compared semantically rather than by expression shape. -/

/-- Where one result bit comes from. -/
inductive BitSrc where
  | zero
  | one
  | input (j : Nat)
  | unknown

/-- Equality of known bit sources; `unknown` matches nothing. -/
def BitSrc.beq : BitSrc → BitSrc → Bool
  | .zero, .zero => true
  | .one, .one => true
  | .input i, .input j => Nat.beq i j
  | _, _ => false

/-- Bit `b` agrees with this source when the input is `x`. -/
def BitSrc.Agrees (x : Word) (b : Bool) : BitSrc → Prop
  | .zero => b = false
  | .one => b = true
  | .input j => b = x.getLsbD j
  | .unknown => True

/-- The source of a conjunction of two bits. -/
def BitSrc.and : BitSrc → BitSrc → BitSrc
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, b => b
  | a, .one => a
  | .input i, .input j => if Nat.beq i j then .input i else .unknown
  | _, _ => .unknown

/-- The source of a disjunction of two bits. -/
def BitSrc.or : BitSrc → BitSrc → BitSrc
  | .one, _ => .one
  | _, .one => .one
  | .zero, b => b
  | a, .zero => a
  | .input i, .input j => if Nat.beq i j then .input i else .unknown
  | _, _ => .unknown

theorem BitSrc.and_sound {x : Word} {a b : BitSrc} {p q : Bool}
    (ha : a.Agrees x p) (hb : b.Agrees x q) : (a.and b).Agrees x (p && q) := by
  cases a <;> cases b <;> simp only [BitSrc.Agrees] at ha hb <;>
    simp only [BitSrc.and, BitSrc.Agrees, ha, hb, Bool.false_and,
      Bool.and_false, Bool.true_and, Bool.and_true]
  rename_i i j
  cases hij : Nat.beq i j
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte]
    rw [Nat.eq_of_beq_eq_true hij, Bool.and_self]

theorem BitSrc.or_sound {x : Word} {a b : BitSrc} {p q : Bool}
    (ha : a.Agrees x p) (hb : b.Agrees x q) : (a.or b).Agrees x (p || q) := by
  cases a <;> cases b <;> simp only [BitSrc.Agrees] at ha hb <;>
    simp only [BitSrc.or, BitSrc.Agrees, ha, hb, Bool.true_or, Bool.or_true,
      Bool.false_or, Bool.or_false]
  rename_i i j
  cases hij : Nat.beq i j
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte]
    rw [Nat.eq_of_beq_eq_true hij, Bool.or_self]

theorem BitSrc.agrees_of_beq {x : Word} {a e : BitSrc} {b : Bool}
    (h : a.beq e = true) (ha : a.Agrees x b) : e.Agrees x b := by
  cases a <;> cases e <;> simp only [BitSrc.beq] at h <;>
    first | exact ha | cases h | skip
  rename_i i j
  rw [← Nat.eq_of_beq_eq_true h]
  exact ha

/-- The source of bit `i` of an expression's word. -/
def Sym.bit : Sym → Nat → BitSrc
  | .input, i => if i < 64 then .input i else .zero
  | .lit w, i => if w.getLsbD i then .one else .zero
  | .and l r, i => (l.bit i).and (r.bit i)
  | .or l r, i => (l.bit i).or (r.bit i)
  | .shl l k, i => if i < 64 ∧ k ≤ i then l.bit (i - k) else .zero
  | .shr l k, i => l.bit (k + i)

theorem Sym.bit_sound (x : Word) :
    ∀ (s : Sym) (i : Nat), (s.bit i).Agrees x ((s.eval x).getLsbD i)
  | .input, i => by
    by_cases h : i < 64
    · simp only [Sym.bit, Sym.eval, h, ↓reduceIte, BitSrc.Agrees]
    · simp only [Sym.bit, Sym.eval, h, ↓reduceIte, BitSrc.Agrees]
      exact BitVec.getLsbD_of_ge x i (Nat.le_of_not_gt h)
  | .lit w, i => by
    cases hw : w.getLsbD i <;>
      simp only [Sym.bit, Sym.eval, hw, Bool.false_eq_true, ↓reduceIte,
        BitSrc.Agrees]
  | .and l r, i => by
    simp only [Sym.bit, Sym.eval, BitVec.getLsbD_and]
    exact BitSrc.and_sound (Sym.bit_sound x l i) (Sym.bit_sound x r i)
  | .or l r, i => by
    simp only [Sym.bit, Sym.eval, BitVec.getLsbD_or]
    exact BitSrc.or_sound (Sym.bit_sound x l i) (Sym.bit_sound x r i)
  | .shl l k, i => by
    simp only [Sym.bit, Sym.eval, BitVec.getLsbD_shiftLeft]
    by_cases h : i < 64 ∧ k ≤ i
    · have hk : ¬ i < k := Nat.not_lt.mpr h.2
      simp only [h, hk, and_self, ↓reduceIte, decide_true, decide_false,
        Bool.not_false, Bool.true_and]
      exact Sym.bit_sound x l (i - k)
    · simp only [h, ↓reduceIte, BitSrc.Agrees]
      by_cases hi : i < 64
      · have hk : i < k := Nat.lt_of_not_le (fun hk => h ⟨hi, hk⟩)
        simp only [hk, decide_true, Bool.not_true, Bool.and_false,
          Bool.false_and]
      · simp only [hi, decide_false, Bool.false_and]
  | .shr l k, i => by
    simp only [Sym.bit, Sym.eval, BitVec.getLsbD_ushiftRight]
    exact Sym.bit_sound x l (k + i)

/-- `true` when `p i` holds for every `i < n`. -/
def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allBelow n p && p n

theorem allBelow_sound {p : Nat → Bool} :
    ∀ {n : Nat}, allBelow n p = true → ∀ i, i < n → p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    simp only [allBelow, Bool.and_eq_true] at h
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with
    | inl hlt => exact allBelow_sound h.1 i hlt
    | inr heq =>
      subst heq
      exact h.2

/-- Every bit below 64 of the word has its expected source. -/
def Sym.bitsAre (s : Sym) (expect : Nat → BitSrc) : Bool :=
  allBelow 64 fun i => (s.bit i).beq (expect i)

theorem Sym.bitsAre_sound {s : Sym} {expect : Nat → BitSrc}
    (h : s.bitsAre expect = true) (x : Word) (i : Nat) (hi : i < 64) :
    (expect i).Agrees x ((s.eval x).getLsbD i) :=
  BitSrc.agrees_of_beq (allBelow_sound h i hi) (Sym.bit_sound x s i)

end SymExec

end
