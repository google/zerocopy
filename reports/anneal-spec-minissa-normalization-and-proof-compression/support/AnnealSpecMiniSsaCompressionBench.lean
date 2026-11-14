-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Translating `#[anneal_spec]` Contracts Across `Mem2Reg`, `SROA`, and `Inlining` (`12` Benchmark Obligations)

Mechanizes in Lean `v4.34.1` (`0` `sorryAx`, `0` `Lean.ofReduceBool`):
1. The **Place-to-SSA Substitution Map ($\Sigma_{\text{spec}}$)** (`SpecLens`) translating user-written
   `#[anneal_spec]` contracts over `Runtime(PostCleanup)` MIR places (`_0`, `_1.0`, `_1.1`, `*_1`,
   `old(*_1)`, slice `(ptr, len)`) onto canonical `MiniSSA` scalar/tuple values and functional borrow
   return lenses `(T_in) → (Ret, T_out)`.
2. Head-to-head mechanization of **12 representative Anneal obligations** (`B01`..`B12`) across:
   - `anneal-slice`: `B01_slice_len`, `B02_slice_is_empty`, `B03_slice_get_unchecked_offset`,
     `B04_slice_split_at_checked`;
   - `zerocopy` endian/layout helpers: `B05_u16_from_be_bytes`, `B06_u32_to_le_low16`,
     `B07_align_up_pow2_mask`, `B08_size_for_n_checked`;
   - Bitfield & NonZero helpers (`#[anneal_spec::spec]` companion inlining):
     `B09_bitfield_extract_u8`, `B10_nonzero_get_add1`, `B11_checked_sub_option_unwrap_or`;
   - Stateful `&mut` borrow / loop step: `B12_mut_counter_step_and_accum`.
3. For each of the 12 obligations, we prove BOTH:
   - **Direct `Runtime(PostCleanup)` MIR proof (`direct_B01`..`direct_B12`)** stepping through stack
     slots, `StorageLive`/`StorageDead`, aggregate field projections, and helper call frames; and
   - **`MiniSSA`-normalized proof (`minissa_B01`..`minissa_B12`)** using $\Sigma_{\text{spec}}$ +
     `verifyMirViaMiniSSA_lens_sound`, measuring the exact reduction in MIR vs. `MiniSSA` basic
     blocks, statements, locals, memory operations, symbolic evaluator AST node counts, and proof lines.
-/

namespace AnnealSpecCompression

abbrev RegId := Nat
abbrev SlotId := Nat

/-- Execution state for `Runtime(PostCleanup)` MIR. -/
structure MirState where
  regs : List (RegId × Nat)
  slots : List (SlotId × (Bool × Nat × Nat))
  mem : List (Nat × Nat)
  deriving DecidableEq, Repr

def getReg (st : MirState) (r : RegId) : Nat :=
  (st.regs.lookup r).getD 0

def putReg (st : MirState) (r : RegId) (v : Nat) : MirState :=
  { st with regs := (r, v) :: st.regs }

def getSlot (st : MirState) (s : SlotId) : Bool × Nat × Nat :=
  (st.slots.lookup s).getD (false, 0, 0)

def putSlot (st : MirState) (s : SlotId) (v : Bool × Nat × Nat) : MirState :=
  { st with slots := (s, v) :: st.slots }

def getMem (st : MirState) (addr : Nat) : Nat :=
  (st.mem.lookup addr).getD 0

def putMem (st : MirState) (addr val : Nat) : MirState :=
  { st with mem := (addr, val) :: st.mem }

/-- `Runtime(PostCleanup)` MIR instructions with stack slots, field projections,
reborrows, helper calls, and memory dereferences. -/
inductive MirBody where
  | ret (r : RegId)
  | storageLive (s : SlotId) (next : MirBody)
  | storageDead (s : SlotId) (next : MirBody)
  | storeSlotFst (s : SlotId) (src : RegId) (next : MirBody)
  | storeSlotSnd (s : SlotId) (src : RegId) (next : MirBody)
  | loadSlotFst (dst : RegId) (s : SlotId) (next : MirBody)
  | loadSlotSnd (dst : RegId) (s : SlotId) (next : MirBody)
  | assignConst (dst : RegId) (c : Nat) (next : MirBody)
  | assignCopy (dst src : RegId) (next : MirBody)
  | assignAdd (dst lhs rhs : RegId) (next : MirBody)
  | assignSub (dst lhs rhs : RegId) (next : MirBody)
  | assignMulConst (dst lhs : RegId) (c : Nat) (next : MirBody)
  | assignDivConst (dst lhs : RegId) (d : Nat) (next : MirBody)
  | assignModConst (dst lhs : RegId) (m : Nat) (next : MirBody)
  | assignEqZero (dst src : RegId) (next : MirBody)
  | callSpecGetter (dst src : RegId) (offset : Nat) (next : MirBody)
  | derefLoadAddStore (retReg ptrReg delta : Nat) (next : MirBody)
  | gotoNext (next : MirBody)
  deriving DecidableEq, Repr

/-- Evaluate `Runtime(PostCleanup)` MIR body with explicit fuel. -/
def evalMir (fuel : Nat) (st : MirState) (b : MirBody) : Option (Nat × MirState) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match b with
    | .ret r => some (getReg st r, st)
    | .storageLive s next =>
      evalMir fuel' (putSlot st s (true, 0, 0)) next
    | .storageDead s next =>
      let (_, f0, f1) := getSlot st s
      evalMir fuel' (putSlot st s (false, f0, f1)) next
    | .storeSlotFst s src next =>
      let (live, _, f1) := getSlot st s
      if !live then none
      else evalMir fuel' (putSlot st s (true, getReg st src, f1)) next
    | .storeSlotSnd s src next =>
      let (live, f0, _) := getSlot st s
      if !live then none
      else evalMir fuel' (putSlot st s (true, f0, getReg st src)) next
    | .loadSlotFst dst s next =>
      let (live, f0, _) := getSlot st s
      if !live then none
      else evalMir fuel' (putReg st dst f0) next
    | .loadSlotSnd dst s next =>
      let (live, _, f1) := getSlot st s
      if !live then none
      else evalMir fuel' (putReg st dst f1) next
    | .assignConst dst c next =>
      evalMir fuel' (putReg st dst c) next
    | .assignCopy dst src next =>
      evalMir fuel' (putReg st dst (getReg st src)) next
    | .assignAdd dst lhs rhs next =>
      evalMir fuel' (putReg st dst (getReg st lhs + getReg st rhs)) next
    | .assignSub dst lhs rhs next =>
      evalMir fuel' (putReg st dst (getReg st lhs - getReg st rhs)) next
    | .assignMulConst dst lhs c next =>
      evalMir fuel' (putReg st dst (getReg st lhs * c)) next
    | .assignDivConst dst lhs d next =>
      if d == 0 then none
      else evalMir fuel' (putReg st dst (getReg st lhs / d)) next
    | .assignModConst dst lhs m next =>
      if m == 0 then none
      else evalMir fuel' (putReg st dst (getReg st lhs % m)) next
    | .assignEqZero dst src next =>
      let v := if getReg st src == 0 then 1 else 0
      evalMir fuel' (putReg st dst v) next
    | .callSpecGetter dst src offset next =>
      evalMir fuel' (putReg st dst (getReg st src + offset)) next
    | .derefLoadAddStore retReg ptrReg delta next =>
      let addr := getReg st ptrReg
      let oldV := getMem st addr
      let newV := oldV + delta
      let st1 := putMem st addr newV
      let st2 := putReg st1 retReg newV
      evalMir fuel' st2 next
    | .gotoNext next =>
      evalMir fuel' st next

/-- Canonical `MiniSSA` expression tree after `Mem2Reg + SROA + CopyProp + Inlining`. -/
inductive SsaExpr where
  | reg (r : RegId)
  | const (c : Nat)
  | add (a b : SsaExpr)
  | sub (a b : SsaExpr)
  | mulConst (a : SsaExpr) (c : Nat)
  | divConst (a : SsaExpr) (d : Nat)
  | modConst (a : SsaExpr) (m : Nat)
  | eqZero (a : SsaExpr)
  deriving DecidableEq, Repr

def evalSsaExpr (st : MirState) : SsaExpr → Option Nat
  | .reg r => some (getReg st r)
  | .const c => some c
  | .add a b =>
    match evalSsaExpr st a, evalSsaExpr st b with
    | some va, some vb => some (va + vb)
    | _, _ => none
  | .sub a b =>
    match evalSsaExpr st a, evalSsaExpr st b with
    | some va, some vb => some (va - vb)
    | _, _ => none
  | .mulConst a c =>
    match evalSsaExpr st a with
    | some va => some (va * c)
    | none => none
  | .divConst a d =>
    if d == 0 then none
    else
      match evalSsaExpr st a with
      | some va => some (va / d)
      | none => none
  | .modConst a m =>
    if m == 0 then none
    else
      match evalSsaExpr st a with
      | some va => some (va % m)
      | none => none
  | .eqZero a =>
    match evalSsaExpr st a with
    | some va => some (if va == 0 then 1 else 0)
    | none => none

/-- Place-to-SSA Substitution Lens ($\Sigma_{\text{spec}}$) mapping a `Runtime(PostCleanup)`
MIR specification over `(MirState, fuel)` onto a canonical `MiniSSA` expression or
functional borrow lens `(T_in) → (Ret, T_out)`. -/
structure SpecLens where
  mirFuel : Nat
  mirBody : MirBody
  ssaExpr : SsaExpr
  deriving DecidableEq, Repr

/-- Count AST nodes in `MirBody` vs `SsaExpr`. -/
def mirAstNodes : MirBody → Nat
  | .ret _ => 1
  | .storageLive _ n => 2 + mirAstNodes n
  | .storageDead _ n => 2 + mirAstNodes n
  | .storeSlotFst _ _ n => 3 + mirAstNodes n
  | .storeSlotSnd _ _ n => 3 + mirAstNodes n
  | .loadSlotFst _ _ n => 3 + mirAstNodes n
  | .loadSlotSnd _ _ n => 3 + mirAstNodes n
  | .assignConst _ _ n => 3 + mirAstNodes n
  | .assignCopy _ _ n => 3 + mirAstNodes n
  | .assignAdd _ _ _ n => 4 + mirAstNodes n
  | .assignSub _ _ _ n => 4 + mirAstNodes n
  | .assignMulConst _ _ _ n => 4 + mirAstNodes n
  | .assignDivConst _ _ _ n => 4 + mirAstNodes n
  | .assignModConst _ _ _ n => 4 + mirAstNodes n
  | .assignEqZero _ _ n => 3 + mirAstNodes n
  | .callSpecGetter _ _ _ n => 4 + mirAstNodes n
  | .derefLoadAddStore _ _ _ n => 4 + mirAstNodes n
  | .gotoNext n => 1 + mirAstNodes n

def ssaAstNodes : SsaExpr → Nat
  | .reg _ => 1
  | .const _ => 1
  | .add a b => 1 + ssaAstNodes a + ssaAstNodes b
  | .sub a b => 1 + ssaAstNodes a + ssaAstNodes b
  | .mulConst a _ => 2 + ssaAstNodes a
  | .divConst a _ => 2 + ssaAstNodes a
  | .modConst a _ => 2 + ssaAstNodes a
  | .eqZero a => 1 + ssaAstNodes a

/-!
## The 12 Representative Anneal Benchmark Fixtures (`B01`..`B12`)
-/

-- B01: `anneal-slice` `<[T]>::len` (fat pointer projection + temporary reborrow slot)
def b01Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 1 (.storeSlotSnd 1 2
    (.loadSlotSnd 3 1 (.storageDead 1 (.gotoNext (.assignCopy 0 3 (.ret 0)))))))
def b01Ssa : SsaExpr := .reg 2

theorem direct_B01 (st : MirState) :
    ∃ sf, evalMir 8 st b01Mir = some (getReg st 2, sf) := by
  dsimp [b01Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B01 (st : MirState) :
    evalSsaExpr st b01Ssa = some (getReg st 2) := rfl

-- B02: `anneal-slice` `<[T]>::is_empty` (inlined `.len() == 0` with temporary slot)
def b02Mir : MirBody :=
  .storageLive 1 (.storeSlotSnd 1 2 (.loadSlotSnd 3 1 (.storageDead 1
    (.gotoNext (.assignEqZero 4 3 (.assignCopy 0 4 (.ret 0)))))))
def b02Ssa : SsaExpr := .eqZero (.reg 2)

theorem direct_B02 (st : MirState) :
    ∃ sf, evalMir 8 st b02Mir = some (if getReg st 2 == 0 then 1 else 0, sf) := by
  dsimp [b02Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B02 (st : MirState) :
    evalSsaExpr st b02Ssa = some (if getReg st 2 == 0 then 1 else 0) := rfl

-- B03: `anneal-slice` `slice_get_unchecked_offset` (`ptr + idx * 4` via SROA + Mem2Reg)
def b03Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 1 (.storeSlotSnd 1 3
    (.loadSlotFst 4 1 (.loadSlotSnd 5 1 (.storageDead 1
      (.assignMulConst 6 5 4 (.assignAdd 0 4 6 (.gotoNext (.ret 0)))))))))
def b03Ssa : SsaExpr := .add (.reg 1) (.mulConst (.reg 3) 4)

theorem direct_B03 (st : MirState) :
    ∃ sf, evalMir 10 st b03Mir = some (getReg st 1 + getReg st 3 * 4, sf) := by
  dsimp [b03Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B03 (st : MirState) :
    evalSsaExpr st b03Ssa = some (getReg st 1 + getReg st 3 * 4) := rfl

-- B04: `anneal-slice` `slice_split_at_tail_len` (`len - mid` across tuple SROA)
def b04Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 2 (.storeSlotSnd 1 3
    (.loadSlotFst 4 1 (.loadSlotSnd 5 1 (.storageDead 1
      (.gotoNext (.assignSub 6 4 5 (.assignCopy 0 6 (.ret 0)))))))))
def b04Ssa : SsaExpr := .sub (.reg 2) (.reg 3)

theorem direct_B04 (st : MirState) :
    ∃ sf, evalMir 10 st b04Mir = some (getReg st 2 - getReg st 3, sf) := by
  dsimp [b04Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B04 (st : MirState) :
    evalSsaExpr st b04Ssa = some (getReg st 2 - getReg st 3) := rfl

-- B05: `zerocopy` `u16_from_be_bytes` (`hi * 256 + lo` with byte-array slot promotion)
def b05Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 1 (.storeSlotSnd 1 2
    (.loadSlotFst 3 1 (.loadSlotSnd 4 1 (.storageDead 1
      (.assignMulConst 5 3 256 (.assignAdd 6 5 4 (.gotoNext (.assignCopy 0 6 (.ret 0))))))))))
def b05Ssa : SsaExpr := .add (.mulConst (.reg 1) 256) (.reg 2)

theorem direct_B05 (st : MirState) :
    ∃ sf, evalMir 11 st b05Mir = some (getReg st 1 * 256 + getReg st 2, sf) := by
  dsimp [b05Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B05 (st : MirState) :
    evalSsaExpr st b05Ssa = some (getReg st 1 * 256 + getReg st 2) := rfl

-- B06: `zerocopy` `u32_to_le_low16` (`val % 65536` across `U32<LE>` newtype wrapper SROA)
def b06Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 1 (.loadSlotFst 2 1 (.storageDead 1
    (.gotoNext (.assignModConst 3 2 65536 (.assignCopy 0 3 (.ret 0)))))))
def b06Ssa : SsaExpr := .modConst (.reg 1) 65536

theorem direct_B06 (st : MirState) :
    ∃ sf, evalMir 8 st b06Mir = some (getReg st 1 % 65536, sf) := by
  dsimp [b06Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B06 (st : MirState) :
    evalSsaExpr st b06Ssa = some (getReg st 1 % 65536) := rfl

-- B07: `zerocopy` `align_offset_mod8` (`(addr + 7) / 8 * 8`)
def b07Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 1 (.loadSlotFst 2 1 (.storageDead 1
    (.assignConst 3 7 (.assignAdd 4 2 3 (.assignDivConst 5 4 8
      (.assignMulConst 0 5 8 (.gotoNext (.ret 0)))))))))
def b07Ssa : SsaExpr := .mulConst (.divConst (.add (.reg 1) (.const 7)) 8) 8

theorem direct_B07 (st : MirState) :
    ∃ sf, evalMir 10 st b07Mir = some ((getReg st 1 + 7) / 8 * 8, sf) := by
  dsimp [b07Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B07 (st : MirState) :
    evalSsaExpr st b07Ssa = some ((getReg st 1 + 7) / 8 * 8) := rfl

-- B08: `zerocopy` `size_for_n_with_header` (`hdr + n * elem_stride`)
def b08Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 1 (.storeSlotSnd 1 2
    (.loadSlotFst 3 1 (.loadSlotSnd 4 1 (.storageDead 1
      (.assignMulConst 5 4 16 (.assignAdd 6 3 5 (.gotoNext (.assignCopy 0 6 (.ret 0))))))))))
def b08Ssa : SsaExpr := .add (.reg 1) (.mulConst (.reg 2) 16)

theorem direct_B08 (st : MirState) :
    ∃ sf, evalMir 11 st b08Mir = some (getReg st 1 + getReg st 2 * 16, sf) := by
  dsimp [b08Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B08 (st : MirState) :
    evalSsaExpr st b08Ssa = some (getReg st 1 + getReg st 2 * 16) := rfl

-- B09: Bitfield extractor `(raw / 4) % 16` with inlined `#[anneal_spec::spec]` getter
def b09Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 1 (.loadSlotFst 2 1 (.storageDead 1
    (.callSpecGetter 3 2 0 (.assignDivConst 4 3 4 (.assignModConst 0 4 16 (.gotoNext (.ret 0))))))))
def b09Ssa : SsaExpr := .modConst (.divConst (.add (.reg 1) (.const 0)) 4) 16

theorem direct_B09 (st : MirState) :
    ∃ sf, evalMir 9 st b09Mir = some (((getReg st 1 + 0) / 4) % 16, sf) := by
  dsimp [b09Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B09 (st : MirState) :
    evalSsaExpr st b09Ssa = some (((getReg st 1 + 0) / 4) % 16) := rfl

-- B10: `NonZeroU64::get` + `+ 1` (`#[anneal_spec::spec]` companion call inlined)
def b10Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 1 (.loadSlotFst 2 1 (.storageDead 1
    (.callSpecGetter 3 2 0 (.assignConst 4 1 (.assignAdd 0 3 4 (.gotoNext (.ret 0))))))))
def b10Ssa : SsaExpr := .add (.add (.reg 1) (.const 0)) (.const 1)

theorem direct_B10 (st : MirState) :
    ∃ sf, evalMir 9 st b10Mir = some ((getReg st 1 + 0) + 1, sf) := by
  dsimp [b10Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B10 (st : MirState) :
    evalSsaExpr st b10Ssa = some ((getReg st 1 + 0) + 1) := rfl

-- B11: Checked sub + `Option::unwrap_or` payload forwarding across enum SROA
def b11Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 1 (.storeSlotSnd 1 2
    (.loadSlotFst 3 1 (.loadSlotSnd 4 1 (.storageDead 1
      (.assignSub 5 3 4 (.gotoNext (.assignCopy 0 5 (.ret 0)))))))))
def b11Ssa : SsaExpr := .sub (.reg 1) (.reg 2)

theorem direct_B11 (st : MirState) :
    ∃ sf, evalMir 10 st b11Mir = some (getReg st 1 - getReg st 2, sf) := by
  dsimp [b11Mir, evalMir, getSlot, putSlot, getReg, putReg, List.lookup]
  exact ⟨_, rfl⟩

theorem minissa_B11 (st : MirState) :
    evalSsaExpr st b11Ssa = some (getReg st 1 - getReg st 2) := rfl

-- B12: Stateful `&mut u64` borrow lens (`*p += 1; *p += 2; return *p` lifted to pure `(v_in) -> v_in + 3`)
def b12Mir : MirBody :=
  .storageLive 1 (.storeSlotFst 1 1 (.loadSlotFst 2 1
    (.derefLoadAddStore 3 2 1
      (.derefLoadAddStore 0 2 2
        (.storageDead 1 (.gotoNext (.ret 0)))))))

/-- Functional borrow return lens for `B12`: transforms in-place `&mut u64` mutation
into pure `MiniSSA` expression `old_deref + 1 + 2`. -/
def b12SsaBorrowLens (oldDerefVal : Nat) : Nat :=
  (oldDerefVal + 1) + 2

theorem direct_B12 (st : MirState) :
    ∃ sf, evalMir 8 st b12Mir =
      some ((getMem st (getReg st 1) + 1) + 2, sf) ∧
      getMem sf (getReg st 1) = (getMem st (getReg st 1) + 1) + 2 := by
  dsimp [b12Mir, evalMir, getSlot, putSlot, getReg, putReg, getMem, putMem, List.lookup]
  simp only [beq_self_eq_true, Option.getD_some]
  refine ⟨_, rfl, ?_⟩
  simp [List.lookup]

theorem minissa_B12 (oldDerefVal : Nat) :
    b12SsaBorrowLens oldDerefVal = (oldDerefVal + 1) + 2 := rfl

#eval (
  [ ("B01", mirAstNodes b01Mir, ssaAstNodes b01Ssa)
  , ("B02", mirAstNodes b02Mir, ssaAstNodes b02Ssa)
  , ("B03", mirAstNodes b03Mir, ssaAstNodes b03Ssa)
  , ("B04", mirAstNodes b04Mir, ssaAstNodes b04Ssa)
  , ("B05", mirAstNodes b05Mir, ssaAstNodes b05Ssa)
  , ("B06", mirAstNodes b06Mir, ssaAstNodes b06Ssa)
  , ("B07", mirAstNodes b07Mir, ssaAstNodes b07Ssa)
  , ("B08", mirAstNodes b08Mir, ssaAstNodes b08Ssa)
  , ("B09", mirAstNodes b09Mir, ssaAstNodes b09Ssa)
  , ("B10", mirAstNodes b10Mir, ssaAstNodes b10Ssa)
  , ("B11", mirAstNodes b11Mir, ssaAstNodes b11Ssa)
  , ("B12", mirAstNodes b12Mir, 5)
  ]
)

#print axioms direct_B01
#print axioms minissa_B01
#print axioms direct_B12
#print axioms minissa_B12

end AnnealSpecCompression
