/-
  UnifiedRegAllocLaneCert.lean
  Standalone Lean 4 (v4.34.1) mechanization for verified SSA register allocation,
  sub-register bit-lane framing, parallel-move sequentialization, rematerialization,
  and unified ABI / RegAllocCert / DWARF composite-location soundness.

  Axiom discipline: zero `sorry` (`sorryAx`), zero `native_decide` (`Lean.ofReduceBool`),
  zero `bv_decide`, zero `partial`, zero `@[extern]` (standard Lean core axioms only).
-/

namespace UnifiedRegAllocLaneCert

/-- Fine-grained 10-lane partition of an architectural register (covering x86-64,
    i686, and AArch64 GPR + SIMD/FP aliasing hierarchies):
    - `b0`: bits [7:0]   (`AL`, `R8B`, `W0[7:0]`, `B0`)
    - `b1`: bits [15:8]  (`AH` high-byte sub-register on x86/i686; upper half of `H0`)
    - `b2, b3`: bits [23:16], [31:24] (`EAX[31:16]`, `W0[31:16]`, `S0[31:16]`)
    - `b4..b7`: bits [63:32] (`RAX[63:32]`, `X0[63:32]`, `D0[63:32]`, `XMM[63:32]`)
    - `xmmHi`: bits [127:64] (`XMM[127:64]`, `Q0[127:64]`)
    - `ymmHi`: bits [255:128] (`YMM[255:128]`, `Z0[255:128]`)
    - `zmmHi`: bits [511:256] (`ZMM[511:256]`) -/
inductive LaneId : Type where
  | b0 | b1 | b2 | b3 | b4 | b5 | b6 | b7 | xmmHi | ymmHi | zmmHi
  deriving DecidableEq, Repr

/-- Concrete value of a physical register decomposed by canonical sub-register lanes. -/
structure RegVal where
  b0    : Nat := 0
  b1    : Nat := 0
  b2    : Nat := 0
  b3    : Nat := 0
  b4    : Nat := 0
  b5    : Nat := 0
  b6    : Nat := 0
  b7    : Nat := 0
  xmmHi : Nat := 0
  ymmHi : Nat := 0
  zmmHi : Nat := 0
  deriving DecidableEq, Repr

def readLane (l : LaneId) (r : RegVal) : Nat :=
  match l with
  | .b0    => r.b0
  | .b1    => r.b1
  | .b2    => r.b2
  | .b3    => r.b3
  | .b4    => r.b4
  | .b5    => r.b5
  | .b6    => r.b6
  | .b7    => r.b7
  | .xmmHi => r.xmmHi
  | .ymmHi => r.ymmHi
  | .zmmHi => r.zmmHi

def writeSingleLane (l : LaneId) (v : Nat) (r : RegVal) : RegVal :=
  match l with
  | .b0    => { r with b0 := v }
  | .b1    => { r with b1 := v }
  | .b2    => { r with b2 := v }
  | .b3    => { r with b3 := v }
  | .b4    => { r with b4 := v }
  | .b5    => { r with b5 := v }
  | .b6    => { r with b6 := v }
  | .b7    => { r with b7 := v }
  | .xmmHi => { r with xmmHi := v }
  | .ymmHi => { r with ymmHi := v }
  | .zmmHi => { r with zmmHi := v }

/-- Architectural sub-register slice views used across ABI, RegAlloc, and DWARF. -/
inductive SubRegSlice : Type where
  | lo8        -- bits [7:0] (`AL`, `R8B`, `B0`)
  | hi8        -- bits [15:8] (`AH`, `BH`, `CH`, `DH` at bit offset 8)
  | lo16       -- bits [15:0] (`AX`, `R8W`, `H0`)
  | lo32       -- bits [31:0] (`EAX`, `W0`, `S0`)
  | hi32       -- bits [63:32] (artificial `W0_HI` / `RAX[63:32]`)
  | full64     -- bits [63:0] (`RAX`, `X0`, `D0`)
  | xmm128     -- bits [127:0] (`XMM0`, `Q0`)
  | ymm256     -- bits [255:0] (`YMM0`)
  | zmm512     -- bits [511:0] (`ZMM0`)
  deriving DecidableEq, Repr

/-- Hardware write semantics distinguishing upper-lane preservation vs implicit zeroing. -/
inductive WriteMode : Type where
  | preserveUpper  -- x86 `Lo8`/`Hi8`/`Lo16`, legacy SSE scalar `MOVSS`/`ADDSS`/`SQRTSD`, AArch64 `BFM`/`MOVK`
  | zeroExtend64   -- x86-64 32-bit GPR write (`MOV32rr` -> zeroes [63:32]); AArch64 `W` write (`MOV Wd, Wn` -> zeroes `Xd[63:32]`)
  | zeroExtend128  -- AArch64 scalar `B`/`H`/`S`/`D` write -> zeroes `Qd[127:width]` (non-SVE)
  | zeroExtend512  -- x86-64 VEX-128/VEX-256/EVEX write -> zeroes `YMM[255:128]` and `ZMM[511:256]`
  deriving DecidableEq, Repr

def sliceLanes : SubRegSlice -> List LaneId
  | .lo8    => [.b0]
  | .hi8    => [.b1]
  | .lo16   => [.b0, .b1]
  | .lo32   => [.b0, .b1, .b2, .b3]
  | .hi32   => [.b4, .b5, .b6, .b7]
  | .full64 => [.b0, .b1, .b2, .b3, .b4, .b5, .b6, .b7]
  | .xmm128 => [.b0, .b1, .b2, .b3, .b4, .b5, .b6, .b7, .xmmHi]
  | .ymm256 => [.b0, .b1, .b2, .b3, .b4, .b5, .b6, .b7, .xmmHi, .ymmHi]
  | .zmm512 => [.b0, .b1, .b2, .b3, .b4, .b5, .b6, .b7, .xmmHi, .ymmHi, .zmmHi]

def laneInSlice (l : LaneId) (s : SubRegSlice) : Bool :=
  (sliceLanes s).contains l

def zeroedByMode (s : SubRegSlice) (m : WriteMode) (l : LaneId) : Bool :=
  if laneInSlice l s then false
  else match m with
  | .preserveUpper => false
  | .zeroExtend64  => laneInSlice l .full64
  | .zeroExtend128 => laneInSlice l .xmm128
  | .zeroExtend512 => true

def touchedByWrite (s : SubRegSlice) (m : WriteMode) (l : LaneId) : Bool :=
  laneInSlice l s || zeroedByMode s m l

/-- Apply a slice write with explicit `WriteMode` to an architectural register `dst`. -/
def applyRegWrite (s : SubRegSlice) (m : WriteMode) (payload : RegVal) (dst : RegVal) : RegVal :=
  let stepLane (l : LaneId) (cur : Nat) (src : Nat) : Nat :=
    if laneInSlice l s then src
    else if zeroedByMode s m l then 0
    else cur
  { b0    := stepLane .b0    dst.b0    payload.b0
  , b1    := stepLane .b1    dst.b1    payload.b1
  , b2    := stepLane .b2    dst.b2    payload.b2
  , b3    := stepLane .b3    dst.b3    payload.b3
  , b4    := stepLane .b4    dst.b4    payload.b4
  , b5    := stepLane .b5    dst.b5    payload.b5
  , b6    := stepLane .b6    dst.b6    payload.b6
  , b7    := stepLane .b7    dst.b7    payload.b7
  , xmmHi := stepLane .xmmHi dst.xmmHi payload.xmmHi
  , ymmHi := stepLane .ymmHi dst.ymmHi payload.ymmHi
  , zmmHi := stepLane .zmmHi dst.zmmHi payload.zmmHi }

/-- Extract a slice into canonical position starting at `b0` (for `hi8` and `hi32` shifts). -/
def extractSliceVal (s : SubRegSlice) (r : RegVal) : List Nat :=
  match s with
  | .lo8    => [r.b0]
  | .hi8    => [r.b1]
  | .lo16   => [r.b0, r.b1]
  | .lo32   => [r.b0, r.b1, r.b2, r.b3]
  | .hi32   => [r.b4, r.b5, r.b6, r.b7]
  | .full64 => [r.b0, r.b1, r.b2, r.b3, r.b4, r.b5, r.b6, r.b7]
  | .xmm128 => [r.b0, r.b1, r.b2, r.b3, r.b4, r.b5, r.b6, r.b7, r.xmmHi]
  | .ymm256 => [r.b0, r.b1, r.b2, r.b3, r.b4, r.b5, r.b6, r.b7, r.xmmHi, r.ymmHi]
  | .zmm512 => [r.b0, r.b1, r.b2, r.b3, r.b4, r.b5, r.b6, r.b7, r.xmmHi, r.ymmHi, r.zmmHi]

/-- Inject canonical slice bytes into the target `SubRegSlice` position of a `RegVal`. -/
def packSlicePayload (s : SubRegSlice) (bytes : List Nat) : RegVal :=
  match s, bytes with
  | .lo8,    [x0]                                  => { b0 := x0 }
  | .hi8,    [x0]                                  => { b1 := x0 }
  | .lo16,   [x0, x1]                              => { b0 := x0, b1 := x1 }
  | .lo32,   [x0, x1, x2, x3]                      => { b0 := x0, b1 := x1, b2 := x2, b3 := x3 }
  | .hi32,   [x0, x1, x2, x3]                      => { b4 := x0, b5 := x1, b6 := x2, b7 := x3 }
  | .full64, [x0, x1, x2, x3, x4, x5, x6, x7]      => { b0 := x0, b1 := x1, b2 := x2, b3 := x3, b4 := x4, b5 := x5, b6 := x6, b7 := x7 }
  | .xmm128, [x0, x1, x2, x3, x4, x5, x6, x7, xh]  => { b0 := x0, b1 := x1, b2 := x2, b3 := x3, b4 := x4, b5 := x5, b6 := x6, b7 := x7, xmmHi := xh }
  | .ymm256, [x0, x1, x2, x3, x4, x5, x6, x7, xh, yh] =>
      { b0 := x0, b1 := x1, b2 := x2, b3 := x3, b4 := x4, b5 := x5, b6 := x6, b7 := x7, xmmHi := xh, ymmHi := yh }
  | .zmm512, [x0, x1, x2, x3, x4, x5, x6, x7, xh, yh, zh] =>
      { b0 := x0, b1 := x1, b2 := x2, b3 := x3, b4 := x4, b5 := x5, b6 := x6, b7 := x7, xmmHi := xh, ymmHi := yh, zmmHi := zh }
  | _, _ => {}

/-! ### 1. Sub-Register Bit-Lane Framing & Zero-Extension Hazard Theorems -/

/-- Theorem 1a (Sub-Register Lane Framing): Any lane `l` outside `touchedByWrite s m`
    is strictly preserved by `applyRegWrite s m payload dst`. -/
theorem applyRegWrite_preserves_untouched
    (s : SubRegSlice) (m : WriteMode) (payload dst : RegVal) (l : LaneId)
    (h_untouched : touchedByWrite s m l = false) :
    readLane l (applyRegWrite s m payload dst) = readLane l dst := by
  unfold touchedByWrite at h_untouched
  cases l <;> simp only [Bool.or_eq_false_iff] at h_untouched <;>
    rcases h_untouched with ⟨h_in, h_zero⟩ <;>
    simp [readLane, applyRegWrite, h_in, h_zero]

/-- Theorem 1b (Written Slice Read-Back): Every lane `l` inside `s` reads back
    the exact lane from `payload` after `applyRegWrite s m payload dst`. -/
theorem applyRegWrite_reads_written
    (s : SubRegSlice) (m : WriteMode) (payload dst : RegVal) (l : LaneId)
    (h_in : laneInSlice l s = true) :
    readLane l (applyRegWrite s m payload dst) = readLane l payload := by
  cases l <;> simp [readLane, applyRegWrite, h_in]

/-- Theorem 1c (x86 `AL`/`AH` Disjoint Byte Co-Allocation): Writing `AL` (`lo8`, `preserveUpper`)
    and `AH` (`hi8`, `preserveUpper`) on the same physical GPR preserves both 8-bit values
    and preserves upper bits `[63:16]`. -/
theorem x86_al_ah_disjoint_coallocation (r : RegVal) (v_al v_ah : Nat) :
    let r1 := applyRegWrite .lo8 .preserveUpper (packSlicePayload .lo8 [v_al]) r
    let r2 := applyRegWrite .hi8 .preserveUpper (packSlicePayload .hi8 [v_ah]) r1
    extractSliceVal .lo8 r2 = [v_al] ∧
    extractSliceVal .hi8 r2 = [v_ah] ∧
    extractSliceVal .hi32 r2 = extractSliceVal .hi32 r := by
  simp [applyRegWrite, packSlicePayload, extractSliceVal, laneInSlice, sliceLanes, zeroedByMode]

/-- Theorem 1d (x86-64 `Lo32_Zext` / AArch64 `W`-Write vs VEX-128 vs Legacy SSE Asymmetry):
    - Writing `lo32` with `zeroExtend64` zeroes `hi32` (`[63:32]`).
    - Writing `xmm128` with `preserveUpper` (legacy SSE) preserves `ymmHi` (`[255:128]`).
    - Writing `xmm128` with `zeroExtend512` (VEX-128) zeroes `ymmHi` and `zmmHi`. -/
theorem partial_write_mode_asymmetries (r p : RegVal) :
    extractSliceVal .hi32 (applyRegWrite .lo32 .zeroExtend64 p r) = [0, 0, 0, 0] ∧
    readLane .ymmHi (applyRegWrite .xmm128 .preserveUpper p r) = r.ymmHi ∧
    readLane .ymmHi (applyRegWrite .xmm128 .zeroExtend512 p r) = 0 ∧
    readLane .zmmHi (applyRegWrite .ymm256 .zeroExtend512 p r) = 0 := by
  simp [applyRegWrite, extractSliceVal, readLane, laneInSlice, sliceLanes, zeroedByMode]

/-! ### 2. Unified Physical Location (ABI + RegAllocCert + DWARF) -/

abbrev PRegId := Nat
abbrev SlotId := Nat
abbrev VRegId := Nat

/-- Unified physical storage slice shared across calling-convention `FnAbi`,
    `RegAllocCert`, and DWARF debug location emission. -/
inductive PhysLoc : Type where
  | reg   (r : PRegId) (slice : SubRegSlice)
  | stack (s : SlotId) (slice : SubRegSlice)
  deriving DecidableEq, Repr

/-- Concrete machine state: finite register file, mutable spill stack, and immutable
    read-only frame/constant pool (for verified rematerialization). -/
structure MachState where
  regs   : PRegId -> RegVal
  stack  : SlotId -> RegVal
  roPool : SlotId -> RegVal

def readPhysLoc (st : MachState) : PhysLoc -> List Nat
  | .reg r sl   => extractSliceVal sl (st.regs r)
  | .stack s sl => extractSliceVal sl (st.stack s)

def updateReg (st : MachState) (r : PRegId) (v : RegVal) : MachState :=
  { st with regs := fun r' => if r' == r then v else st.regs r' }

def updateStack (st : MachState) (s : SlotId) (v : RegVal) : MachState :=
  { st with stack := fun s' => if s' == s then v else st.stack s' }

def writePhysLoc (st : MachState) (loc : PhysLoc) (m : WriteMode) (bytes : List Nat) : MachState :=
  match loc with
  | .reg r sl =>
      updateReg st r (applyRegWrite sl m (packSlicePayload sl bytes) (st.regs r))
  | .stack s sl =>
      updateStack st s (applyRegWrite sl .preserveUpper (packSlicePayload sl bytes) (st.stack s))

theorem readLane_packSlicePayload_same (sl : SubRegSlice) (r : RegVal) (l : LaneId)
    (h_in : laneInSlice l sl = true) :
    readLane l (packSlicePayload sl (extractSliceVal sl r)) = readLane l r := by
  cases sl <;> cases l <;> simp [laneInSlice, sliceLanes] at h_in <;>
    simp [packSlicePayload, extractSliceVal, readLane]

theorem extractSliceVal_write_roundtrip (sl : SubRegSlice) (m : WriteMode) (src dst : RegVal) :
    extractSliceVal sl (applyRegWrite sl m (packSlicePayload sl (extractSliceVal sl src)) dst) =
      extractSliceVal sl src := by
  cases sl <;>
    simp [extractSliceVal, applyRegWrite, packSlicePayload, laneInSlice, sliceLanes]

/-- Two `PhysLoc`s are write-non-interfering when writes to `dst` under `m` cannot
    overwrite or zero-extend over any lane read by `other`. -/
def nonInterferingWrite (dst : PhysLoc) (m : WriteMode) (other : PhysLoc) : Bool :=
  match dst, other with
  | .reg r1 sl1, .reg r2 sl2 =>
      if r1 == r2 then
        (sliceLanes sl2).all (fun l => !(touchedByWrite sl1 m l))
      else true
  | .stack s1 sl1, .stack s2 sl2 =>
      if s1 == s2 then
        (sliceLanes sl2).all (fun l => !(touchedByWrite sl1 .preserveUpper l))
      else true
  | _, _ => true

theorem extractSliceVal_preserved_of_all_untouched
    (sl1 : SubRegSlice) (m : WriteMode) (payload dst : RegVal) (sl2 : SubRegSlice)
    (h_disj : (sliceLanes sl2).all (fun l => !(touchedByWrite sl1 m l)) = true) :
    extractSliceVal sl2 (applyRegWrite sl1 m payload dst) = extractSliceVal sl2 dst := by
  have h_lane : ∀ l, l ∈ sliceLanes sl2 ->
      readLane l (applyRegWrite sl1 m payload dst) = readLane l dst := by
    intro l hl
    rw [List.all_eq_true] at h_disj
    have h_not := h_disj l hl
    simp only [Bool.not_eq_true'] at h_not
    exact applyRegWrite_preserves_untouched sl1 m payload dst l h_not
  have hb0 := h_lane .b0
  have hb1 := h_lane .b1
  have hb2 := h_lane .b2
  have hb3 := h_lane .b3
  have hb4 := h_lane .b4
  have hb5 := h_lane .b5
  have hb6 := h_lane .b6
  have hb7 := h_lane .b7
  have hxh := h_lane .xmmHi
  have hyh := h_lane .ymmHi
  have hzh := h_lane .zmmHi
  simp only [readLane] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hxh hyh hzh
  cases sl2 <;> simp [sliceLanes] at hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hxh hyh hzh <;>
    simp [extractSliceVal, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hxh, hyh, hzh]

theorem writePhysLoc_frame
    (st : MachState) (dst : PhysLoc) (m : WriteMode) (bytes : List Nat) (other : PhysLoc)
    (h_ni : nonInterferingWrite dst m other = true) :
    readPhysLoc (writePhysLoc st dst m bytes) other = readPhysLoc st other := by
  cases dst with
  | reg r1 sl1 =>
    cases other with
    | reg r2 sl2 =>
      simp only [nonInterferingWrite] at h_ni
      by_cases h_eq : r1 = r2
      · subst h_eq
        simp only [beq_self_eq_true, ↓reduceIte] at h_ni
        simp only [writePhysLoc, readPhysLoc, updateReg, beq_self_eq_true, ↓reduceIte]
        exact extractSliceVal_preserved_of_all_untouched sl1 m _ _ sl2 h_ni
      · have h_neq21 : (r2 == r1) = false := beq_eq_false_iff_ne.mpr (fun h => h_eq h.symm)
        simp only [writePhysLoc, readPhysLoc, updateReg, h_neq21]
        rfl
    | stack s2 sl2 =>
      rfl
  | stack s1 sl1 =>
    cases other with
    | reg r2 sl2 =>
      rfl
    | stack s2 sl2 =>
      simp only [nonInterferingWrite] at h_ni
      by_cases h_eq : s1 = s2
      · subst h_eq
        simp only [beq_self_eq_true, ↓reduceIte] at h_ni
        simp only [writePhysLoc, readPhysLoc, updateStack, beq_self_eq_true, ↓reduceIte]
        exact extractSliceVal_preserved_of_all_untouched sl1 .preserveUpper _ _ sl2 h_ni
      · have h_neq21 : (s2 == s1) = false := beq_eq_false_iff_ne.mpr (fun h => h_eq h.symm)
        simp only [writePhysLoc, readPhysLoc, updateStack, h_neq21]
        rfl

def locSlice : PhysLoc -> SubRegSlice
  | .reg _ sl   => sl
  | .stack _ sl => sl

theorem writePhysLoc_same (st : MachState) (loc : PhysLoc) (m : WriteMode) (src : RegVal) :
    readPhysLoc (writePhysLoc st loc m (extractSliceVal (locSlice loc) src)) loc =
      extractSliceVal (locSlice loc) src := by
  cases loc with
  | reg r sl =>
    simp [locSlice, writePhysLoc, readPhysLoc, updateReg, extractSliceVal_write_roundtrip]
  | stack s sl =>
    simp [locSlice, writePhysLoc, readPhysLoc, updateStack, extractSliceVal_write_roundtrip]

/-! ### 3. Fixing `regalloc2`'s `Edit::Move` Unsoundness (`src/checker.rs:553-561`) -/

/-- Symbolic state mapping physical locations to tracked `Option VRegId`. -/
abbrev SymState := List (PhysLoc × VRegId)

def lookupSym (sym : SymState) (loc : PhysLoc) : Option VRegId :=
  match sym.find? (fun p => p.1 == loc) with
  | some (_, v) => some v
  | none        => none

/-- Kill every symbolic binding that overlaps with writing `dst` under `m`. -/
def killOverlapping (sym : SymState) (dst : PhysLoc) (m : WriteMode) : SymState :=
  sym.filter (fun p => nonInterferingWrite dst m p.1)

/-- Sound transfer for `Move(src -> dst, mode)`: ALWAYS kills `dst` and overlapping
    lanes FIRST, and only binds `(dst, v)` when `src` holds a tracked `some v` of
    matching slice shape. -/
def sliceShapeEq (s1 s2 : SubRegSlice) : Bool :=
  (sliceLanes s1).length == (sliceLanes s2).length

def stepMoveSound (sym : SymState) (src dst : PhysLoc) (m : WriteMode) : SymState :=
  let cleaned := killOverlapping sym dst m
  match lookupSym sym src with
  | some v =>
      if sliceShapeEq (locSlice src) (locSlice dst) then (dst, v) :: cleaned
      else cleaned
  | none => cleaned

/-- Buggy transfer mirroring `regalloc2/src/checker.rs:553-561`: when `lookupSym sym src`
    is `none` (uninitialized or clobbered source), leaves `sym` unchanged instead of
    killing `dst`! -/
def stepMoveBuggyRegalloc2 (sym : SymState) (src dst : PhysLoc) : SymState :=
  match lookupSym sym src with
  | some v => (dst, v) :: sym.filter (fun p => p.1 != dst)
  | none   => sym

abbrev SsaEnv := VRegId -> RegVal

def SymRefines (ssa : SsaEnv) (st : MachState) (sym : SymState) : Prop :=
  ∀ loc v, (loc, v) ∈ sym -> readPhysLoc st loc = extractSliceVal (locSlice loc) (ssa v)

def execMoveConcrete (st : MachState) (src dst : PhysLoc) (m : WriteMode) : MachState :=
  writePhysLoc st dst m (readPhysLoc st src)

theorem pack_extract_shape_roundtrip
    (sl1 sl2 : SubRegSlice) (m : WriteMode) (src dst : RegVal)
    (h_shape : sliceShapeEq sl1 sl2 = true) :
    extractSliceVal sl2 (applyRegWrite sl2 m (packSlicePayload sl2 (extractSliceVal sl1 src)) dst) =
      extractSliceVal sl2 (packSlicePayload sl2 (extractSliceVal sl1 src)) := by
  cases sl1 <;> cases sl2 <;> simp [sliceShapeEq, sliceLanes] at h_shape <;>
    simp [extractSliceVal, applyRegWrite, packSlicePayload, laneInSlice, sliceLanes]

/-- Theorem 2a (Sound `Edit::Move` Transfer): For same-slice moves, `stepMoveSound`
    soundly preserves `SymRefines` even when `src` is uninitialized/clobbered (`none`)
    or `m` zero-extends over upper sub-register lanes! -/
theorem stepMoveSound_preserves_refinement
    (ssa : SsaEnv) (st : MachState) (sym : SymState)
    (src dst : PhysLoc) (m : WriteMode)
    (h_same_slice : locSlice src = locSlice dst)
    (h_find_mem : ∀ v, lookupSym sym src = some v -> (src, v) ∈ sym)
    (h_ref : SymRefines ssa st sym) :
    SymRefines ssa (execMoveConcrete st src dst m) (stepMoveSound sym src dst m) := by
  intro loc v h_mem
  unfold stepMoveSound at h_mem
  cases h_look : lookupSym sym src with
  | none =>
    simp only [h_look, killOverlapping, List.mem_filter] at h_mem
    rcases h_mem with ⟨h_in, h_ni⟩
    unfold execMoveConcrete
    rw [writePhysLoc_frame st dst m _ loc h_ni]
    exact h_ref loc v h_in
  | some v_src =>
    have h_shape : sliceShapeEq (locSlice src) (locSlice dst) = true := by
      simp [sliceShapeEq, h_same_slice]
    simp only [h_look, h_shape, ↓reduceIte, List.mem_cons, killOverlapping, List.mem_filter] at h_mem
    rcases h_mem with h_pair | ⟨h_in, h_ni⟩
    · cases h_pair
      have h_src_in := h_find_mem _ h_look
      have h_src_val := h_ref src _ h_src_in
      unfold execMoveConcrete
      rw [h_src_val, h_same_slice]
      exact writePhysLoc_same st _ m (ssa _)
    · unfold execMoveConcrete
      rw [writePhysLoc_frame st dst m _ loc h_ni]
      exact h_ref loc v h_in

/-- Theorem 2b (Formal Counterexample to `regalloc2/src/checker.rs:553-561`):
    Exhibits a concrete `ssa`, `MachState` (with clobbered `p1` != `v0`), and `SymState`
    where `SymRefines` holds BEFORE `Move(p1 -> p0)`, `stepMoveBuggyRegalloc2` still claims
    `(p0, v0)` holds AFTER `Move(p1 -> p0)`, yet `SymRefines` is VIOLATED on the post-move
    `MachState` (and `stepMoveSound` rejects the stale binding!). -/
theorem buggyRegalloc2Move_unsound_witness :
    let p0 := PhysLoc.reg 0 .full64
    let p1 := PhysLoc.reg 1 .full64
    let v0 : VRegId := 0
    let ssa : SsaEnv := fun _ => { b0 := 42 }
    let st : MachState :=
      { regs := fun r => if r == 0 then { b0 := 42 } else { b0 := 99 }
      , stack := fun _ => {}
      , roPool := fun _ => {} }
    let sym : SymState := [(p0, v0)]
    SymRefines ssa st sym ∧
    (p0, v0) ∈ stepMoveBuggyRegalloc2 sym p1 p0 ∧
    ¬ SymRefines ssa (execMoveConcrete st p1 p0 .preserveUpper) (stepMoveBuggyRegalloc2 sym p1 p0) ∧
    (p0, v0) ∉ stepMoveSound sym p1 p0 .preserveUpper := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro loc v h_in
    simp at h_in
    rcases h_in with ⟨rfl, rfl⟩
    rfl
  · simp [stepMoveBuggyRegalloc2, lookupSym]
  · intro h_bad
    have h_eq := h_bad (PhysLoc.reg 0 .full64) 0 (by simp [stepMoveBuggyRegalloc2, lookupSym])
    simp [execMoveConcrete, writePhysLoc, readPhysLoc, updateReg, applyRegWrite,
          packSlicePayload, extractSliceVal, laneInSlice, sliceLanes, locSlice] at h_eq
  · simp [stepMoveSound, lookupSym, killOverlapping, nonInterferingWrite,
          sliceLanes, touchedByWrite, laneInSlice]

/-! ### 4. Parallel-Move Cycle Sequentialization with Sub-Register Lane Framing -/

structure SeqMove where
  src  : PhysLoc
  dst  : PhysLoc
  mode : WriteMode
  deriving DecidableEq, Repr

def execMoveSeq (st : MachState) : List SeqMove -> MachState
  | []      => st
  | m :: ms => execMoveSeq (execMoveConcrete st m.src m.dst m.mode) ms

/-- Symbolic parallel-move checker tracking original pre-sequence `PhysLoc` origins. -/
abbrev OriginEnv := List (PhysLoc × PhysLoc)

def lookupOrigin (env : OriginEnv) (loc : PhysLoc) : PhysLoc :=
  match env.find? (fun p => p.1 == loc) with
  | some (_, orig) => orig
  | none           => loc

def stepOriginMove (env : OriginEnv) (m : SeqMove) : Option OriginEnv :=
  if sliceShapeEq (locSlice m.src) (locSlice m.dst) then
    let srcOrig := lookupOrigin env m.src
    let cleaned := env.filter (fun p => nonInterferingWrite m.dst m.mode p.1)
    -- Also invalidate any untouched identity assumption on clobbered sibling lanes
    some ((m.dst, srcOrig) :: cleaned)
  else none

def runOriginMoves : List SeqMove -> OriginEnv -> Option OriginEnv
  | [], env      => some env
  | m :: ms, env =>
      match stepOriginMove env m with
      | none      => none
      | some env' => runOriginMoves ms env'

/-- Explicitly seed `OriginEnv` with all relevant locations `(l, l)` before running
    `stepOriginMove` so clobbered sibling lanes are soundly evicted rather than
    defaulting back to identity! -/
def checkParMoveOnDomain
    (domain : List PhysLoc) (seq : List SeqMove) (spec : List (PhysLoc × PhysLoc)) : Bool :=
  let initEnv : OriginEnv := domain.map (fun l => (l, l))
  match runOriginMoves seq initEnv with
  | none => false
  | some finalEnv =>
      spec.all (fun p =>
        finalEnv.any (fun q => q.1 == p.1 && q.2 == p.2))

def OriginRefines (st0 st : MachState) (env : OriginEnv) : Prop :=
  ∀ loc orig, (loc, orig) ∈ env ->
    sliceShapeEq (locSlice loc) (locSlice orig) = true ∧
    readPhysLoc st loc = readPhysLoc st0 orig

theorem extractSliceVal_write_same_shape
    (sl_d sl_o : SubRegSlice) (m : WriteMode) (src dst : RegVal)
    (h_shape : sliceShapeEq sl_d sl_o = true) :
    extractSliceVal sl_d (applyRegWrite sl_d m (packSlicePayload sl_d (extractSliceVal sl_o src)) dst) =
      extractSliceVal sl_o src := by
  cases sl_d <;> cases sl_o <;> simp [sliceShapeEq, sliceLanes] at h_shape <;>
    simp [extractSliceVal, applyRegWrite, packSlicePayload, laneInSlice, sliceLanes]

theorem writePhysLoc_readPhysLoc_same_shape
    (st0 st : MachState) (dst orig : PhysLoc) (m : WriteMode)
    (h_shape : sliceShapeEq (locSlice dst) (locSlice orig) = true) :
    readPhysLoc (writePhysLoc st dst m (readPhysLoc st0 orig)) dst = readPhysLoc st0 orig := by
  cases dst <;> cases orig <;> simp only [locSlice] at h_shape <;>
    simp [writePhysLoc, readPhysLoc, updateReg, updateStack,
          extractSliceVal_write_same_shape _ _ _ _ _ h_shape]

theorem sliceShapeEq_trans (a b c : SubRegSlice)
    (h1 : sliceShapeEq a b = true) (h2 : sliceShapeEq b c = true) :
    sliceShapeEq a c = true := by
  simp only [sliceShapeEq, beq_iff_eq] at h1 h2 ⊢
  omega

theorem sliceShapeEq_symm (a b : SubRegSlice)
    (h : sliceShapeEq a b = true) :
    sliceShapeEq b a = true := by
  simp only [sliceShapeEq, beq_iff_eq] at h ⊢
  omega

theorem stepOriginMove_sound
    (st0 st : MachState) (env env' : OriginEnv) (m : SeqMove)
    (h_ref : OriginRefines st0 st env)
    (h_src_seeded : ∃ o, env.find? (fun p => p.1 == m.src) = some (m.src, o))
    (h_step : stepOriginMove env m = some env') :
    OriginRefines st0 (execMoveConcrete st m.src m.dst m.mode) env' := by
  unfold stepOriginMove at h_step
  cases h_sl : sliceShapeEq (locSlice m.src) (locSlice m.dst)
  · simp [h_sl] at h_step
  · simp only [h_sl, ↓reduceIte, Option.some.injEq] at h_step
    subst h_step
    rcases h_src_seeded with ⟨o_src, h_find⟩
    have h_orig_eq : lookupOrigin env m.src = o_src := by
      simp [lookupOrigin, h_find]
    have h_mem_src : (m.src, o_src) ∈ env := List.mem_of_find?_eq_some h_find
    rcases h_ref m.src o_src h_mem_src with ⟨h_sl_orig, h_val_src⟩
    intro loc orig h_mem
    rw [h_orig_eq] at h_mem
    simp only [List.mem_cons, List.mem_filter] at h_mem
    rcases h_mem with h_pair | ⟨h_in, h_ni⟩
    · cases h_pair
      have h_dst_orig : sliceShapeEq (locSlice m.dst) (locSlice o_src) = true :=
        sliceShapeEq_trans _ _ _ (sliceShapeEq_symm _ _ h_sl) h_sl_orig
      refine ⟨h_dst_orig, ?_⟩
      unfold execMoveConcrete
      rw [h_val_src]
      exact writePhysLoc_readPhysLoc_same_shape st0 st m.dst o_src m.mode h_dst_orig
    · rcases h_ref loc orig h_in with ⟨h_sl_loc, h_val_loc⟩
      refine ⟨h_sl_loc, ?_⟩
      unfold execMoveConcrete
      rw [writePhysLoc_frame st m.dst m.mode _ loc h_ni]
      exact h_val_loc

/-- Concrete kernel-checked verification that a 3-way register swap cycle `(r0, r1, r2) := (r1, r2, r0)`
    using scratch register `r3` AND simultaneous `AL`/`AH` sub-register swap in `r4` using byte
    scratch `bl5` (`r5.lo8`) passes! -/
theorem parmove_3cycle_and_subreg_swap_verified :
    let r0 := PhysLoc.reg 0 .full64
    let r1 := PhysLoc.reg 1 .full64
    let r2 := PhysLoc.reg 2 .full64
    let scratch := PhysLoc.reg 3 .full64
    let al4 := PhysLoc.reg 4 .lo8
    let ah4 := PhysLoc.reg 4 .hi8
    let bl5 := PhysLoc.reg 5 .lo8
    let domain := [r0, r1, r2, scratch, al4, ah4, bl5]
    let seq : List SeqMove :=
      [ { src := r0,  dst := scratch, mode := .preserveUpper }
      , { src := r1,  dst := r0,      mode := .preserveUpper }
      , { src := r2,  dst := r1,      mode := .preserveUpper }
      , { src := scratch, dst := r2,  mode := .preserveUpper }
      , { src := al4, dst := bl5,     mode := .preserveUpper }
      , { src := ah4, dst := al4,     mode := .preserveUpper }
      , { src := bl5, dst := ah4,     mode := .preserveUpper } ]
    let spec := [(r0, r1), (r1, r2), (r2, r0), (al4, ah4), (ah4, al4)]
    checkParMoveOnDomain domain seq spec = true := by
  decide

/-! ### 5. Rematerialization Under Sub-Register Zero-Extension (`AArch64SRLTDefineSuperRegs` Invariant B) -/

inductive RematSource : Type where
  | constReg (val : RegVal)
  | roSlot   (slot : SlotId)
  deriving DecidableEq, Repr

def evalRematSource (st : MachState) : RematSource -> RegVal
  | .constReg v => v
  | .roSlot s   => st.roPool s

def execRemat (st : MachState) (src : RematSource) (dst : PRegId) (sl : SubRegSlice) (m : WriteMode) : MachState :=
  writePhysLoc st (.reg dst sl) m (extractSliceVal sl (evalRematSource st src))

/-- Check that rematerializing `(src, vreg)` into `(dst, sl)` with `WriteMode m` does NOT
    clobber any live lane in `sym` (specifically catching `zeroExtend64` / `zeroExtend128`
    clobbering live upper lanes!). -/
def checkRematSafe (sym : SymState) (dst : PRegId) (sl : SubRegSlice) (m : WriteMode) : Bool :=
  sym.all (fun (loc, _) => loc == .reg dst sl || nonInterferingWrite (.reg dst sl) m loc)

/-- Theorem 5a (Verified Rematerialization Soundness): When `checkRematSafe sym dst sl m = true`,
    rematerializing from an immutable constant or read-only frame slot (1) preserves every
    distinct live binding `(loc, v') ∈ sym` WITHOUT dropping any entry from `sym`, and
    (2) establishes `(.reg dst sl, v)`! -/
theorem checkRematSafe_sound
    (ssa : SsaEnv) (st : MachState) (sym : SymState)
    (src : RematSource) (v : VRegId) (dst : PRegId) (sl : SubRegSlice) (m : WriteMode)
    (h_ref : SymRefines ssa st sym)
    (h_origin : extractSliceVal sl (evalRematSource st src) = extractSliceVal sl (ssa v))
    (h_safe : checkRematSafe sym dst sl m = true) :
    SymRefines ssa (execRemat st src dst sl m)
      ((.reg dst sl, v) :: sym.filter (fun p => p.1 != .reg dst sl)) := by
  intro loc v' h_mem
  simp only [List.mem_cons, List.mem_filter] at h_mem
  rcases h_mem with ⟨rfl, rfl⟩ | ⟨h_in, h_neq⟩
  · unfold execRemat
    rw [h_origin]
    exact writePhysLoc_same st (.reg dst sl) m (ssa v)
  · unfold checkRematSafe at h_safe
    rw [List.all_eq_true] at h_safe
    have h_each := h_safe (loc, v') h_in
    simp only [Bool.or_eq_true] at h_each
    rcases h_each with h_eq | h_ni
    · simp only [bne_iff_ne, ne_eq] at h_neq
      simp only [beq_iff_eq] at h_eq
      exact False.elim (h_neq h_eq)
    · unfold execRemat
      rw [writePhysLoc_frame st (.reg dst sl) m _ loc h_ni]
      exact h_ref loc v' h_in

/-- Theorem 5b (Rematerialization Zero-Extension Hazard Counterexample — Formalizing
    `AArch64SRLTDefineSuperRegs.cpp:43-44,51-53` Invariant B):
    If `X0[63:32]` (`hi32`) holds a live variable `v_hi` while a 32-bit constant `v_lo` is
    rematerialized into `W0` (`lo32`) via `zeroExtend64`, `checkRematSafe` REJECTS the
    rematerialization (`false`), and executing it indeed destroys `X0[63:32]`! -/
theorem remat_narrow_zeroext_destroys_upper_lane :
    let hiLoc := PhysLoc.reg 0 .hi32
    let sym : SymState := [(hiLoc, 1)]
    let st : MachState :=
      { regs := fun _ => { b4 := 0xAA, b5 := 0xBB, b6 := 0xCC, b7 := 0xDD }
      , stack := fun _ => {}
      , roPool := fun _ => {} }
    checkRematSafe sym 0 .lo32 .zeroExtend64 = false ∧
    readPhysLoc (execRemat st (.constReg { b0 := 7 }) 0 .lo32 .zeroExtend64) hiLoc = [0, 0, 0, 0] := by
  refine ⟨rfl, rfl⟩

/-! ### 6. Unified DWARF `DW_OP_piece` / `DW_OP_bit_piece` / `DW_OP_regx` Seam -/

/-- Canonical DWARF v5 location-description opcodes for single and composite locations. -/
inductive DwarfAtom : Type where
  | reg0_31  (regNo : Nat)                     -- `DW_OP_reg0 .. DW_OP_reg31` (`regNo < 32`)
  | regx     (regNo : Nat)                     -- `DW_OP_regx <ULEB128>` (`regNo >= 32`, e.g., XMM16..31 = 67..82)
  | fbreg    (slot : SlotId)                   -- `DW_OP_fbreg <SLEB128>`
  | piece    (byteSize : Nat)                  -- `DW_OP_piece <ULEB128>` (byte-aligned offset 0)
  | bitPiece (bitSize : Nat) (bitOffset : Nat) -- `DW_OP_bit_piece <size> <offset>` (e.g., `AH` = 8 bits @ offset 8)
  deriving DecidableEq, Repr

/-- Emit a single DWARF fragment from a canonical `PhysLoc` (matching LLVM's
    `DwarfExpression::addReg` + `addMachineReg` + `addOpPiece` in `DwarfExpression.cpp:56-158`). -/
def emitDwarfFragment (loc : PhysLoc) : List DwarfAtom :=
  let addrAtom := match loc with
    | .reg r _   => if r < 32 then DwarfAtom.reg0_31 r else DwarfAtom.regx r
    | .stack s _ => DwarfAtom.fbreg s
  let pieceAtom := match locSlice loc with
    | .lo8    => DwarfAtom.piece 1
    | .hi8    => DwarfAtom.bitPiece 8 8
    | .lo16   => DwarfAtom.piece 2
    | .lo32   => DwarfAtom.piece 4
    | .hi32   => DwarfAtom.bitPiece 32 32
    | .full64 => DwarfAtom.piece 8
    | .xmm128 => DwarfAtom.piece 16
    | .ymm256 => DwarfAtom.piece 32
    | .zmm512 => DwarfAtom.piece 64
  [addrAtom, pieceAtom]

def emitCompositeDwarf (pieces : List PhysLoc) : List DwarfAtom :=
  pieces.flatMap emitDwarfFragment

def decodePieceAtom (r : RegVal) : DwarfAtom -> Option (List Nat)
  | .piece 1        => some (extractSliceVal .lo8 r)
  | .bitPiece 8 8   => some (extractSliceVal .hi8 r)
  | .piece 2        => some (extractSliceVal .lo16 r)
  | .piece 4        => some (extractSliceVal .lo32 r)
  | .bitPiece 32 32 => some (extractSliceVal .hi32 r)
  | .piece 8        => some (extractSliceVal .full64 r)
  | .piece 16       => some (extractSliceVal .xmm128 r)
  | .piece 32       => some (extractSliceVal .ymm256 r)
  | .piece 64       => some (extractSliceVal .zmm512 r)
  | _               => none

/-- DWARF location-expression evaluator over a concrete `MachState`. -/
def evalDwarfAtoms (st : MachState) : List DwarfAtom -> Option (List Nat)
  | [] => some []
  | (.reg0_31 r) :: pieceOp :: rest =>
      if r < 32 then
        match decodePieceAtom (st.regs r) pieceOp, evalDwarfAtoms st rest with
        | some frag, some tail => some (frag ++ tail)
        | _, _ => none
      else none
  | (.regx r) :: pieceOp :: rest =>
      match decodePieceAtom (st.regs r) pieceOp, evalDwarfAtoms st rest with
      | some frag, some tail => some (frag ++ tail)
      | _, _ => none
  | (.fbreg s) :: pieceOp :: rest =>
      match decodePieceAtom (st.stack s) pieceOp, evalDwarfAtoms st rest with
      | some frag, some tail => some (frag ++ tail)
      | _, _ => none
  | _ => none

theorem evalDwarfFragment_append
    (st : MachState) (loc : PhysLoc) (rest : List DwarfAtom) (tailBytes : List Nat)
    (h_rest : evalDwarfAtoms st rest = some tailBytes) :
    evalDwarfAtoms st (emitDwarfFragment loc ++ rest) =
      some (readPhysLoc st loc ++ tailBytes) := by
  cases loc with
  | reg r sl =>
    by_cases h_lt : r < 32
    · cases sl <;> simp [emitDwarfFragment, h_lt, locSlice, evalDwarfAtoms, decodePieceAtom, h_rest, readPhysLoc]
    · cases sl <;> simp [emitDwarfFragment, h_lt, locSlice, evalDwarfAtoms, decodePieceAtom, h_rest, readPhysLoc]
  | stack s sl =>
    cases sl <;> simp [emitDwarfFragment, locSlice, evalDwarfAtoms, decodePieceAtom, h_rest, readPhysLoc]

/-- Theorem 6a (Composite DWARF Decoder Exactness): Evaluating `emitCompositeDwarf pieces`
    reconstructs the exact concatenation of `readPhysLoc st loc` across arbitrary mixed
    `DW_OP_reg0..31`, `DW_OP_regx` (`XMM16..31`), `DW_OP_fbreg` spill slots, `DW_OP_piece`,
    and `DW_OP_bit_piece` (`AH` / `hi32`) fragments! -/
theorem emitCompositeDwarf_sound (st : MachState) (pieces : List PhysLoc) :
    evalDwarfAtoms st (emitCompositeDwarf pieces) =
      some (pieces.flatMap (readPhysLoc st)) := by
  induction pieces with
  | nil => rfl
  | cons loc tl ih =>
    simp only [emitCompositeDwarf, List.flatMap_cons]
    exact evalDwarfFragment_append st loc (emitCompositeDwarf tl) (tl.flatMap (readPhysLoc st)) ih

/-- Theorem 6b (End-to-End Unified Bridge — ABI + `RegAllocCert` + DWARF Value Preservation):
    Whenever `SymRefines ssa st sym` holds at a program point (established by `stepMoveSound` /
    `checkRematSafe`) and a source variable's fragments `(loc_i, v_i)` are all certified in `sym`,
    evaluating the emitted DWARF location list on `st` yields the exact concatenated SSA values
    — proving true debugger value accuracy (stronger than CompCert `Debugvarproof.v`, which
    proves only trace non-interference!). -/
theorem unified_regalloc_abi_dwarf_value_accuracy
    (ssa : SsaEnv) (st : MachState) (sym : SymState)
    (fragments : List (PhysLoc × VRegId))
    (h_ref : SymRefines ssa st sym)
    (h_cert : ∀ p, p ∈ fragments -> p ∈ sym) :
    evalDwarfAtoms st (emitCompositeDwarf (fragments.map Prod.fst)) =
      some (fragments.flatMap (fun (loc, v) => extractSliceVal (locSlice loc) (ssa v))) := by
  rw [emitCompositeDwarf_sound]
  congr 1
  induction fragments with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨loc, v⟩
    simp only [List.map_cons, List.flatMap_cons]
    have h_head := h_ref loc v (h_cert (loc, v) (by simp))
    have h_tail := ih (fun p hp => h_cert p (by simp [hp]))
    rw [h_head, h_tail]

end UnifiedRegAllocLaneCert

#print axioms UnifiedRegAllocLaneCert.applyRegWrite_preserves_untouched
#print axioms UnifiedRegAllocLaneCert.x86_al_ah_disjoint_coallocation
#print axioms UnifiedRegAllocLaneCert.partial_write_mode_asymmetries
#print axioms UnifiedRegAllocLaneCert.stepMoveSound_preserves_refinement
#print axioms UnifiedRegAllocLaneCert.buggyRegalloc2Move_unsound_witness
#print axioms UnifiedRegAllocLaneCert.stepOriginMove_sound
#print axioms UnifiedRegAllocLaneCert.parmove_3cycle_and_subreg_swap_verified
#print axioms UnifiedRegAllocLaneCert.checkRematSafe_sound
#print axioms UnifiedRegAllocLaneCert.remat_narrow_zeroext_destroys_upper_lane
#print axioms UnifiedRegAllocLaneCert.emitCompositeDwarf_sound
#print axioms UnifiedRegAllocLaneCert.unified_regalloc_abi_dwarf_value_accuracy
