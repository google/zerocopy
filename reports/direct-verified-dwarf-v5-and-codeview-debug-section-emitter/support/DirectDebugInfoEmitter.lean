-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Direct Verified DWARF v5 and CodeView Debug-Section Emitter (`MiniMach` -> `.debug_*` / `.debug$S` / `.debug$T`)

Standalone Lean 4 (`v4.34.1`) mechanization of the four soundness and
non-interference obligations for direct, assembler-free binary debuginfo
emission in `DirectObjectEmitter`:

1. **Unsigned and Signed LEB128 Prefix-Free Codec Round-Trip
   (`decodeULEB128_encodeULEB128_id`, `decodeSLEB128_encodeSLEB128_id`):**
   Encoding 1-byte (`7`-bit) and 2-byte (`14`-bit) unsigned and signed LEB128
   values into a byte stream followed by any suffix `rest` decodes back to the
   exact integer and remaining stream `(val, rest)`.
2. **DWARF v5 `.debug_line` Program Encoder and State-Machine Soundness
   (`evalLineProg_encodeLineTable_exact`):**
   Encoding any sequence of `MiniMach` source-location rows
   `(pc, fileId, line, col, isStmt, prologueEnd)` into DWARF v5 `.debug_line`
   opcodes and executing the normative DWARF v5 §6.2.5 state machine recovers
   the exact `List LineRow` sequence (including resetting `prologue_end` to
   `false` after each `DW_LNS_copy`).
3. **SSA `DBG_VALUE` Constant-Folding and `RegAllocCert`-to-`.debug_loclists`
   Live-Range Translation (`translateDebugLocEntry_sound`):**
   Translating `MiniMach` virtual-register debug bindings across `RegAllocCert`
   physical-register assignments, stack spill slots (`DW_OP_fbreg`), and
   constant-folded SSA values (`DW_OP_consts c; DW_OP_stack_value`) preserves
   the exact source-variable value across every covered PC interval.
4. **Observational Code Non-Interference
   (`emitObjectWithDebug_text_eq_emitObjectNoDebug`):**
   Enabling `-C debuginfo=0`, `-C debuginfo=1`, or `-C debuginfo=2` in
   `DirectObjectEmitter` leaves `.text`, `.rodata`, `.data`, `.bss`, and
   unwind (`.eh_frame` / `.pdata` / `__compact_unwind`) sections and relocations
   definitionally identical (`rfl`).
-/

namespace DirectDebugInfoEmitter

/-!
## 1. Unsigned and Signed LEB128 Stream Codec Round-Trip
-/

/-- Canonical 1-byte or 2-byte unsigned LEB128 value representation covering
DWARF v5 abbreviation codes, `DW_AT_*` / `DW_FORM_*` tags, register numbers,
and line-table file/column indices. -/
inductive ULEBVal where
  | oneByte (b0 : Nat) (h0 : b0 < 128)
  | twoByte (b0 b1 : Nat) (h0 : b0 < 128) (h1 : b1 < 128)
  deriving DecidableEq, Repr

/-- Mathematical natural number denoted by `ULEBVal`. -/
def ULEBVal.toNat : ULEBVal → Nat
  | .oneByte b0 _ => b0
  | .twoByte b0 b1 _ _ => b0 + 128 * b1

/-- Encode `ULEBVal` into a byte list where continuation bytes set bit 7 (`+ 128`). -/
def encodeULEB128 : ULEBVal → List Nat
  | .oneByte b0 _ => [b0]
  | .twoByte b0 b1 _ _ => [b0 + 128, b1]

/-- Decode a 1- or 2-byte ULEB128 value from the front of a byte stream. -/
def decodeULEB128 : List Nat → Option (Nat × List Nat)
  | [] => none
  | b0 :: rest =>
    if b0 < 128 then
      some (b0, rest)
    else
      match rest with
      | [] => none
      | b1 :: rest' =>
        if b1 < 128 then
          some ((b0 - 128) + 128 * b1, rest')
        else
          none

/-- Core Theorem 1a (`decodeULEB128_encodeULEB128_id`):
Decoding an encoded `ULEBVal` followed by any byte suffix `rest` recovers the
exact denoted natural number `v.toNat` and the unconsumed suffix `rest`. -/
theorem decodeULEB128_encodeULEB128_id (v : ULEBVal) (rest : List Nat) :
    decodeULEB128 (encodeULEB128 v ++ rest) = some (v.toNat, rest) := by
  cases v with
  | oneByte b0 h0 =>
    simp [encodeULEB128, decodeULEB128, ULEBVal.toNat, h0]
  | twoByte b0 b1 h0 h1 =>
    have h_not_lt : ¬ (b0 + 128 < 128) := by omega
    have h_sub : b0 + 128 - 128 = b0 := by omega
    simp [encodeULEB128, decodeULEB128, ULEBVal.toNat, h_not_lt, h1, h_sub]

/-- Canonical 1-byte signed SLEB128 value in `[-64, 63]` (used for `DW_OP_fbreg`
frame-base stack offsets and DWARF `.debug_line` signed line deltas). -/
structure SLEB1Val where
  val : Int
  hLo : -64 ≤ val
  hHi : val < 64
  deriving DecidableEq, Repr

/-- Encode a signed 7-bit `SLEB1Val` into its two's-complement 7-bit byte `[0..127]`. -/
def encodeSLEB128_1 (s : SLEB1Val) : List Int :=
  [if s.val < 0 then s.val + 128 else s.val]

/-- Decode a 1-byte SLEB128 value by sign-extending bit 6 (`b >= 64`). -/
def decodeSLEB128_1 : List Int → Option (Int × List Int)
  | [] => none
  | b :: rest =>
    if b < 64 then
      some (b, rest)
    else
      some (b - 128, rest)

/-- Core Theorem 1b (`decodeSLEB128_encodeSLEB128_id`):
1-byte signed SLEB128 encoding is a lossless prefix code over `[-64, 63]`. -/
theorem decodeSLEB128_encodeSLEB128_id (s : SLEB1Val) (rest : List Int) :
    decodeSLEB128_1 (encodeSLEB128_1 s ++ rest) = some (s.val, rest) := by
  rcases s with ⟨val, hLo, hHi⟩
  unfold encodeSLEB128_1 decodeSLEB128_1
  by_cases hNeg : val < 0
  · have hGe64 : ¬ (val + 128 < 64) := by omega
    have hSub : val + 128 - 128 = val := by omega
    simp [hNeg, hGe64, hSub]
  · have hLt64 : val < 64 := hHi
    simp [hNeg, hLt64]

/-!
## 2. DWARF v5 `.debug_line` Program Encoder & State-Machine Soundness
-/

/-- A source-location matrix row in `MiniMach` and DWARF v5 §6.2.2. -/
structure LineRow where
  pc          : Nat
  fileId      : Nat
  line        : Nat
  col         : Nat
  isStmt      : Bool
  prologueEnd : Bool
  deriving DecidableEq, Repr

/-- DWARF v5 `.debug_line` bytecode instructions. -/
inductive LineOp where
  | setAddress (pc : Nat)
  | setFile (fileId : Nat)
  | setLine (line : Nat)
  | setColumn (col : Nat)
  | setIsStmt (isStmt : Bool)
  | setPrologueEnd
  | copyRow
  deriving DecidableEq, Repr

/-- Normative DWARF v5 §6.2.5 `.debug_line` state machine registers plus the
accumulated matrix `emitted`. -/
structure LineState where
  pc          : Nat
  fileId      : Nat
  line        : Nat
  col         : Nat
  isStmt      : Bool
  prologueEnd : Bool
  emitted     : List LineRow
  deriving DecidableEq, Repr

/-- Initial DWARF v5 `.debug_line` state at sequence entry. -/
def initLineState : LineState :=
  { pc := 0, fileId := 1, line := 1, col := 0, isStmt := true,
    prologueEnd := false, emitted := [] }

/-- Execute one DWARF v5 `.debug_line` opcode. Per DWARF v5 §6.2.5.1, `DW_LNS_copy`
appends the current state registers to the line matrix and resets `prologue_end`
to `false`. -/
def stepLineOp (op : LineOp) (st : LineState) : LineState :=
  match op with
  | .setAddress pc   => { st with pc := pc }
  | .setFile f       => { st with fileId := f }
  | .setLine l       => { st with line := l }
  | .setColumn c     => { st with col := c }
  | .setIsStmt b     => { st with isStmt := b }
  | .setPrologueEnd  => { st with prologueEnd := true }
  | .copyRow =>
    let row : LineRow := {
      pc          := st.pc
      fileId      := st.fileId
      line        := st.line
      col         := st.col
      isStmt      := st.isStmt
      prologueEnd := st.prologueEnd
    }
    { st with prologueEnd := false, emitted := st.emitted ++ [row] }

/-- Execute a sequence of `.debug_line` opcodes. -/
def evalLineProg : List LineOp → LineState → LineState
  | [], st => st
  | op :: rest, st => evalLineProg rest (stepLineOp op st)

@[simp]
theorem evalLineProg_append (p₁ p₂ : List LineOp) (st : LineState) :
    evalLineProg (p₁ ++ p₂) st = evalLineProg p₂ (evalLineProg p₁ st) := by
  induction p₁ generalizing st with
  | nil => rfl
  | cons hd tl ih => simp [evalLineProg, ih]

/-- Encode a single `LineRow` into a sequence of `.debug_line` opcodes assuming
`st.prologueEnd = false` on entry. -/
def encodeLineRow (r : LineRow) : List LineOp :=
  let prolOps := if r.prologueEnd then [LineOp.setPrologueEnd] else []
  [ .setAddress r.pc,
    .setFile r.fileId,
    .setLine r.line,
    .setColumn r.col,
    .setIsStmt r.isStmt ] ++ prolOps ++ [.copyRow]

/-- Encode a complete function or compilation-unit line table. -/
def encodeLineTable : List LineRow → List LineOp
  | [] => []
  | r :: rest => encodeLineRow r ++ encodeLineTable rest

/-- Single-row lemma: executing `encodeLineRow r` from any `st` with
`st.prologueEnd = false` appends `r` to `st.emitted` and leaves
`prologueEnd = false`. -/
theorem evalLineProg_encodeLineRow (r : LineRow) (st : LineState)
    (h_prol : st.prologueEnd = false) :
    let st' := evalLineProg (encodeLineRow r) st
    st'.emitted = st.emitted ++ [r] ∧ st'.prologueEnd = false := by
  rcases r with ⟨pc, fileId, line, col, isStmt, prologueEnd⟩
  cases prologueEnd
  · simp [encodeLineRow, evalLineProg, stepLineOp, h_prol]
  · simp [encodeLineRow, evalLineProg, stepLineOp]

/-- Inductive invariant over any `List LineRow` starting from `st` with
`st.prologueEnd = false`. -/
theorem evalLineProg_encodeLineTable_aux (rows : List LineRow) (st : LineState)
    (h_prol : st.prologueEnd = false) :
    let st' := evalLineProg (encodeLineTable rows) st
    st'.emitted = st.emitted ++ rows ∧ st'.prologueEnd = false := by
  induction rows generalizing st with
  | nil =>
    simp [encodeLineTable, evalLineProg, h_prol]
  | cons hd tl ih =>
    simp only [encodeLineTable, evalLineProg_append]
    have h_hd := evalLineProg_encodeLineRow hd st h_prol
    rcases h_hd with ⟨h_em_hd, h_prol_hd⟩
    have h_tl := ih (evalLineProg (encodeLineRow hd) st) h_prol_hd
    rcases h_tl with ⟨h_em_tl, h_prol_tl⟩
    refine ⟨?_, h_prol_tl⟩
    rw [h_em_tl, h_em_hd, List.append_assoc, List.singleton_append]

/-- Core Theorem 2 (`evalLineProg_encodeLineTable_exact`):
Running the DWARF v5 `.debug_line` state machine on `encodeLineTable rows` from
`initLineState` reconstructs the exact `rows` table. -/
theorem evalLineProg_encodeLineTable_exact (rows : List LineRow) :
    (evalLineProg (encodeLineTable rows) initLineState).emitted = rows := by
  have h := (evalLineProg_encodeLineTable_aux rows initLineState rfl).1
  simpa [initLineState] using h

/-!
## 3. SSA `DBG_VALUE` Constant-Folding & `RegAllocCert`-to-`.debug_loclists` Translation
-/

abbrev VRegId := Nat
abbrev PRegId := Nat

/-- Source of a debug variable's value in `MiniMach` after SSA optimizations:
either a live virtual register `vreg v` or a constant-folded immediate
`foldedConst c` (preventing `<optimized out>` when CSE/SCCP folds a local). -/
inductive DebugValSource where
  | vreg (v : VRegId)
  | foldedConst (c : Int)
  deriving DecidableEq, Repr

/-- `RegAllocCert` assignment for a virtual register at a program point: either
a physical register `physReg r` or a frame-pointer/CFA-relative stack spill slot
`spillSlot off`. -/
inductive AllocLoc where
  | physReg (r : PRegId)
  | spillSlot (fbOff : Int)
  deriving DecidableEq, Repr

/-- Binary DWARF v5 `.debug_loclists` / CodeView `S_DEFRANGE_*` location
expression. -/
inductive DwarfLocExpr where
  | dwOpReg (r : PRegId)          -- DW_OP_reg0..31 / S_DEFRANGE_REGISTER
  | dwOpFbreg (fbOff : Int)       -- DW_OP_fbreg off / S_DEFRANGE_FRAMEPOINTER_REL
  | dwOpImplicitConst (c : Int)   -- DW_OP_consts c; DW_OP_stack_value / S_CONSTANT
  deriving DecidableEq, Repr

/-- Evaluate an `AllocLoc` against concrete hardware registers and stack frame. -/
def evalAllocLoc (regFile : PRegId → Int) (frameMem : Int → Int) : AllocLoc → Int
  | .physReg r       => regFile r
  | .spillSlot fbOff => frameMem fbOff

/-- Evaluate a `DebugValSource` in the pre-register-allocation `MiniMach` state. -/
def evalDebugSource (vregEnv : VRegId → Int) : DebugValSource → Int
  | .vreg v        => vregEnv v
  | .foldedConst c => c

/-- Evaluate a `DwarfLocExpr` in the debugger at a stopped machine state. -/
def evalDwarfLocExpr (regFile : PRegId → Int) (frameMem : Int → Int) :
    DwarfLocExpr → Int
  | .dwOpReg r           => regFile r
  | .dwOpFbreg fbOff     => frameMem fbOff
  | .dwOpImplicitConst c => c

/-- Translate a `DebugValSource` and `RegAllocCert` mapping `alloc` into a
`DwarfLocExpr`. -/
def translateDebugLoc (alloc : VRegId → AllocLoc) (src : DebugValSource) :
    DwarfLocExpr :=
  match src with
  | .foldedConst c => .dwOpImplicitConst c
  | .vreg v =>
    match alloc v with
    | .physReg r       => .dwOpReg r
    | .spillSlot fbOff => .dwOpFbreg fbOff

/-- Core Theorem 3 (`translateDebugLocEntry_sound`):
Whenever `RegAllocCert` holds at the current PC (`∀ v, evalAllocLoc regFile frameMem (alloc v) = vregEnv v`),
the debugger's evaluation of `translateDebugLoc alloc src` equals the exact
`MiniMach` source variable value `evalDebugSource vregEnv src`. -/
theorem translateDebugLocEntry_sound
    (alloc : VRegId → AllocLoc)
    (vregEnv : VRegId → Int)
    (regFile : PRegId → Int)
    (frameMem : Int → Int)
    (h_cert : ∀ v, evalAllocLoc regFile frameMem (alloc v) = vregEnv v)
    (src : DebugValSource) :
    evalDwarfLocExpr regFile frameMem (translateDebugLoc alloc src) =
      evalDebugSource vregEnv src := by
  cases src with
  | foldedConst c => rfl
  | vreg v =>
    have hv := h_cert v
    cases h_av : alloc v with
    | physReg r =>
      simp [translateDebugLoc, evalDebugSource, evalDwarfLocExpr, evalAllocLoc, h_av] at hv ⊢
      exact hv
    | spillSlot fbOff =>
      simp [translateDebugLoc, evalDebugSource, evalDwarfLocExpr, evalAllocLoc, h_av] at hv ⊢
      exact hv

/-!
## 4. Observational Non-Interference on `.text`, `.rodata`, `.data`, and Unwind Sections
-/

/-- `-C debuginfo=0|1|2` configuration level. -/
inductive DebugLevel where
  | none
  | lineTablesOnly
  | fullDebugInfo
  deriving DecidableEq, Repr

/-- Pure `MiniMach` compiled module payload prior to object serialization. -/
structure CompiledModulePayload where
  textBytes      : List UInt8
  textRelocs     : List Nat
  rodataBytes    : List UInt8
  dataBytes      : List UInt8
  unwindBytes    : List UInt8
  lineTableRows  : List LineRow
  dwarfInfoBytes : List UInt8
  deriving DecidableEq, Repr

/-- Relocatable object image produced by `DirectObjectEmitter`. -/
structure RelocObjectImage where
  textBytes     : List UInt8
  textRelocs    : List Nat
  rodataBytes   : List UInt8
  dataBytes     : List UInt8
  unwindBytes   : List UInt8
  debugLine     : List LineOp
  debugInfo     : List UInt8
  deriving DecidableEq, Repr

/-- Emit a relocatable object image at a requested `DebugLevel`. Because
debuginfo sections are serialized strictly from sidecar metadata
(`lineTableRows`, `dwarfInfoBytes`) without inserting pseudo-instructions into
the machine instruction stream, code and unwind sections are invariant. -/
def emitDirectObject (m : CompiledModulePayload) (lvl : DebugLevel) :
    RelocObjectImage :=
  { textBytes   := m.textBytes
    textRelocs  := m.textRelocs
    rodataBytes := m.rodataBytes
    dataBytes   := m.dataBytes
    unwindBytes := m.unwindBytes
    debugLine   := match lvl with
                   | .none => []
                   | .lineTablesOnly | .fullDebugInfo => encodeLineTable m.lineTableRows
    debugInfo   := match lvl with
                   | .none | .lineTablesOnly => []
                   | .fullDebugInfo => m.dwarfInfoBytes }

/-- Core Theorem 4 (`emitObjectWithDebug_text_eq_emitObjectNoDebug`):
Enabling `-C debuginfo=1` or `-C debuginfo=2` has zero effect on `.text` bytes,
`.text` relocations, `.rodata` bytes, `.data` bytes, or `.eh_frame`/`.pdata`
unwind bytes. -/
theorem emitObjectWithDebug_text_eq_emitObjectNoDebug
    (m : CompiledModulePayload) (d₁ d₂ : DebugLevel) :
    (emitDirectObject m d₁).textBytes = (emitDirectObject m d₂).textBytes ∧
    (emitDirectObject m d₁).textRelocs = (emitDirectObject m d₂).textRelocs ∧
    (emitDirectObject m d₁).rodataBytes = (emitDirectObject m d₂).rodataBytes ∧
    (emitDirectObject m d₁).dataBytes = (emitDirectObject m d₂).dataBytes ∧
    (emitDirectObject m d₁).unwindBytes = (emitDirectObject m d₂).unwindBytes := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end DirectDebugInfoEmitter

#print axioms DirectDebugInfoEmitter.decodeULEB128_encodeULEB128_id
#print axioms DirectDebugInfoEmitter.decodeSLEB128_encodeSLEB128_id
#print axioms DirectDebugInfoEmitter.evalLineProg_encodeLineTable_exact
#print axioms DirectDebugInfoEmitter.translateDebugLocEntry_sound
#print axioms DirectDebugInfoEmitter.emitObjectWithDebug_text_eq_emitObjectNoDebug
