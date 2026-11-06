module

public import Kraken.AArch64.Syntax
meta import Kraken.AArch64.Syntax
import Kraken.Attribute
public import Kraken.Mem
meta import Kraken.Mem
public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr

@[expose] public section

-- injective coercions only
attribute [-instance] BitVec.instNatCast
attribute [-instance] BitVec.instIntCast
instance : Coe Bool Nat where coe := Bool.toNat

@[kstep] def BitVec.unsigned {w} (x : BitVec w) : Int := x.toNat
@[kstep] def BitVec.signed {w} (x : BitVec w) : Int := x.toInt
@[kstep] def BitVec.take {w} (x : BitVec w) (n : Nat) : BitVec n := x.extractLsb' 0 n
@[kstep] def BitVec.drop {w} (x : BitVec w) (n : Nat) : BitVec (w - n) := x.extractLsb' n (w-n)

attribute [kstep]
  BitVec.ofInt_add
  BitVec.ofInt_toInt
  BitVec.signed
  BitVec.truncate

namespace RegOrSp
@[kstep] def base {w} (r : RegOrSp w) : XRegOrSp := match r with
  | .low r _ => r
end RegOrSp

namespace RegOrZr
@[kstep] def base {w} (r : RegOrZr w) : XRegOrXzr := match r with
  | .low r _ => r
end RegOrZr

structure Reg64s where
  X0 : UInt64 := 0
  X1 : UInt64 := 0
  X2 : UInt64 := 0
  X3 : UInt64 := 0
  X4 : UInt64 := 0
  X5 : UInt64 := 0
  X6 : UInt64 := 0
  X7 : UInt64 := 0
  X8 : UInt64 := 0
  X9 : UInt64 := 0
  X10 : UInt64 := 0
  X11 : UInt64 := 0
  X12 : UInt64 := 0
  X13 : UInt64 := 0
  X14 : UInt64 := 0
  X15 : UInt64 := 0
  X16 : UInt64 := 0
  X17 : UInt64 := 0
  X18 : UInt64 := 0
  X19 : UInt64 := 0
  X20 : UInt64 := 0
  X21 : UInt64 := 0
  X22 : UInt64 := 0
  X23 : UInt64 := 0
  X24 : UInt64 := 0
  X25 : UInt64 := 0
  X26 : UInt64 := 0
  X27 : UInt64 := 0
  X28 : UInt64 := 0
  X29 : UInt64 := 0
  X30 : UInt64 := 0
  SP : UInt64 := 0
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

@[kstep] def Reg64s.getXReg (s : Reg64s) (r : XReg) := match r with
  |  .X0 =>  s.X0 |  .X1 =>  s.X1 |  .X2 =>  s.X2 |  .X3 =>  s.X3
  |  .X4 =>  s.X4 |  .X5 =>  s.X5 |  .X6 =>  s.X6 |  .X7 =>  s.X7
  |  .X8 =>  s.X8 |  .X9 =>  s.X9 | .X10 => s.X10 | .X11 => s.X11
  | .X12 => s.X12 | .X13 => s.X13 | .X14 => s.X14 | .X15 => s.X15
  | .X16 => s.X16 | .X17 => s.X17 | .X18 => s.X18 | .X19 => s.X19
  | .X20 => s.X20 | .X21 => s.X21 | .X22 => s.X22 | .X23 => s.X23
  | .X24 => s.X24 | .X25 => s.X25 | .X26 => s.X26 | .X27 => s.X27
  | .X28 => s.X28 | .X29 => s.X29 | .X30 => s.X30

@[kstep] def Reg64s.getRegOrSp64 (s : Reg64s) (r : XRegOrSp) : RegWidth.W64.type := UInt64.toBitVec (match r with
  | .reg r => s.getXReg r
  | .SP => s.SP )

@[kstep] def Reg64s.getRegOrZr64 (s : Reg64s) (r : XRegOrXzr) : RegWidth.W64.type := UInt64.toBitVec (match r with
  | .reg r => s.getXReg r
  | .XZR => 0 ) -- Reads from XZR return constant 0.

@[kstep] def Reg64s.setXReg (regs : Reg64s) (r : XReg) (v : RegWidth.W64.type) : Reg64s :=
  let v := UInt64.ofBitVec v
  match r with
  |  .X0 => { regs with  X0 := v } |  .X1 => { regs with  X1 := v }
  |  .X2 => { regs with  X2 := v } |  .X3 => { regs with  X3 := v }
  |  .X4 => { regs with  X4 := v } |  .X5 => { regs with  X5 := v }
  |  .X6 => { regs with  X6 := v } |  .X7 => { regs with  X7 := v }
  |  .X8 => { regs with  X8 := v } |  .X9 => { regs with  X9 := v }
  | .X10 => { regs with X10 := v } | .X11 => { regs with X11 := v }
  | .X12 => { regs with X12 := v } | .X13 => { regs with X13 := v }
  | .X14 => { regs with X14 := v } | .X15 => { regs with X15 := v }
  | .X16 => { regs with X16 := v } | .X17 => { regs with X17 := v }
  | .X18 => { regs with X18 := v } | .X19 => { regs with X19 := v }
  | .X20 => { regs with X20 := v } | .X21 => { regs with X21 := v }
  | .X22 => { regs with X22 := v } | .X23 => { regs with X23 := v }
  | .X24 => { regs with X24 := v } | .X25 => { regs with X25 := v }
  | .X26 => { regs with X26 := v } | .X27 => { regs with X27 := v }
  | .X28 => { regs with X28 := v } | .X29 => { regs with X29 := v }
  | .X30 => { regs with X30 := v }

@[kstep] def Reg64s.setRegOrSp64 (regs : Reg64s) (r : XRegOrSp) (v : RegWidth.W64.type) : Reg64s :=
  match r with
  | .reg r => regs.setXReg r v
  | .SP => { regs with SP := UInt64.ofBitVec v }

@[kstep] def Reg64s.setRegOrZr64 (regs : Reg64s) (r : XRegOrXzr) (v : RegWidth.W64.type) : Reg64s :=
  match r with
  | .reg r => regs.setXReg r v
  | .XZR => regs -- Writes to XZR are dropped.

@[kstep] def Reg64s.getRegOrSp (s : Reg64s) {w} (r : RegOrSp w) : w.type :=
  (s.getRegOrSp64 r.base).take w.bits

@[kstep] def Reg64s.getRegOrZr (s : Reg64s) {w} (r : RegOrZr w) : w.type :=
  (s.getRegOrZr64 r.base).take w.bits

@[kstep] def Reg64s.setRegOrSp (s : Reg64s) {w} (r : RegOrSp w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.setRegOrSp64 r v
  | .low r .W32 => s.setRegOrSp64 r (v.zeroExtend _)

@[kstep] def Reg64s.setRegOrZr (s : Reg64s) {w} (r : RegOrZr w) (v : w.type) : Reg64s := match r with
  | .low r .W64 => s.setRegOrZr64 r v
  | .low r .W32 => s.setRegOrZr64 r (v.zeroExtend _)

structure StatusFlags where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

abbrev DataMem := Mem 64
instance : Repr DataMem where reprPrec _ _ := "<opaque memory>"
structure MachineData where -- does not include code or program position
  regs : Reg64s := {}
  status : StatusFlags := .mk false false false false
  dmem : DataMem := ∅
  deriving Repr, BEq, DecidableEq

-- We only allow nondeterministic choices for a fixed set of types.
class inductive NondetSupportingType : Type -> Type
  | bitvec (w : RegWidth) : NondetSupportingType w.type
  | bool : NondetSupportingType Bool
  | statusFlags : NondetSupportingType StatusFlags

def NondetSupportingType.from_hash {α} [t : NondetSupportingType α] (h : UInt64) : α :=
  match t with
  | .bool => h % 2 != 0
  | .statusFlags => let h := h.toBitVec; (.mk h[0] h[1] h[2] h[3])
  | .bitvec w => h.toBitVec.setWidth w.bits

instance (w : RegWidth) : NondetSupportingType w.type := .bitvec w
instance : NondetSupportingType Bool := .bool
instance : NondetSupportingType StatusFlags := .statusFlags

structure MachineState where
  data : MachineData
  pc : Int64

inductive Effects
  | done (a : MachineState)
  | unimplemented (msg : String)
  -- loads and stores *outside* the data memory, eg. MMIO, might still affect the data memory:
  -- for instance, MMIO reads/writes at certain device register addresses might change what
  -- data memory the process logically owns vs what memory is owned by devices
  | nonmem_load (dmem : DataMem) (addr : BitVec 64) (w : MemWidth) (ret : w.type → DataMem → Effects)
  | nonmem_store (dmem : DataMem) (addr : BitVec 64) {w : MemWidth} (v : w.type) (ret: DataMem → Effects)
  | undefined {α : Type} [NondetSupportingType α] (ret : α → Effects)
  | require_read_access (addr : BitVec 64) (w : MemWidth) (ok : Unit → Effects)
  | require_write_access (addr : BitVec 64) (w : MemWidth) (ok : Unit → Effects)
  | require_exec_access (p: Std.Rco Int64) (ok : Unit → Effects)
  | unaligned_sp {w : RegWidth} (sp : w.type)
export Effects (unimplemented nonmem_load nonmem_store undefined require_read_access require_write_access require_exec_access)

-- the unused `Std.Rco Int64` argument and the unmodified `MachineData` return
-- value are present for uniformity with RegOrMem.interp
def RegOrSp.interp {w} (r : RegOrSp w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.getRegOrSp r) s

def RegOrZr.interp {w} (r : RegOrZr w) (s : MachineData) (_ : Std.Rco Int64)
  (ret : w.type → MachineData → Effects) : Effects :=
  ret (s.regs.getRegOrZr r) s

-- Since MMIO can cause devices to do arbitrary actions, a load might actually
-- *modify* memory. For instance:
-- A TEST instruction might load a flag from an MMIO address and bitwise-and it with
-- an immediate, and if the result is non-zero, it might mean that some device has
-- finished processing a buffer and therefore now passes ownership of that buffer
-- to the CPU.
-- Note that `ret` takes a whole `MachineData` instead of only `DataMem`, which
-- provides a bit more flexibility than we need: MachineData.load might change
-- dmem, but will not change the registers or status flags.
-- But this superfluous flexibility helps us simplify the state-threading:
-- Instead of writing `fun v dmem => ... { s with dmem } ...` everywhere, we
-- can just write `fun v s => ...` and the new `s` will shadow the old `s`.
def MachineData.load
  (s : MachineData) (addr : BitVec 64) (w : MemWidth)
  (ret : w.type → MachineData → Effects): Effects :=
  require_read_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some i => ret (.ofInt _ i) s
    | .none => nonmem_load s.dmem addr w (fun v dmem => ret v { s with dmem }))

def MachineData.store (s : MachineData) (addr : BitVec 64) {w : MemWidth} (v : w.type) (ret: MachineData → Effects) : Effects :=
  require_write_access addr w (fun _unit =>
    match Mem.loadInt s.dmem addr w.bytes with
    | .some _ =>
        ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }
    | .none => nonmem_store s.dmem addr v (fun dmem' => ret { s with dmem := dmem' }))

class Labels where label : Label → Int64
export Labels (label)

@[kstep] def ConstExpr.interp [Labels] : ConstExpr → Std.Rco Int64 → Int64
  | .label l, _ => Labels.label l
  | .int64 i, _ => i
  | .before_current_instruction, r => r.lower
  | .after_current_instruction, r => r.upper
  | .add e1 e2, p => e1.interp p + e2.interp p
  | .sub e1 e2, p => e1.interp p - e2.interp p
  | .pg_hi21 e, p =>
    let val := BitVec.ofInt 64 (Int64.toInt (e.interp p))
    let page := val &&& ~~~0xFFF#64
    Int64.ofNat page.toNat
  | .lo12 e, p =>
    let val := BitVec.ofInt 64 (Int64.toInt (e.interp p))
    let lo := val &&& 0xFFF#64
    Int64.ofNat lo.toNat

def ConstExpr.evalBranchTarget [Labels] (target : ConstExpr) (p : Std.Rco Int64) : Int64 :=
  match target with
  | .int64 imm => p.lower + imm
  | _ => target.interp p

@[kstep] def BitVec.apply_extend (v : BitVec 64) (ext : Extend) :=
  let extended := match ext.type with
               | .UXTB => (v.take MemWidth.W8.bits).unsigned
               | .SXTB => (v.take MemWidth.W8.bits).signed
               | .UXTH => (v.take MemWidth.W16.bits).unsigned
               | .SXTH => (v.take MemWidth.W16.bits).signed
               | .UXTW => (v.take MemWidth.W32.bits).unsigned
               | .SXTW => (v.take MemWidth.W32.bits).signed
               | .UXTX => v.unsigned
               | .SXTX => v.signed
  let shifted := match ext.amount with
                 | .E0 => extended
                 | .E1 => extended <<< 1
                 | .E2 => extended <<< 2
                 | .E3 => extended <<< 3
                 | .E4 => extended <<< 4
  shifted

@[kstep] def BitVec.apply_mem_extend (v : BitVec 64) (ext : MemExtend) :=
  let extended := match ext.type with
               | .UXTW => (v.take MemWidth.W32.bits).unsigned
               | .SXTW => (v.take MemWidth.W32.bits).signed
               | .UXTX => v.unsigned
               | .SXTX => v.signed
  let shifted := match ext.amount with
                 | .E0 => extended
                 | .E1 => extended <<< 1
                 | .E2 => extended <<< 2
                 | .E3 => extended <<< 3
  shifted

@[kstep] def ExtRegExpr.interp (er : ExtRegExpr) (s : Reg64s) (_ : Std.Rco Int64) :=
  (s.getRegOrZr64 er.reg.reg.base).apply_extend er.ext

@[kstep] def MemExtRegExpr.interp (er : MemExtRegExpr) (s : Reg64s) (_ : Std.Rco Int64) :=
  (s.getRegOrZr64 er.reg.reg.base).apply_mem_extend er.ext

@[kstep] def ExtOrImmReg.interp [Labels] {w : RegWidth} (expr : ExtOrImmReg) (s : Reg64s) (p : Std.Rco Int64) : w.type :=
  match expr with
  | .ext e =>
    BitVec.ofInt w.bits (e.interp s p)
  | .imm i =>
    let imm := Int64.toInt (i.imm.interp p)
    match i.shift with
    | .S0 => BitVec.ofInt w.bits (imm)
    | .S12 => BitVec.ofInt w.bits (imm <<< 12)

@[kstep] def ShiftRegExpr.interp {w} (expr : ShiftRegExpr w) (s : Reg64s) (_ : Std.Rco Int64) : w.type :=
  let base := s.getRegOrZr expr.reg
  let amount := (Int64.toInt expr.amount).toNat
  match expr.shift with
  | .LSL => base <<< amount
  | .LSR => base.ushiftRight amount
  | .ASR => base.sshiftRight amount
  | .ROR => base.rotateRight amount

@[kstep] def AddrExpr.eval [Labels] (mem : AddrExpr) (s : MachineData) (p : Std.Rco Int64) : BitVec 64 × MachineData :=
  let base := (s.regs.getRegOrSp mem.base).signed
  match mem.off with
  | .reg r =>
    let off := r.interp s.regs p
    (BitVec.ofInt 64 (base + off), s)
  | .imm i =>
    let off := Int64.toInt (i.imm.interp p)
    let addr := match i.index with
      | some .Post => BitVec.ofInt 64 base
      | _ => BitVec.ofInt 64 (base + off)
    let s' := match i.index with
      | some _ => { s with regs := s.regs.setRegOrSp mem.base (BitVec.ofInt 64 (base + off)) }
      | none => s
    (addr, s')

-- AArch64 mandates 16-byte alignment when accessing memory through SP.
@[kstep] def AddrExpr.checkSPAlignment (mem : AddrExpr) (s : MachineData) (ok : Unit → Effects) : Effects :=
  match mem.base with
  | .SP =>
    if s.regs.getRegOrSp .SP % 16#64 != 0#64 then
      .unaligned_sp (s.regs.getRegOrSp .SP)
    else
      ok ()
  | _ => ok ()

@[kstep] def AddrExpr.interpLoad [Labels] {w : MemWidth} (mem : AddrExpr) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :=
  mem.checkSPAlignment s (fun _unit =>
    let (addr, s') := mem.eval s p
    s'.load addr w ret)

@[kstep] def AddrExpr.interpStore [Labels] {w : MemWidth} (mem : AddrExpr) (s : MachineData) (p : Std.Rco Int64)
    (val : w.type) (next : MachineData → Effects) : Effects :=
  mem.checkSPAlignment s (fun _unit =>
    let (addr, s') := mem.eval s p
    s'.store addr (w := w) val next)

@[kstep] def UnscaledAddrExpr.eval [Labels] (mem : UnscaledAddrExpr) (s : MachineData) (p : Std.Rco Int64) : BitVec 64 :=
  let base := (s.regs.getRegOrSp mem.base).signed
  let off := Int64.toInt (mem.imm.interp p)
  BitVec.ofInt 64 (base + off)

-- AArch64 mandates 16-byte alignment when accessing memory through SP.
@[kstep] def UnscaledAddrExpr.checkSPAlignment (mem : UnscaledAddrExpr) (s : MachineData) (ok : Unit → Effects) : Effects :=
  match mem.base with
  | .SP =>
    if s.regs.getRegOrSp .SP % 16#64 != 0#64 then
      .unaligned_sp (s.regs.getRegOrSp .SP)
    else
      ok ()
  | _ => ok ()

@[kstep] def UnscaledAddrExpr.interpLoad [Labels] {w : MemWidth} (mem : UnscaledAddrExpr) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :=
  mem.checkSPAlignment s (fun _unit =>
    let addr := mem.eval s p
    s.load addr w ret)

@[kstep] def UnscaledAddrExpr.interpStore [Labels] {w : MemWidth} (mem : UnscaledAddrExpr) (s : MachineData) (p : Std.Rco Int64)
    (val : w.type) (next : MachineData → Effects) : Effects :=
  mem.checkSPAlignment s (fun _unit =>
    let addr := mem.eval s p
    s.store addr (w := w) val next)

@[kstep] def Literal.interpLoad [Labels] {w : MemWidth} (expr : Literal) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) : Effects :=
  match expr with
  | .addr addr_expr => -- Load from address.
    let addr_val := Labels.label addr_expr.label
    let addr := BitVec.ofInt 64 (Int64.toInt addr_val)
    s.load addr w ret
  | .pool litpool_expr => -- Bypass loading and return value directly.
    let val := litpool_expr.expr.interp p
    let val_bv : w.type := BitVec.ofInt w.bits (Int64.toInt val)
    ret val_bv s

@[kstep] def AddrOrLit.interpLoad [Labels] {w : MemWidth} (expr : AddrOrLit) (s : MachineData) (p : Std.Rco Int64) (ret : w.type → MachineData → Effects) :=
  match expr with
  | .addr addr_expr => addr_expr.interpLoad s p ret
  | .lit lit_expr => lit_expr.interpLoad s p ret

@[kstep] def MachineData.setRegOrSp (s : MachineData) {w} (r : RegOrSp w) (v : w.type) (ret : MachineData → Effects) : Effects :=
  ret { s with regs := s.regs.setRegOrSp r v }

@[kstep] def MachineData.setRegOrZr (s : MachineData) {w} (r : RegOrZr w) (v : w.type) (ret : MachineData → Effects) : Effects :=
  ret { s with regs := s.regs.setRegOrZr r v }

@[kstep, simp] def CondCode.interp (cc : CondCode) (s : StatusFlags) : Bool := match cc with
  | .EQ => s.z
  | .NE => !s.z
  | .CS => s.c
  | .CC => !s.c
  | .MI => s.n
  | .PL => !s.n
  | .VS => s.v
  | .VC => !s.v
  | .HI => s.c && !s.z
  | .LS => !s.c || s.z
  | .GE => s.n == s.v
  | .LT => s.n != s.v
  | .GT => !s.z && s.n == s.v
  | .LE => s.z || s.n != s.v
  | .AL => true
  | .NV => true -- NV ("never") behaves the same as AL ("always") on AArch64

structure StatusFlags.from_result.Remaining where
  c : Bool
  v : Bool
  deriving Repr, BEq, DecidableEq

@[kstep, simp] def StatusFlags.from_result {w} (result : BitVec w) (f : from_result.Remaining) : StatusFlags :=
  { n := result.msb
    z := result == BitVec.zero _
    c := f.c
    v := f.v }

@[kstep, simp] def StatusFlags.adds {w} (res val1 val2 : BitVec w) : StatusFlags :=
  StatusFlags.from_result res {
    c := res.unsigned != val1.unsigned + val2.unsigned
    v := res.signed != val1.signed + val2.signed }

@[kstep, simp] def StatusFlags.subs {w} (res val1 val2 : BitVec w) : StatusFlags :=
  StatusFlags.from_result res {
    c := res.unsigned == val1.unsigned - val2.unsigned
    v := res.signed != val1.signed - val2.signed }

def StatusFlags.ofNat (nzcv : Nat) : StatusFlags :=
  { n := (nzcv &&& 8) != 0
    z := (nzcv &&& 4) != 0
    c := (nzcv &&& 2) != 0
    v := (nzcv &&& 1) != 0 }

@[kstep, simp] def maskOfLen {w : RegWidth} (len : Nat) : w.type :=
  if len >= w.bits then
    ~~~(0 : w.type)
  else
    ((1 : w.type) <<< len) - 1

@[kstep, simp] def evalUBFM {w : RegWidth} (src : w.type) (immr imms : Nat) : w.type :=
  let immr := immr % w.bits
  let imms := imms % w.bits
  if imms >= immr then
    let len := imms - immr + 1
    let field := (src >>> immr).take len
    field.zeroExtend w.bits
  else
    let len := imms + 1
    let pos := w.bits - immr
    let field := src.take len
    (field.zeroExtend w.bits) <<< pos

@[kstep, simp] def evalSBFM {w : RegWidth} (src : w.type) (immr imms : Nat) : w.type :=
  let immr := immr % w.bits
  let imms := imms % w.bits
  if imms >= immr then
    let len := imms - immr + 1
    let field := (src >>> immr).take len
    field.signExtend w.bits
  else
    let len := imms + 1
    let pos := w.bits - immr
    let field := src.take len
    (field.signExtend (w.bits - pos)).zeroExtend w.bits <<< pos

@[kstep, simp] def evalBFM {w : RegWidth} (dst src : w.type) (immr imms : Nat) : w.type :=
  let immr := immr % w.bits
  let imms := imms % w.bits
  if imms >= immr then
    let len := imms - immr + 1
    let mask : w.type := maskOfLen (w := w) len
    let field := (src >>> immr) &&& mask
    (dst &&& ~~~mask) ||| field
  else
    let len := imms + 1
    let pos := w.bits - immr
    let mask : w.type := (maskOfLen (w := w) len) <<< pos
    let field : w.type := (src &&& maskOfLen (w := w) len) <<< pos
    (dst &&& ~~~mask) ||| field

set_option maxHeartbeats 1000000
@[kstep] def Operation.interp [Labels]
  {w} (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match (generalizing := false) (motive := Operation w → Effects) i with
  | .LDR dst src => src.interpLoad s p (fun val s => s.setRegOrZr dst val next)
  | .STR src dst => dst.interpStore s p (s.regs.getRegOrZr src) next
  | .LDUR dst src => src.interpLoad s p (fun val s => s.setRegOrZr dst val next)
  | .STUR src dst => dst.interpStore s p (s.regs.getRegOrZr src) next
  -- TODO: Architecturally, the memory access ordering of LDP/STP is UNORDERED and can occur
  -- simultaneously as a 128-bit transaction or in any order on hardware. Here we model a specific
  -- sequential order (lower address first, then higher address), which does not necessarily reflect
  -- physical execution order on device memory. (Note: unpredictable cases like identical transfer
  -- registers in LDP or writeback conflicts are statically rejected during parsing).
  | .LDP dst1 dst2 src =>
    src.checkSPAlignment s (fun _unit =>
      let (addr, s') := src.eval s p
      s'.load addr w (fun val1 s'' =>
        s''.load (addr + w.bytesv) w (fun val2 s''' =>
          s'''.setRegOrZr dst1 val1 (fun s'''' =>
            s''''.setRegOrZr dst2 val2 next))))
  | .STP src1 src2 dst =>
    dst.checkSPAlignment s (fun _unit =>
      let val1 := s.regs.getRegOrZr src1
      let val2 := s.regs.getRegOrZr src2
      let (addr, s') := dst.eval s p
      s'.store addr val1 (fun s'' =>
        s''.store (addr + w.bytesv) val2 next))
  | .LDRB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .LDURB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .STRB src dst =>
    dst.interpStore (w := .W8) s p ((s.regs.getRegOrZr src).take MemWidth.W8.bits) next
  | .STURB src dst =>
    dst.interpStore (w := .W8) s p ((s.regs.getRegOrZr src).take MemWidth.W8.bits) next
  | .LDRSB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDURSB dst src =>
    src.interpLoad (w := .W8) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDRH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .LDURH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.zeroExtend RegWidth.W32.bits) next)
  | .STRH src dst =>
    dst.interpStore (w := .W16) s p ((s.regs.getRegOrZr src).take MemWidth.W16.bits) next
  | .STURH src dst =>
    dst.interpStore (w := .W16) s p ((s.regs.getRegOrZr src).take MemWidth.W16.bits) next
  | .LDRSH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDURSH dst src =>
    src.interpLoad (w := .W16) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend w.bits) next)
  | .LDRSW dst src =>
    src.interpLoad (w := .W32) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend RegWidth.W64.bits) next)
  | .LDURSW dst src =>
    src.interpLoad (w := .W32) s p (fun val s' =>
      s'.setRegOrZr dst (val.signExtend RegWidth.W64.bits) next)
  | .LDPSW dst1 dst2 src =>
    src.checkSPAlignment s (fun _unit =>
      let (addr, s') := src.eval s p
      s'.load addr .W32 (fun val1 s'' =>
        s''.load (addr + MemWidth.W32.bytesv) .W32 (fun val2 s''' =>
          s'''.setRegOrZr dst1 (val1.signExtend RegWidth.W64.bits) (fun s'''' =>
            s''''.setRegOrZr dst2 (val2.signExtend RegWidth.W64.bits) next))))
  | .ADD_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    s.setRegOrSp dst res next
  | .ADD_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    s.setRegOrZr dst res next
  | .ADDS_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    { s with status := StatusFlags.adds res val1 val2 }.setRegOrZr dst res next
  | .ADDS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 + val2
    { s with status := StatusFlags.adds res val1 val2 }.setRegOrZr dst res next
  | .SUB_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    s.setRegOrSp dst res next
  | .SUB_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    s.setRegOrZr dst res next
  | .SUBS_e dst src1 src2 =>
    let val1 := s.regs.getRegOrSp src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    { s with status := StatusFlags.subs res val1 val2 }.setRegOrZr dst res next
  | .SUBS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 - val2
    { s with status := StatusFlags.subs res val1 val2 }.setRegOrZr dst res next
  | .ADC dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let carry : w.type := s.status.c
    let res := val1 + val2 + carry
    s.setRegOrZr dst res next
  | .ADCS dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let carry : w.type := s.status.c
    let res := val1 + val2 + carry
    let carry_int : Int := if s.status.c then 1 else 0
    let status := StatusFlags.from_result res {
      c := res.unsigned != val1.unsigned + val2.unsigned + carry_int
      v := res.signed != val1.signed + val2.signed + carry_int }
    { s with status }.setRegOrZr dst res next
  | .SBC dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let borrow : w.type := !s.status.c
    let res := val1 - val2 - borrow
    s.setRegOrZr dst res next
  | .SBCS dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let borrow : w.type := !s.status.c
    let res := val1 - val2 - borrow
    let borrow_int : Int := if s.status.c then 0 else 1
    let status := StatusFlags.from_result res {
      c := val1.unsigned >= val2.unsigned + borrow_int
      v := res.signed != val1.signed - val2.signed - borrow_int }
    { s with status }.setRegOrZr dst res next
  | .MADD dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := val1 * val2 + val3
    s.setRegOrZr dst res next
  | .MSUB dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := val3 - val1 * val2
    s.setRegOrZr dst res next
  | .SMULH dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let prod := val1.signed * val2.signed
    let res := (BitVec.ofInt (RegWidth.W64.bits + RegWidth.W64.bits) prod).extractLsb' RegWidth.W64.bits RegWidth.W64.bits
    s.setRegOrZr dst res next
  | .UMULH dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let prod := val1.unsigned * val2.unsigned
    let res := (BitVec.ofInt (RegWidth.W64.bits + RegWidth.W64.bits) prod).extractLsb' RegWidth.W64.bits RegWidth.W64.bits
    s.setRegOrZr dst res next
  | .SDIV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let res := if val2 == 0 then (0 : w.type) else val1.sdiv val2
    s.setRegOrZr dst res next
  | .UDIV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let res := if val2 == 0 then (0 : w.type) else val1 / val2
    s.setRegOrZr dst res next
  | .SMADDL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val1.signed * val2.signed + val3.signed)
    s.setRegOrZr dst res next
  | .UMADDL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val1.unsigned * val2.unsigned + val3.unsigned)
    s.setRegOrZr dst res next
  | .SMSUBL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val3.signed - val1.signed * val2.signed)
    s.setRegOrZr dst res next
  | .UMSUBL dst src1 src2 src3 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let val3 := s.regs.getRegOrZr src3
    let res := BitVec.ofInt RegWidth.W64.bits (val3.unsigned - val1.unsigned * val2.unsigned)
    s.setRegOrZr dst res next
  | .AND_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 &&& val2
    s.setRegOrSp dst res next
  | .AND_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& val2
    s.setRegOrZr dst res next
  | .ANDS_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 &&& val2
    let flags := StatusFlags.from_result res { c := false, v := false }
    { s with status := flags }.setRegOrZr dst res next
  | .ANDS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& val2
    let flags := StatusFlags.from_result res { c := false, v := false }
    { s with status := flags }.setRegOrZr dst res next
  | .ORR_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 ||| val2
    s.setRegOrSp dst res next
  | .ORR_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ||| val2
    s.setRegOrZr dst res next
  | .ORN_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ||| ~~~val2
    s.setRegOrZr dst res next
  | .EOR_i dst src1 imm =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := BitVec.ofInt w.bits (Int64.toInt (imm.interp p))
    let res := val1 ^^^ val2
    s.setRegOrSp dst res next
  | .EOR_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ^^^ val2
    s.setRegOrZr dst res next
  | .BIC_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& ~~~val2
    s.setRegOrZr dst res next
  | .EON_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 ^^^ ~~~val2
    s.setRegOrZr dst res next
  | .BICS_s dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := src2.interp s.regs p
    let res := val1 &&& ~~~val2
    let status' := StatusFlags.from_result res { c := false, v := false }
    { s with status := status' }.setRegOrZr dst res next
  | .BFM dst src immr imms =>
    let val_dst := s.regs.getRegOrZr dst
    let val_src := s.regs.getRegOrZr src
    let res := evalBFM val_dst val_src immr imms
    s.setRegOrZr dst res next
  | .SBFM dst src immr imms =>
    let val_src := s.regs.getRegOrZr src
    let res := evalSBFM val_src immr imms
    s.setRegOrZr dst res next
  | .UBFM dst src immr imms =>
    let val_src := s.regs.getRegOrZr src
    let res := evalUBFM val_src immr imms
    s.setRegOrZr dst res next
  | .CLZ dst src =>
    let val := s.regs.getRegOrZr src
    s.setRegOrZr dst val.clz next
  | .CLS dst src =>
    let val := s.regs.getRegOrZr src
    let res := (if val.msb then (~~~val).clz else val.clz) - 1#w.bits
    s.setRegOrZr dst res next
  | .RBIT dst src =>
    let val := s.regs.getRegOrZr src
    s.setRegOrZr dst val.reverse next
  | .REV dst src =>
    let val := s.regs.getRegOrZr src
    let res : w.type := match w, val with
      | .W32, v =>
        let step1 := ((v &&& 0x00FF00FF#32) <<< 8) ||| ((v &&& 0xFF00FF00#32) >>> 8)
        ((step1 &&& 0x0000FFFF#32) <<< 16) ||| ((step1 &&& 0xFFFF0000#32) >>> 16)
      | .W64, v =>
        let step1 := ((v &&& 0x00FF00FF00FF00FF#64) <<< 8) ||| ((v &&& 0xFF00FF00FF00FF00#64) >>> 8)
        let step2 := ((step1 &&& 0x0000FFFF0000FFFF#64) <<< 16) ||| ((step1 &&& 0xFFFF0000FFFF0000#64) >>> 16)
        ((step2 &&& 0x00000000FFFFFFFF#64) <<< 32) ||| ((step2 &&& 0xFFFFFFFF00000000#64) >>> 32)
    s.setRegOrZr dst res next
  | .REV16 dst src =>
    let val := s.regs.getRegOrZr src
    let res := ((val &&& 0x00FF00FF00FF00FF#w.bits) <<< 8) ||| ((val &&& 0xFF00FF00FF00FF00#w.bits) >>> 8)
    s.setRegOrZr dst res next
  | .REV32 dst src =>
    let val := s.regs.getRegOrZr src
    let step1 := ((val &&& 0x00FF00FF00FF00FF#64) <<< 8) ||| ((val &&& 0xFF00FF00FF00FF00#64) >>> 8)
    let res := ((step1 &&& 0x0000FFFF0000FFFF#64) <<< 16) ||| ((step1 &&& 0xFFFF0000FFFF0000#64) >>> 16)
    s.setRegOrZr dst res next
  | .EXTR dst src1 src2 lsb =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let lsb := lsb % w.bits
    let res := if lsb == 0 then val2 else (val1 <<< (w.bits - lsb)) ||| (val2 >>> lsb)
    s.setRegOrZr dst res next
  | .MOVZ dst imm shift =>
    let val16 := (BitVec.ofInt w.bits (Int64.toInt (imm.interp p))) &&& 0xFFFF#w.bits
    let res := val16 <<< shift.toNat
    s.setRegOrZr dst res next
  | .MOVK dst imm shift =>
    let oldVal := s.regs.getRegOrZr dst
    let mask := ~~~(0xFFFF#w.bits <<< shift.toNat)
    let val16 := (BitVec.ofInt w.bits (Int64.toInt (imm.interp p))) &&& 0xFFFF#w.bits
    let res := (oldVal &&& mask) ||| (val16 <<< shift.toNat)
    s.setRegOrZr dst res next
  | .MOVN dst imm shift =>
    let val16 := (BitVec.ofInt w.bits (Int64.toInt (imm.interp p))) &&& 0xFFFF#w.bits
    let res := ~~~(val16 <<< shift.toNat)
    s.setRegOrZr dst res next
  | .LSLV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1 <<< shift
    s.setRegOrZr dst res next
  | .LSRV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1.ushiftRight shift
    s.setRegOrZr dst res next
  | .ASRV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1.sshiftRight shift
    s.setRegOrZr dst res next
  | .RORV dst src1 src2 =>
    let val1 := s.regs.getRegOrZr src1
    let val2 := s.regs.getRegOrZr src2
    let shift := val2.toNat % w.bits
    let res := val1.rotateRight shift
    s.setRegOrZr dst res next
  | .CSEL dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else s.regs.getRegOrZr src2
    s.setRegOrZr dst val next
  | .CSINC dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else s.regs.getRegOrZr src2 + 1#w.bits
    s.setRegOrZr dst val next
  | .CSINV dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else ~~~(s.regs.getRegOrZr src2)
    s.setRegOrZr dst val next
  | .CSNEG dst src1 src2 cond =>
    let val := if cond.interp s.status then s.regs.getRegOrZr src1 else -(s.regs.getRegOrZr src2)
    s.setRegOrZr dst val next
  | .CCMP_reg src1 src2 nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := s.regs.getRegOrZr src2
        let res := val1 - val2
        StatusFlags.subs res val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .CCMP_imm src1 imm nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := BitVec.ofNat w.bits imm
        let res := val1 - val2
        StatusFlags.subs res val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .CCMN_reg src1 src2 nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := s.regs.getRegOrZr src2
        let res := val1 + val2
        StatusFlags.adds res val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .CCMN_imm src1 imm nzcv cond =>
    let status' := if cond.interp s.status then
        let val1 := s.regs.getRegOrZr src1
        let val2 := BitVec.ofNat w.bits imm
        let res := val1 + val2
        StatusFlags.adds res val1 val2
      else
        StatusFlags.ofNat nzcv
    next { s with status := status' }
  | .ADR dst target =>
    let val := match target with
      | .int64 imm => BitVec.ofInt 64 (Int64.toInt p.lower + Int64.toInt imm)
      | _ => BitVec.ofInt 64 (Int64.toInt (target.interp p))
    s.setRegOrZr dst val next
  | .ADRP dst target =>
    let val := match target with
      | .int64 imm => BitVec.ofInt 64 (Int64.toInt p.lower + Int64.toInt imm)
      | _ => BitVec.ofInt 64 (Int64.toInt (target.interp p))
    s.setRegOrZr dst (val &&& ~~~0xFFF#64) next
  | .B target =>
    jmp (target.evalBranchTarget p) s
  | .B_cond cond target =>
    if cond.interp s.status then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .BL target =>
    let lr_val := BitVec.ofInt 64 (Int64.toInt p.upper)
    s.setRegOrZr RegOrZr.X30 lr_val (fun s' => jmp (target.evalBranchTarget p) s')
  | .BLR target =>
    let lr_val := BitVec.ofInt 64 (Int64.toInt p.upper)
    let target_val := Int64.ofInt (s.regs.getRegOrZr target).signed
    s.setRegOrZr RegOrZr.X30 lr_val (fun s' => jmp target_val s')
  | .BR target =>
    let target_val := Int64.ofInt (s.regs.getRegOrZr target).signed
    jmp target_val s
  | .RET target =>
    let target_val := Int64.ofInt (s.regs.getRegOrZr target).signed
    jmp target_val s
  | .CBZ reg target =>
    let val := s.regs.getRegOrZr reg
    if val == 0 then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .CBNZ reg target =>
    let val := s.regs.getRegOrZr reg
    if val != 0 then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .TBZ reg bit target =>
    let val := s.regs.getRegOrZr reg
    if val.getLsbD bit == false then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .TBNZ reg bit target =>
    let val := s.regs.getRegOrZr reg
    if val.getLsbD bit == true then
      jmp (target.evalBranchTarget p) s
    else
      next s
  | .NOP => next s

@[kstep] def Instr.interp [Labels]
  (i : Instr) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  require_exec_access p (fun _unit =>
    Operation.interp (w := i.operation_size) i.operation p s next jmp)

@[kstep] def Directive.interp [Labels]
  (d : Directive) (s : MachineData) (p : Std.Rco Int64)
  (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) : Effects :=
  match d with
  | .label _ => next s
  | .instr i => i.interp s p next jmp
  | .byteArray _ => .unimplemented s!"Unimplemented: execution reached data block at {p.1}"

def Directives.interp [Labels]
  (ds : List (Kraken.Sized Directive)) (s : MachineData) (pc : Int64)
  (ret : Int64 → MachineData → Effects) : Effects :=
  match ds with
  | [] => ret pc s
  | {directive, size := sz} :: ds =>
    directive.interp s (.mk pc (pc+.ofNat sz)) (jmp:=ret) (next := (fun s =>
    interp ds s (pc+.ofNat sz) ret))

abbrev Layout := Kraken.Layout Directive

@[reducible]
def Executable.labels (e : Executable) : Labels :=
  { label l := (e.withAddresses.findSome?
      (fun {directive, addr, ..} => if directive = .label l then .some addr else .none)).getD (-1) }

def Executable.directivesFromLabel (e : Executable) (l : Label) : List (Kraken.Sized Directive) :=
  e.program.dropWhile (·.directive != .label l)

def Executable.step (e : Executable) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let := Executable.labels e
  Directives.interp (e.directivesAtAddress s.pc) s.data s.pc (fun pc s => ret ⟨s, pc⟩)

def Executable.straightline (e : Executable) (s : MachineState) (ret : MachineState → Effects) : Effects :=
  let := Executable.labels e
  Directives.interp (e.directivesFromAddress s.pc) s.data s.pc (fun pc s => ret ⟨s, pc⟩)

-- -- Concrete evaluators for expedient testing

partial def Executable.eval (e : Executable) (s : MachineState) (until_ : MachineState → Bool) : Except String (MachineState) :=
  if until_ s then .ok s else handleEffects (Executable.straightline e s .done)
where
  handleEffects es :=
    match es with
    | .done s => eval e s until_
    | .unimplemented msg => .error msg
    | .require_read_access _ _ ok => handleEffects (ok ())
    | .require_write_access _ _ ok => handleEffects (ok ())
    | .require_exec_access _ ok => handleEffects (ok ())
    | .nonmem_load _ addr _ _ => .error s!"Load at unmapped address {repr addr}"
    | .nonmem_store _ addr _ _ => .error s!"Store at unmapped address {repr addr}"
    | .unaligned_sp sp => .error s!"SP={sp} (is not 16-byte aligned)"
    | @Effects.undefined _ t cont => handleEffects (cont (t.from_hash (hash s.1.regs)))

def Directive.fakeSize (d : Directive) : Nat :=
  match d with
  | .instr _ => 4
  | .label _ => 0
  | .byteArray bs => bs.size

def Program.fakeLayout (prog : Program) : Executable :=
  let : Inhabited Directive := .mk (.byteArray (.mk #[]))
  let h := hash prog;
  let layout : Layout := { start := h.toInt64<<<16, size i := prog[i]!.fakeSize }
  layout prog

abbrev eval [layout : Layout] (prog : Program) := Executable.eval (layout prog)

/-- info: Except.ok 58 -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr ⟨.W64, .LDR .X1 (.addr { base := .SP, off := 0 })⟩,
    .instr ⟨.W64, .ADD_e .X1 .X1 0x10⟩,
    .instr ⟨.W64, .STR .X1 { base := .SP, off := 0 }⟩,
    .instr ⟨.W64, .LDR .X2 (.addr { base := .SP, off := 0 })⟩]
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 42, regs := {SP := 0x100} }
  (Executable.eval exe {data, pc := start} (fun st => (exe.directivesFromAddress st.pc).isEmpty)).bind (fun s => .ok s.1.regs.X2)

/-- info: Except.ok (42, 264) -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr ⟨.W64, .LDR .X1 (.addr { base := .SP, off := .imm { imm := 8, index := some .Pre } })⟩ ]
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x108 8 42, regs := { SP := 0x100 } }
  (Executable.eval exe {data, pc := start} (fun st => (exe.directivesFromAddress st.pc).isEmpty)).bind (fun s => .ok (s.1.regs.X1, s.1.regs.SP))

/-- info: Except.ok (42, 264) -/
#guard_msgs in
#eval
  let exe := Program.fakeLayout [
    .label "main",
    .instr ⟨.W64, .STR .X1 { base := .SP, off := .imm { imm := 8, index := some .Post } }⟩ ]
  let start := (Executable.labels exe).label "main"
  let data : MachineData := { dmem := Mem.storeInt {} 0x100 8 0, regs := { SP := 0x100, X1 := 42 } }
  (Executable.eval exe {data, pc := start} (fun st => (exe.directivesFromAddress st.pc).isEmpty)).bind (fun s =>
    match Mem.loadInt s.1.dmem 0x100 8 with
    | some v => .ok (v, s.1.regs.SP)
    | none => .error "Memory store failed"
  )
