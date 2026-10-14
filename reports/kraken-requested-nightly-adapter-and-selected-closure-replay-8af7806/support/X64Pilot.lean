module
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.SeparationMem
import Kraken.Tactics

open Kraken.X64.Parser

def addBody : Program := parse("leaq (%rdi,%rsi,1), %rax")
def addReturn : Program := parse("leaq (%rdi,%rsi,1), %rax\nret")

def bodyState (d : MachineData) : MachineData :=
  { d with regs := { d.regs with rax := d.regs.rdi + d.regs.rsi } }

def returnState (d : MachineData) : MachineData :=
  { d with regs := { d.regs with rax := d.regs.rdi + d.regs.rsi, rsp := d.regs.rsp + 8 } }

theorem addBody_correct [layout : Layout] (d : MachineData) :
    straightlineStep (layout addBody) ⟨d, layout.start⟩
      (fun s' => s'.data = bodyState d) := by
  kprologue addBody with d
  sym => kstep; tactic =>
  simp (config := { zetaDelta := true }) [bodyState, BitVec.ofInt_add, BitVec.ofInt_toInt]

theorem addReturn_of_load [layout : Layout] (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra) :
    straightlineStep (layout addReturn) ⟨d, layout.start⟩
      (fun s' => s'.data = returnState d ∧ s'.pc.toBitVec = BitVec.ofInt 64 ra) := by
  unfold straightlineStep Executable.straightline
  rw [Kraken.Executable.directivesFromStart]
  simp [addReturn, Directives.interp, Directive.interp, Instr.interp,
    Operation.interp, Effects.All, MachineData.load, hload,
    MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get64,
    AddrExpr.interp, ConstExpr.interp, returnState,
    Width.bits, Width.bytes, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.take]

theorem addReturn_correct [layout : Layout] (d : MachineData) (ra : UInt64)
    (R : DataMem → Prop)
    (hsep : d.dmem =⋆ Eq (ra.At d.regs.rsp.toBitVec) ⋆ R) :
    straightlineStep (layout addReturn) ⟨d, layout.start⟩
      (fun s' => s'.data = returnState d ∧ s'.pc.toBitVec = ra.toBitVec) := by
  have hload := Mem.loadInt_sep ra.toBytes d.regs.rsp.toBitVec 8 R d.dmem
    hsep (UInt64.toBytes_length ra) (by decide)
  have result := addReturn_of_load d (Int.ofBytes ra.toBytes) hload
  simpa only [UInt64.toBytes, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] using result

theorem addReturn_iff [layout : Layout] (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra) (post : MachineState → Prop) :
    straightlineStep (layout addReturn) ⟨d, layout.start⟩ post ↔
      post ⟨returnState d, Int64.ofBitVec (BitVec.ofInt 64 ra)⟩ := by
  unfold straightlineStep Executable.straightline
  rw [Kraken.Executable.directivesFromStart]
  simp [addReturn, Directives.interp, Directive.interp, Instr.interp,
    Operation.interp, Effects.All, MachineData.load, hload,
    MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get64,
    AddrExpr.interp, ConstExpr.interp, returnState,
    Width.bits, Width.bytes, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.take]

theorem wrong_return_rejected [layout : Layout] (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (wrong : BitVec 64) (hwrong : BitVec.ofInt 64 ra ≠ wrong) :
    ¬ straightlineStep (layout addReturn) ⟨d, layout.start⟩
      (fun s' => s'.pc.toBitVec = wrong) := by
  rw [addReturn_iff d ra hload]
  simpa using hwrong

def clobberReturn : Program := parse("leaq (%rdi,%rsi,1), %rax\nmovq $99, %rbx\nret")

theorem hidden_clobber_rejected [layout : Layout] (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (hclobber : d.regs.rbx ≠ 99) :
    ¬ straightlineStep (layout clobberReturn) ⟨d, layout.start⟩
      (fun s' => s'.data = returnState d) := by
  unfold straightlineStep Executable.straightline
  rw [Kraken.Executable.directivesFromStart]
  simp [clobberReturn, Directives.interp, Directive.interp, Instr.interp,
    Operation.interp, Effects.All, MachineData.load, hload,
    MachineData.setReg, MachineData.set, Operand.interp,
    Reg64s.set, Reg64s.set64, Reg64s.get64,
    AddrExpr.interp, ConstExpr.interp, returnState,
    Width.bits, Width.bytes, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.take]
  exact Ne.symm hclobber

theorem result_is_wrapping_sum (d : MachineData) :
    (returnState d).regs.rax.toNat = (d.regs.rdi.toNat + d.regs.rsi.toNat) % 2 ^ 64 := by
  exact UInt64.toNat_add d.regs.rdi d.regs.rsi

def PermissionAll (readable writable : BitVec 64 → Nat → Prop)
    (executable : Std.Rco Int64 → Prop) (post : MachineState → Prop) : Effects → Prop
  | .done s => post s
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined _ _ k => ∀ v, PermissionAll readable writable executable post (k v)
  | .require_read_access a w k => readable a w.bytes ∧ PermissionAll readable writable executable post (k ())
  | .require_write_access a w k => writable a w.bytes ∧ PermissionAll readable writable executable post (k ())
  | .require_exec_access p k => executable p ∧ PermissionAll readable writable executable post (k ())

def firstCodeRange [layout : Layout] : Std.Rco Int64 :=
  ⟨layout.start, layout.start + Int64.ofNat (layout.size 0)⟩

def secondCodeRange [layout : Layout] : Std.Rco Int64 :=
  let pc := layout.start + Int64.ofNat (layout.size 0)
  ⟨pc, pc + Int64.ofNat (layout.size 1)⟩

theorem addReturn_permission_iff [layout : Layout] (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (readable writable : BitVec 64 → Nat → Prop)
    (executable : Std.Rco Int64 → Prop) (post : MachineState → Prop) :
    PermissionAll readable writable executable post
      (Executable.straightline (layout addReturn) ⟨d, layout.start⟩ .done) ↔
      executable firstCodeRange ∧ executable secondCodeRange ∧
      readable d.regs.rsp.toBitVec 8 ∧
      post ⟨returnState d, Int64.ofBitVec (BitVec.ofInt 64 ra)⟩ := by
  unfold Executable.straightline
  rw [Kraken.Executable.directivesFromStart]
  simp [addReturn, Directives.interp, Directive.interp, Instr.interp,
    Operation.interp, PermissionAll, MachineData.load, hload,
    MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get64,
    AddrExpr.interp, ConstExpr.interp, returnState, firstCodeRange, secondCodeRange,
    Width.bits, Width.bytes, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.take]

theorem forbidden_stack_read_rejected [layout : Layout] (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (readable writable : BitVec 64 → Nat → Prop)
    (executable : Std.Rco Int64 → Prop) (post : MachineState → Prop)
    (hforbid : ¬ readable d.regs.rsp.toBitVec 8) :
    ¬ PermissionAll readable writable executable post
      (Executable.straightline (layout addReturn) ⟨d, layout.start⟩ .done) := by
  rw [addReturn_permission_iff d ra hload]
  intro h
  exact hforbid h.2.2.1

theorem forbidden_exec_rejected [layout : Layout] (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (readable writable : BitVec 64 → Nat → Prop)
    (executable : Std.Rco Int64 → Prop) (post : MachineState → Prop)
    (hforbid : ¬ executable firstCodeRange) :
    ¬ PermissionAll readable writable executable post
      (Executable.straightline (layout addReturn) ⟨d, layout.start⟩ .done) := by
  rw [addReturn_permission_iff d ra hload]
  intro h
  exact hforbid h.1

theorem bounded_access_positive [layout : Layout] (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (readable writable : BitVec 64 → Nat → Prop)
    (executable : Std.Rco Int64 → Prop) (post : MachineState → Prop)
    (hcode1 : executable firstCodeRange) (hcode2 : executable secondCodeRange)
    (hread : readable d.regs.rsp.toBitVec 8)
    (hpost : post ⟨returnState d, Int64.ofBitVec (BitVec.ofInt 64 ra)⟩) :
    PermissionAll readable writable executable post
      (Executable.straightline (layout addReturn) ⟨d, layout.start⟩ .done) := by
  rw [addReturn_permission_iff d ra hload]
  exact ⟨hcode1, hcode2, hread, hpost⟩

def withinRegion (base size : Nat) (addr : BitVec 64) (width : Nat) : Prop :=
  base ≤ addr.toNat ∧ addr.toNat + width ≤ base + size ∧ addr.toNat + width ≤ 2 ^ 64

theorem seven_byte_stack_prefix_rejected [layout : Layout] (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (writable : BitVec 64 → Nat → Prop) (executable : Std.Rco Int64 → Prop)
    (post : MachineState → Prop) :
    ¬ PermissionAll (withinRegion d.regs.rsp.toBitVec.toNat 7) writable executable post
      (Executable.straightline (layout addReturn) ⟨d, layout.start⟩ .done) := by
  apply forbidden_stack_read_rejected d ra hload
  intro h
  unfold withinRegion at h
  omega

theorem eight_byte_stack_region_positive [layout : Layout] (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (writable : BitVec 64 → Nat → Prop) (executable : Std.Rco Int64 → Prop)
    (post : MachineState → Prop)
    (hnowrap : d.regs.rsp.toBitVec.toNat + 8 ≤ 2 ^ 64)
    (hcode1 : executable firstCodeRange) (hcode2 : executable secondCodeRange)
    (hpost : post ⟨returnState d, Int64.ofBitVec (BitVec.ofInt 64 ra)⟩) :
    PermissionAll (withinRegion d.regs.rsp.toBitVec.toNat 8) writable executable post
      (Executable.straightline (layout addReturn) ⟨d, layout.start⟩ .done) := by
  apply bounded_access_positive d ra hload _ _ _ _ hcode1 hcode2 _ hpost
  exact ⟨Nat.le_refl _, Nat.le_refl _, hnowrap⟩

def hostProgram : Program := parse("nop\nleaq (%rdi,%rsi,1), %rax\nret\nnop")

abbrev hostLayout : Layout := { start := 4096, size := fun i => if i = 1 then 4 else 1 }
def hostLea : Directive := .instr (.regular .W64 .W64 (.lea (.low .rax .W64)
  { base := some (.reg .rdi), idx := some { reg := .rsi, scale := .W8 } }))
def hostRet : Directive := .instr (.regular .W64 .W64 .ret)
def hostNop : Directive := .instr (.regular .W64 .W64 (.nop 1))
def fixedHost : Executable := { startAddr := 4096, program := [
  ⟨hostNop, 1⟩, ⟨hostLea, 4⟩, ⟨hostRet, 1⟩, ⟨hostNop, 1⟩] }

theorem fixedHost_program_identity : fixedHost.program.map (·.directive) = hostProgram := by rfl
local instance : Layout := hostLayout

theorem host_addReturn_iff (host : Executable) (hidentity : host = fixedHost)
    (d : MachineData) (pc : Int64) (hentry : pc = 4097) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (post : MachineState → Prop) :
    straightlineStep host ⟨d, pc⟩ post ↔
      post ⟨returnState d, Int64.ofBitVec (BitVec.ofInt 64 ra)⟩ := by
  subst host pc
  simp [straightlineStep, Executable.straightline, fixedHost, hostLea, hostRet, hostNop,
    Kraken.Executable.directivesFromAddress, Kraken.Executable.withAddresses.eq_def,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    Effects.All, MachineData.load, hload, MachineData.setReg,
    Reg64s.set, Reg64s.set64, Reg64s.get64, AddrExpr.interp, ConstExpr.interp,
    returnState, Width.bits, Width.bytes, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.take]

theorem host_entry_step_iff (d : MachineData) (post : MachineState → Prop) :
    step1 fixedHost ⟨d, 4097⟩ post ↔ post ⟨bodyState d, 4101⟩ := by
  simp [step1, Executable.step, fixedHost, hostLea, hostRet, hostNop,
    Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses.eq_def,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    Effects.All, MachineData.setReg, Reg64s.set, Reg64s.set64, Reg64s.get64,
    AddrExpr.interp, ConstExpr.interp, bodyState, Width.bits, Width.bytes,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_add, BitVec.take]

def retStateOnly (d : MachineData) : MachineData :=
  { d with regs := { d.regs with rsp := d.regs.rsp + 8 } }

theorem host_ret_step_iff (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (post : MachineState → Prop) :
    step1 fixedHost ⟨d, 4101⟩ post ↔
      post ⟨retStateOnly d, Int64.ofBitVec (BitVec.ofInt 64 ra)⟩ := by
  simp [step1, Executable.step, fixedHost, hostLea, hostRet, hostNop,
    Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses.eq_def,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    Effects.All, MachineData.load, hload, Reg64s.set64, Reg64s.get64,
    retStateOnly, Width.bits, Width.bytes]

theorem host_two_step_composition (host : Executable) (hidentity : host = fixedHost)
    (d : MachineData) (pc : Int64) (hentry : pc = 4097) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (post : MachineState → Prop)
    (hpost : post ⟨returnState d, Int64.ofBitVec (BitVec.ofInt 64 ra)⟩) :
    Eventually (step1 host) post ⟨d, pc⟩ := by
  subst host pc
  apply step_cps
  rw [host_entry_step_iff]
  apply step_cps
  rw [host_ret_step_iff (bodyState d) ra hload]
  apply Eventually.done
  simpa only [retStateOnly, bodyState, returnState] using hpost

theorem host_permission_iff (d : MachineData) (ra : Int)
    (hload : Mem.loadInt d.dmem d.regs.rsp.toBitVec 8 = some ra)
    (readable writable : BitVec 64 → Nat → Prop)
    (executable : Std.Rco Int64 → Prop) (post : MachineState → Prop) :
    PermissionAll readable writable executable post
      (Executable.straightline fixedHost ⟨d, 4097⟩ .done) ↔
      executable ⟨4097, 4101⟩ ∧ executable ⟨4101, 4102⟩ ∧
      readable d.regs.rsp.toBitVec 8 ∧
      post ⟨returnState d, Int64.ofBitVec (BitVec.ofInt 64 ra)⟩ := by
  simp [Executable.straightline, fixedHost, hostLea, hostRet, hostNop,
    Kraken.Executable.directivesFromAddress, Kraken.Executable.withAddresses.eq_def,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    PermissionAll, MachineData.load, hload, MachineData.setReg,
    Reg64s.set, Reg64s.set64, Reg64s.get64, AddrExpr.interp, ConstExpr.interp,
    returnState, Width.bits, Width.bytes, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.take]

#print axioms result_is_wrapping_sum
#print axioms addBody_correct
#print axioms addReturn_of_load
#print axioms addReturn_correct
#print axioms addReturn_iff
#print axioms wrong_return_rejected
#print axioms hidden_clobber_rejected
#print axioms addReturn_permission_iff
#print axioms forbidden_stack_read_rejected
#print axioms forbidden_exec_rejected
#print axioms bounded_access_positive
#print axioms seven_byte_stack_prefix_rejected
#print axioms eight_byte_stack_region_positive
#print axioms host_addReturn_iff
#print axioms host_entry_step_iff
#print axioms host_ret_step_iff
#print axioms host_two_step_composition
#print axioms host_permission_iff
#print axioms fixedHost_program_identity
