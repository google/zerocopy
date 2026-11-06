module
public import Kraken.AArch64.OmniSemantics
public import Kraken.SeparationMem

@[expose] public section

/- A small byte-driven adapter. The encoding predicates below are an owned
   transcription of the selected A64 encoding fields, not an imported Arm theorem. -/
namespace CheckedByteLeaf

inductive Decoded where
  | loadByte (offset : Nat)
  | retLR
  deriving DecidableEq, Repr

def ldrbBase : Nat := 0x39400000
def retWord : Nat := 0xd65f03c0

/-- The independent field presentation: size=00, V=0, opc=01,
    unsigned-immediate load/store class; Rn=0, Rt=0. -/
def LoadFields (word offset : Nat) : Prop :=
  offset < 4096 ∧ word = 0x39400000 + offset * 1024

def decodeWord (word : Nat) : Option Decoded :=
  if word = retWord then some .retLR
  else if word % 1024 = 0 ∧ word / 4194304 = 229 then
    some (.loadByte ((word / 1024) % 4096))
  else none

theorem decode_load_iff (word offset : Nat) :
    decodeWord word = some (.loadByte offset) ↔ LoadFields word offset := by
  unfold decodeWord LoadFields retWord
  split <;> rename_i h
  · constructor
    · intro he
      cases he
    · rintro ⟨hb,he⟩
      omega
  · split <;> rename_i hf
    · simp only [Option.some.injEq, Decoded.loadByte.injEq]
      have hm := Nat.mod_lt (word / 1024) (by decide : 0 < 4096)
      constructor
      · intro heq
        rcases hf with ⟨ha,hb⟩
        omega
      · rintro ⟨ha,hb⟩
        omega
    · simp only [reduceCtorEq, false_iff]
      intro hc
      apply hf
      rcases hc with ⟨ha,hb⟩
      constructor <;> omega

theorem decode_ret_iff (word : Nat) :
    decodeWord word = some .retLR ↔ word = retWord := by
  unfold decodeWord
  split <;> simp_all

def wordLE (a b c d : UInt8) : Nat :=
  a.toNat + 256*b.toNat + 65536*c.toNat + 16777216*d.toNat

def encodeLE (word : Nat) : List UInt8 :=
  [UInt8.ofNat word, UInt8.ofNat (word / 256),
   UInt8.ofNat (word / 65536), UInt8.ofNat (word / 16777216)]

theorem wordLE_bound (a b c d : UInt8) : wordLE a b c d < 4294967296 := by
  have := a.toNat_lt
  have := b.toNat_lt
  have := c.toNat_lt
  have := d.toNat_lt
  unfold wordLE
  omega

theorem encodeLE_wordLE (a b c d : UInt8) :
    encodeLE (wordLE a b c d) = [a,b,c,d] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  simp only [encodeLE, List.cons.injEq, and_true]
  constructor
  · apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', wordLE]
    omega
  constructor
  · apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', wordLE]
    omega
  constructor
  · apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', wordLE]
    omega
  · apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat', wordLE]
    omega

def decodeLeaf : List UInt8 → Option Nat
  | [a,b,c,d,e,f,g,h] =>
    match decodeWord (wordLE a b c d), decodeWord (wordLE e f g h) with
    | some (.loadByte off), some .retLR => some off
    | _, _ => none
  | _ => none

def canonicalBytes : List UInt8 := [0x00,0x00,0x40,0x39,0xc0,0x03,0x5f,0xd6]

/-- Executable contract checker. Offset zero is part of the one-byte resource contract. -/
def accept (bytes : List UInt8) : Bool := decodeLeaf bytes == some 0

theorem canonical_accepted : accept canonicalBytes = true := by decide

theorem decodeLeaf_fields (a b c d e f g h : UInt8) (off : Nat) :
    decodeLeaf [a,b,c,d,e,f,g,h] = some off ↔
      LoadFields (wordLE a b c d) off ∧ wordLE e f g h = retWord := by
  rw [← decode_load_iff, ← decode_ret_iff]
  unfold decodeLeaf
  cases hl : decodeWord (wordLE a b c d) with
  | none => simp [hl]
  | some load =>
    cases load <;> cases hr : decodeWord (wordLE e f g h) with
    | none => simp [hl,hr]
    | some r => cases r <;> simp_all

theorem accepted_iff_canonical (bytes : List UInt8) :
    accept bytes = true ↔ bytes = canonicalBytes := by
  constructor
  · intro ha
    have hd : decodeLeaf bytes = some 0 := by simpa [accept] using ha
    unfold decodeLeaf at hd
    split at hd
    next a b c d e f g h =>
      have hf := (decodeLeaf_fields a b c d e f g h 0).mp hd
      rcases hf with ⟨⟨_,hl⟩,hr⟩
      have ha := encodeLE_wordLE a b c d
      have hb := encodeLE_wordLE e f g h
      rw [hl] at ha
      rw [hr] at hb
      have hc : encodeLE (960495616 + 0 * 1024) ++ encodeLE retWord = canonicalBytes := by decide
      rw [ha,hb] at hc
      exact hc
    next => cases hd
  · intro he
    subst bytes
    exact canonical_accepted

def loadInstr (off : Nat) : Instr :=
  ⟨.W32, .LDRB (.low (.reg .X0) .W32)
    { base := .low (.reg .X0) .W64,
      off := .imm {imm := .int64 (Int64.ofNat off), index := none} }⟩

def retInstr : Instr := ⟨.W64, .RET (.low (.reg .X30) .W64)⟩
def program (off : Nat) : Program := [.instr (loadInstr off), .instr retInstr]
abbrev fixedLayout (pc : Int64) : Layout := {start := pc, size := fun _ => 4}
def executable (pc : Int64) (off : Nat) : Executable := fixedLayout pc (program off)

def LayoutOK (pc : Int64) : Prop :=
  pc.toInt % 4 = 0 ∧ 0 ≤ pc.toInt ∧ pc.toInt + 8 ≤ 2^63-1
instance (pc : Int64) : Decidable (LayoutOK pc) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def certificate (pc : Int64) (bytes : List UInt8) : Option Executable :=
  if decide (LayoutOK pc) && accept bytes then some (executable pc 0) else none

theorem certificate_iff (pc : Int64) (bytes : List UInt8) (e : Executable) :
    certificate pc bytes = some e ↔
    LayoutOK pc ∧ bytes = canonicalBytes ∧ e = executable pc 0 := by
  unfold certificate
  split <;> rename_i ha
  · simp only [Option.some.injEq]
    have hp : LayoutOK pc ∧ accept bytes = true := by simpa using ha
    have hc := (accepted_iff_canonical bytes).mp hp.2
    simp [hp.1, hc, eq_comm]
  · simp only [reduceCtorEq, false_iff, not_and]
    intro hp hb
    apply False.elim
    apply ha
    simp [hp, (accepted_iff_canonical bytes).mpr hb]

def resultData (d : MachineData) (v : BitVec 8) : MachineData :=
  { d with regs := {d.regs with X0 := UInt64.ofBitVec (v.zeroExtend 64)} }

/-- A tree equality, including every access request, not just final-state equality. -/
theorem actual_effects (pc : Int64) (d : MachineData) (v : BitVec 8)
    (hload : Mem.loadInt d.dmem d.regs.X0.toBitVec 1 = some (Int.ofNat v.toNat)) :
    Executable.straightline (executable pc 0) ⟨d,pc⟩ .done =
      .require_exec_access ⟨pc,pc+4⟩ (fun _ =>
        .require_read_access d.regs.X0.toBitVec .W8 (fun _ =>
          .require_exec_access ⟨pc+4,pc+4+4⟩ (fun _ =>
            .done ⟨resultData d v,Int64.ofBitVec d.regs.X30.toBitVec⟩))) := by
  change Executable.straightline
    {startAddr := pc, program := [⟨.instr (loadInstr 0),4⟩,⟨.instr retInstr,4⟩]}
    ⟨d,pc⟩ .done = _
  simp [Executable.straightline,
    Kraken.Executable.directivesFromAddress, Kraken.Executable.withAddresses.eq_def,
    Directives.interp,
    Directive.interp, Instr.interp, Operation.interp, loadInstr, retInstr,
    AddrExpr.interpLoad, AddrExpr.checkSPAlignment, AddrExpr.eval,
    Reg64s.getRegOrSp, Reg64s.getRegOrSp64, Reg64s.getXReg,
    RegOrSp.base, RegOrZr.base, BitVec.take, BitVec.signed,
    ConstExpr.interp, MachineData.load, hload,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
    Reg64s.setXReg, Reg64s.getRegOrZr, Reg64s.getRegOrZr64,
    RegWidth.bits, MemWidth.bits, MemWidth.bytes, resultData]

def PermissionAll (readable writable : BitVec 64 → Nat → Prop)
    (exec : Std.Rco Int64 → Prop) (post : MachineState → Prop) : Effects → Prop
  | .done s => post s
  | .unimplemented _ => False
  | .unaligned_sp .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined _ _ k => ∀ v, PermissionAll readable writable exec post (k v)
  | .require_read_access a w k => readable a w.bytes ∧ PermissionAll readable writable exec post (k ())
  | .require_write_access a w k => writable a w.bytes ∧ PermissionAll readable writable exec post (k ())
  | .require_exec_access p k => exec p ∧ PermissionAll readable writable exec post (k ())

inductive Access where
  | exec (lower upper : Int64)
  | read (addr : BitVec 64) (width : Nat)
  | write (addr : BitVec 64) (width : Nat)
  deriving DecidableEq, Repr

def observe : Effects → Option (List Access × MachineState)
  | .done s => some ([],s)
  | .require_exec_access p k => (observe (k ())).map (fun (t,s) => (.exec p.lower p.upper :: t,s))
  | .require_read_access a w k => (observe (k ())).map (fun (t,s) => (.read a w.bytes :: t,s))
  | .require_write_access a w k => (observe (k ())).map (fun (t,s) => (.write a w.bytes :: t,s))
  | _ => none

def exactTrace (pc : Int64) (d : MachineData) : List Access :=
  [.exec pc (pc+4), .read d.regs.X0.toBitVec 1, .exec (pc+4) (pc+4+4)]

theorem complete_trace (pc : Int64) (d : MachineData) (v : BitVec 8)
    (hload : Mem.loadInt d.dmem d.regs.X0.toBitVec 1 = some (Int.ofNat v.toNat)) :
    observe (Executable.straightline (executable pc 0) ⟨d,pc⟩ .done) =
      some (exactTrace pc d, ⟨resultData d v, Int64.ofBitVec d.regs.X30.toBitVec⟩) := by
  rw [actual_effects pc d v hload]
  rfl

theorem permission_iff (pc : Int64) (d : MachineData) (v : BitVec 8)
    (hload : Mem.loadInt d.dmem d.regs.X0.toBitVec 1 = some (Int.ofNat v.toNat))
    (readable writable : BitVec 64 → Nat → Prop) (exec : Std.Rco Int64 → Prop)
    (post : MachineState → Prop) :
    PermissionAll readable writable exec post
      (Executable.straightline (executable pc 0) ⟨d,pc⟩ .done) ↔
    exec ⟨pc,pc+4⟩ ∧ readable d.regs.X0.toBitVec 1 ∧ exec ⟨pc+4,pc+4+4⟩ ∧
      post ⟨resultData d v, Int64.ofBitVec d.regs.X30.toBitVec⟩ := by
  rw [actual_effects pc d v hload]
  rfl

theorem checked_adapter (pc : Int64) (bytes : List UInt8) (e : Executable)
    (hcert : certificate pc bytes = some e) (d : MachineData) (v : BitVec 8)
    (hload : Mem.loadInt d.dmem d.regs.X0.toBitVec 1 = some (Int.ofNat v.toNat)) :
    observe (Executable.straightline e ⟨d,pc⟩ .done) =
      some (exactTrace pc d, ⟨resultData d v,Int64.ofBitVec d.regs.X30.toBitVec⟩) := by
  rcases (certificate_iff pc bytes e).mp hcert with ⟨_,_,he⟩
  subst e
  exact complete_trace pc d v hload

def withinRegion (base size : Nat) (addr : BitVec 64) (width : Nat) : Prop :=
  base ≤ addr.toNat ∧ addr.toNat + width ≤ base + size ∧ addr.toNat + width ≤ 2^64

theorem one_byte_region (d : MachineData) :
    withinRegion d.regs.X0.toNat 1 d.regs.X0.toBitVec 1 := by
  have := d.regs.X0.toNat_lt
  unfold withinRegion
  simp only [UInt64.toNat_toBitVec]
  omega

theorem empty_span_rejected (pc : Int64) (d : MachineData) (v : BitVec 8)
    (hload : Mem.loadInt d.dmem d.regs.X0.toBitVec 1 = some (Int.ofNat v.toNat))
    (writable : BitVec 64 → Nat → Prop) (exec : Std.Rco Int64 → Prop)
    (post : MachineState → Prop) :
    ¬ PermissionAll (withinRegion d.regs.X0.toNat 0) writable exec post
      (Executable.straightline (executable pc 0) ⟨d,pc⟩ .done) := by
  rw [permission_iff pc d v hload]
  rintro ⟨_,h,_,_⟩
  unfold withinRegion at h
  simp only [UInt64.toNat_toBitVec] at h
  omega

theorem wrong_return_rejected (pc : Int64) (d : MachineData) (v : BitVec 8)
    (hload : Mem.loadInt d.dmem d.regs.X0.toBitVec 1 = some (Int.ofNat v.toNat))
    (wrong : Int64) (hne : Int64.ofBitVec d.regs.X30.toBitVec ≠ wrong) :
    ¬ (Executable.straightline (executable pc 0) ⟨d,pc⟩ .done).All (fun s => s.pc = wrong) := by
  rw [actual_effects pc d v hload]
  simpa only [Effects.All] using hne

theorem wrong_frame_rejected (pc : Int64) (d : MachineData) (v : BitVec 8)
    (hload : Mem.loadInt d.dmem d.regs.X0.toBitVec 1 = some (Int.ofNat v.toNat))
    (wrong : UInt64) (hne : d.regs.X19 ≠ wrong) :
    ¬ (Executable.straightline (executable pc 0) ⟨d,pc⟩ .done).All (fun s => s.data.regs.X19 = wrong) := by
  rw [actual_effects pc d v hload]
  simpa only [Effects.All, resultData] using hne

theorem zero_writes (pc : Int64) (d : MachineData) (a : BitVec 64) (n : Nat) :
    Access.write a n ∉ exactTrace pc d := by simp [exactTrace]

theorem result_zero_extended (d : MachineData) (v : UInt8) :
    (resultData d v.toBitVec).regs.X0.toNat = v.toNat := by
  simp [resultData]

theorem byte_value (v : UInt8) : Int.ofBytes v.toBytes = (v.toNat : Int) := by
  rw [UInt8.toBytes, ofBytes_toBytes]
  simp only [Int.take, BitVec.toInt_eq_msb_cond, UInt8.toNat_toBitVec]
  have hv := v.toNat_lt
  split <;> omega

theorem resource_load (d : MachineData) (v : UInt8) (R : DataMem → Prop)
    (hsep : d.dmem =⋆ Eq (v.At d.regs.X0.toBitVec) ⋆ R) :
    Mem.loadInt d.dmem d.regs.X0.toBitVec 1 = some (Int.ofNat v.toBitVec.toNat) := by
  have h := Mem.loadInt_sep v.toBytes d.regs.X0.toBitVec 1 R d.dmem
    hsep (UInt8.toBytes_length v) (by decide)
  simpa [byte_value] using h

theorem checked_resource_contract (pc : Int64) (bytes : List UInt8) (e : Executable)
    (hcert : certificate pc bytes = some e) (d : MachineData) (v : UInt8)
    (base : BitVec 64) (harg : d.regs.X0.toBitVec = base) (R : DataMem → Prop)
    (hsep : d.dmem =⋆ Eq (v.At base) ⋆ R)
    (exec : Std.Rco Int64 → Prop) (hx0 : exec ⟨pc,pc+4⟩) (hx1 : exec ⟨pc+4,pc+4+4⟩) :
    PermissionAll (withinRegion base.toNat 1) (fun _ _ => False) exec
      (fun s => s.data = resultData d v.toBitVec ∧
        s.pc = Int64.ofBitVec d.regs.X30.toBitVec ∧
        s.data.dmem = d.dmem ∧ s.data.dmem =⋆ Eq (v.At base) ⋆ R)
      (Executable.straightline e ⟨d,pc⟩ .done) := by
  have hload := resource_load d v R (by simpa only [harg] using hsep)
  rcases (certificate_iff pc bytes e).mp hcert with ⟨_,_,he⟩
  subst e
  rw [permission_iff pc d v.toBitVec hload]
  refine ⟨hx0, ?_, hx1, rfl, rfl, rfl, hsep⟩
  simpa only [← harg, UInt64.toNat_toBitVec] using one_byte_region d

theorem code_no_wrap (pc : Int64) (h : LayoutOK pc) :
    pc.toInt + 8 < 2^63 := by unfold LayoutOK at h; omega

theorem layout_endpoints (pc : Int64) (h : LayoutOK pc) :
    (pc+4).toInt = pc.toInt+4 ∧ (pc+4+4).toInt = pc.toInt+8 := by
  unfold LayoutOK at h
  have h4 : (pc+4).toInt = pc.toInt+4 := by
    rw [Int64.toInt_add]
    change (pc.toInt+4).bmod (2^64) = pc.toInt+4
    apply Int.bmod_eq_of_le <;> omega
  refine ⟨h4, ?_⟩
  rw [Int64.toInt_add, h4]
  change (pc.toInt+4+4).bmod (2^64) = pc.toInt+8
  rw [show pc.toInt+4+4 = pc.toInt+8 by omega]
  apply Int.bmod_eq_of_le <;> omega

theorem actual_load_step (pc : Int64) (hp : LayoutOK pc) (d : MachineData) (v : BitVec 8)
    (hload : Mem.loadInt d.dmem d.regs.X0.toBitVec 1 = some (Int.ofNat v.toNat)) :
    Executable.step (executable pc 0) ⟨d,pc⟩ .done =
      .require_exec_access ⟨pc,pc+4⟩ (fun _ =>
        .require_read_access d.regs.X0.toBitVec .W8 (fun _ =>
          .done ⟨resultData d v,pc+4⟩)) := by
  have hdistinct : pc+4 ≠ pc := by
    intro he
    have hh := congrArg Int64.toInt he
    rw [(layout_endpoints pc hp).1] at hh
    omega
  change Executable.step
    {startAddr := pc, program := [⟨.instr (loadInstr 0),4⟩,⟨.instr retInstr,4⟩]}
    ⟨d,pc⟩ .done = _
  simp [Executable.step, Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses.eq_def,
    hdistinct, Directives.interp, Directive.interp, Instr.interp, Operation.interp, loadInstr,
    AddrExpr.interpLoad, AddrExpr.checkSPAlignment, AddrExpr.eval,
    Reg64s.getRegOrSp, Reg64s.getRegOrSp64, Reg64s.getXReg,
    RegOrSp.base, BitVec.take, BitVec.signed, ConstExpr.interp, MachineData.load, hload,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64,
    Reg64s.setXReg, RegWidth.bits, MemWidth.bits, MemWidth.bytes, resultData]

theorem actual_ret_step (pc : Int64) (hp : LayoutOK pc) (d : MachineData) :
    Executable.step (executable pc 0) ⟨d,pc+4⟩ .done =
      .require_exec_access ⟨pc+4,pc+4+4⟩ (fun _ =>
        .done ⟨d,Int64.ofBitVec d.regs.X30.toBitVec⟩) := by
  have hdistinct : pc ≠ pc+4 := by
    intro he
    have hh := congrArg Int64.toInt he
    rw [(layout_endpoints pc hp).1] at hh
    omega
  change Executable.step
    {startAddr := pc, program := [⟨.instr (loadInstr 0),4⟩,⟨.instr retInstr,4⟩]}
    ⟨d,pc+4⟩ .done = _
  simp [Executable.step, Kraken.Executable.directivesAtAddress, Kraken.Executable.withAddresses.eq_def,
    hdistinct, Directives.interp, Directive.interp, Instr.interp, Operation.interp, retInstr,
    Reg64s.getRegOrZr, Reg64s.getRegOrZr64, Reg64s.getXReg, RegOrZr.base,
    BitVec.take, BitVec.signed, RegWidth.bits]

theorem result_preserves_resource (d : MachineData) (v : UInt8) (base : BitVec 64)
    (R : DataMem → Prop) (hsep : d.dmem =⋆ Eq (v.At base) ⋆ R) :
    (resultData d v.toBitVec).dmem =⋆ Eq (v.At base) ⋆ R := hsep

theorem malformed_layout_rejected (pc : Int64) (h : ¬ LayoutOK pc) (bytes : List UInt8) :
    certificate pc bytes = none := by simp [certificate, h]

theorem any_changed_bytes_rejected (bytes : List UInt8) (h : bytes ≠ canonicalBytes) :
    accept bytes = false := by
  have hn : accept bytes ≠ true := fun ha => h ((accepted_iff_canonical bytes).mp ha)
  cases he : accept bytes <;> simp_all

theorem wrong_length_rejected (bytes : List UInt8) (h : bytes.length ≠ 8) :
    accept bytes = false := by
  apply any_changed_bytes_rejected
  intro he
  subst bytes
  exact h rfl

theorem unaligned_certificate_rejected : certificate 4097 canonicalBytes = none := by decide
theorem wrapping_certificate_rejected : certificate 9223372036854775804 canonicalBytes = none := by decide
theorem good_certificate : certificate 4096 canonicalBytes = some (executable 4096 0) := by rfl

/-- These mutants are data only; none is executed natively. -/
def byteControls : List (String × List UInt8) :=
  [("widen_to_64bit_load", [0x00,0x00,0x40,0xf9,0xc0,0x03,0x5f,0xd6]),
   ("load_from_x1", [0x20,0x00,0x40,0x39,0xc0,0x03,0x5f,0xd6]),
   ("write_result_w19", [0x13,0x00,0x40,0x39,0xc0,0x03,0x5f,0xd6]),
   ("offset_one", [0x00,0x04,0x40,0x39,0xc0,0x03,0x5f,0xd6]),
   ("return_x0", [0x00,0x00,0x40,0x39,0x00,0x00,0x5f,0xd6]),
   ("hidden_load_before_ret", [0x00,0x00,0x40,0x39,0x21,0x00,0x40,0x39,0xc0,0x03,0x5f,0xd6]),
   ("hidden_clobber_before_ret", [0x00,0x00,0x40,0x39,0x33,0x00,0x80,0xd2,0xc0,0x03,0x5f,0xd6]),
   ("truncated", [0x00,0x00,0x40,0x39,0xc0,0x03,0x5f])]

theorem named_byte_controls_rejected : byteControls.all (fun row => !(accept row.2)) = true := by decide

#print axioms decode_load_iff
#print axioms decode_ret_iff
#print axioms wordLE_bound
#print axioms encodeLE_wordLE
#print axioms decodeLeaf_fields
#print axioms accepted_iff_canonical
#print axioms certificate_iff
#print axioms actual_effects
#print axioms complete_trace
#print axioms permission_iff
#print axioms checked_adapter
#print axioms one_byte_region
#print axioms empty_span_rejected
#print axioms wrong_return_rejected
#print axioms wrong_frame_rejected
#print axioms zero_writes
#print axioms result_zero_extended
#print axioms byte_value
#print axioms resource_load
#print axioms checked_resource_contract
#print axioms code_no_wrap
#print axioms layout_endpoints
#print axioms actual_load_step
#print axioms actual_ret_step
#print axioms result_preserves_resource
#print axioms malformed_layout_rejected
#print axioms any_changed_bytes_rejected
#print axioms wrong_length_rejected
#print axioms unaligned_certificate_rejected
#print axioms wrapping_certificate_rejected
#print axioms good_certificate
#print axioms named_byte_controls_rejected

end CheckedByteLeaf
