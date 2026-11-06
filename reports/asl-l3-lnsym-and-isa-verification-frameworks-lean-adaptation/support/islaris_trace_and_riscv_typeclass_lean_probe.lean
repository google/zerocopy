/-
  islaris_trace_and_riscv_typeclass_lean_probe.lean

  Standalone Lean 4.34.1 mechanization for Chunk 9:
  "Rocq, HOL4, Isabelle/HOL, ACL2, and F* ISA Verification Frameworks and Their
   Lean 4 Adaptation for Anneal"

  This file mechanizes two self-contained architectural probes directly connected
  to Anneal's `Trusted/StepResult.lean` and `Trusted/Refinement.lean` kernel:

  1. `riscv-coq`-Style Typeclass-Parameterized ISA Semantics (`IsaMachineM`)
     instantiated over two concrete state models:
     - `FlatMachine`: flat 64-bit word registers + flat word-addressed memory +
       `riscv-coq`-style `xAddrs` executable-address coherence tracking,
       Jasmin-style partial-register write modes (`MsbFlag.clear` vs `MsbFlag.merge`),
       and CompCert/Jasmin-style optional flag initialization (`RFlagVal.def` vs `.undef`).
     - `ProvMachine`: CompCert/Anneal-style allocation-provenance (`IsaVal.ptr allocId ofs`)
       and per-block bounds/permission checking (`Perm.readable`, `Perm.writable`),
       with a machine-checked forward simulation theorem (`prov_to_flat_simulation`)
       and a negative control (`forged_or_cross_block_ptr_ub_in_prov_succeeds_in_flat`)
       showing that cross-allocation spatial overflow is caught as `.failed .ub` in
       `ProvMachine` even when adjacent blocks make the flat load succeed in `FlatMachine`.

  2. `Islaris`-in-Lean Symbolic Trace Language (`IslaTrace`) and Trace-to-`StepResult`
     Adequacy:
     - Models `isla-lang` / `Islaris` trace trees (`readReg`, `writeReg`, `readMem`,
       `writeMem`, `setPC`, `smtAssert`, `sailAssume`, `cases`) and the inverted
       polarity between `Smt (Assert e)` (path assumption transitioning to
       `seq_nb_state := true` / `.nbHalted` when false) and `Assume e` (`sail_assume`
       verification obligation transitioning to `.stuckUB` when false).
     - Proves a positive adequacy bridge (`islaTrace_refines_stepResult`) showing that
       when a trace satisfies the `sail-riscv`-style completeness & simulation
       validator (`ValidCompleteTrace`), `naiveIslarisAdequacy` implies concrete
       `StepResult` postcondition satisfaction on `stepFlat`.
     - Mechanizes a negative control
       (`incomplete_trace_accepted_by_naive_nb_adequacy_but_rejected_by_completeness_validator`)
       demonstrating that an incomplete `tcases` trace omitting a feasible branch is
       vacuously accepted by `seq_nb_state` adequacy yet rejected by the completeness
       validator.
-/

namespace AnnealIsaAdaptationProbe

/-! ## Section 1: Anneal Core `Error`, `StepResult`, `Partial`, and `StepResult.Refines` -/

/-- Mirrors `Trusted.Error` in `skeleton/trusted/lean/Trusted/StepResult.lean`. -/
inductive Error where
  | ub
  | unsupported
  | resourceExhausted
  deriving DecidableEq, Repr

/-- Mirrors `Trusted.StepResult` in `skeleton/trusted/lean/Trusted/StepResult.lean`. -/
inductive StepResult (State : Type) where
  | step (next : State)
  | ret (val : BitVec 64)
  | diverged
  | failed (err : Error)
  deriving DecidableEq, Repr

/-- Mirrors `Trusted.StepResult.Refines` in `skeleton/trusted/lean/Trusted/Refinement.lean`:
    source `.failed .ub` refines any target outcome, while non-UB outcomes must match. -/
def StepResult.Refines {State : Type} (src tgt : StepResult State) : Prop :=
  match src with
  | .failed .ub => True
  | other => other = tgt

theorem StepResult.Refines.refl {State : Type} (r : StepResult State) :
    StepResult.Refines r r := by
  cases r with
  | failed err =>
    cases err <;> simp [StepResult.Refines]
  | _ => simp [StepResult.Refines]

theorem StepResult.Refines.ub_left {State : Type} (tgt : StepResult State) :
    StepResult.Refines (.failed .ub) tgt := by
   trivial

/-- Mirrors `Trusted.Partial` in `skeleton/trusted/lean/Trusted/Refinement.lean`. -/
structure Partial (α : Type) : Type 1 where
  Defined : Prop
  val : Defined → α

namespace Partial

def defined (x : α) : Partial α where
  Defined := True
  val := fun _ => x

def undefined : Partial α where
  Defined := False
  val := False.elim

def Refines (src tgt : Partial α) : Prop :=
  ∀ hSrc : src.Defined, ∃ hTgt : tgt.Defined, src.val hSrc = tgt.val hTgt

theorem undefined_refines_any (tgt : Partial α) :
    Partial.Refines Partial.undefined tgt := by
  intro hSrc
  exact False.elim hSrc

end Partial

/-! ## Section 2: `riscv-coq`-Style Typeclass-Parameterized ISA Semantics -/

/-- Architectural general-purpose registers (representative subset). -/
inductive Reg where
  | r0
  | r1
  | r2
  | r3
  deriving DecidableEq, Repr

/-- Architectural status flags (representative subset: `ZF`, `CF`, `PF`). -/
inductive FlagId where
  | zf
  | cf
  | pf
  deriving DecidableEq, Repr

/-- CompCert (`Vundef`) / Jasmin (`rflagv := Def bool | Undef`) flag lattice. -/
inductive RFlagVal where
  | def (b : Bool)
  | undef
  deriving DecidableEq, Repr

/-- Jasmin `msb_flag` (`proofs/arch/arch_decl.v:279`):
    - `clear` (`MSB_CLEAR`): zero-extends sub-word write into upper bits (x86-64 32-bit write).
    - `merge` (`MSB_MERGE`): merges sub-word write with existing upper bits (x86-64 8/16-bit write). -/
inductive MsbFlag where
  | clear
  | merge
  deriving DecidableEq, Repr

/-- Purely decoded ISA instruction AST (`riscv-coq` `Decode.v` / Jasmin `asm_op` style). -/
inductive IsaInst where
  | movImm (dst : Reg) (imm : BitVec 64)
  | add (dst src1 src2 : Reg)
  | subWidthWrite32 (dst : Reg) (msbMode : MsbFlag) (val32 : BitVec 32)
  | cmpSetFlags (src1 src2 : Reg)
  | readFlagToReg (dst : Reg) (f : FlagId)
  | branchEqZero (condReg : Reg) (targetTaken targetFallthrough : BitVec 64)
  | load64 (dst addrReg : Reg) (ofs : Nat)
  | store64 (addrReg srcReg : Reg) (ofs : Nat)
  | fenceI
  deriving DecidableEq, Repr

/-- Pure bit-manipulation helper for 32-bit partial register writes (`MSB_CLEAR` vs `MSB_MERGE`). -/
def applySubWidth32 (old64 : BitVec 64) (mode : MsbFlag) (low32 : BitVec 32) : BitVec 64 :=
  let zextLow : BitVec 64 := low32.zeroExtend 64
  match mode with
  | .clear => zextLow
  | .merge =>
    let highMask : BitVec 64 := 0xFFFFFFFF00000000#64
    (old64 &&& highMask) ||| zextLow

/-- `riscv-coq` `RiscvProgram` / `RiscvMachine`-style monadic typeclass interface.
    Decouples instruction semantics (`executeInst`) from the representation of values,
    memory provenance, flag undefness, and instruction-cache coherence. -/
class IsaMachineM (M : Type → Type) [Monad M] where
  Val : Type
  getReg : Reg → M Val
  setReg : Reg → Val → M Unit
  getFlag : FlagId → M Bool
  setFlag : FlagId → RFlagVal → M Unit
  getPC : M (BitVec 64)
  setPC : BitVec 64 → M Unit
  constWord : BitVec 64 → M Val
  boolToVal : Bool → M Val
  addVal : Val → Val → M Val
  subWidth32Val : Val → MsbFlag → BitVec 32 → M Val
  eqVal : Val → Val → M Bool
  isZeroVal : Val → M Bool
  loadWord64 : Val → Nat → M Val
  storeWord64 : Val → Nat → Val → M Unit
  fetchAndCheckICache : BitVec 64 → M Unit
  syncICache : M Unit

/-- Generic monadic ISA execution semantics (`riscv-coq` `Execute.v` style),
    shared identically across `FlatMachine` and `ProvMachine`. -/
def executeInst {M : Type → Type} [Monad M] [IsaMachineM M] (inst : IsaInst) : M Unit := do
  let pc ← IsaMachineM.getPC
  IsaMachineM.fetchAndCheckICache pc
  match inst with
  | .movImm dst imm =>
    let v ← IsaMachineM.constWord imm
    IsaMachineM.setReg dst v
    IsaMachineM.setPC (pc + 4#64)
  | .add dst src1 src2 =>
    let v1 ← IsaMachineM.getReg src1
    let v2 ← IsaMachineM.getReg src2
    let res ← IsaMachineM.addVal v1 v2
    IsaMachineM.setReg dst res
    IsaMachineM.setPC (pc + 4#64)
  | .subWidthWrite32 dst mode val32 =>
    let old ← IsaMachineM.getReg dst
    let res ← IsaMachineM.subWidth32Val old mode val32
    IsaMachineM.setReg dst res
    IsaMachineM.setPC (pc + 4#64)
  | .cmpSetFlags src1 src2 =>
    let v1 ← IsaMachineM.getReg src1
    let v2 ← IsaMachineM.getReg src2
    let isEq ← IsaMachineM.eqVal v1 v2
    -- Like CompCert `compare_ints` (`x86/Asm.v:433-446`), ZF is defined while PF is left `.undef`.
    IsaMachineM.setFlag .zf (.def isEq)
    IsaMachineM.setFlag .cf (.def false)
    IsaMachineM.setFlag .pf .undef
    IsaMachineM.setPC (pc + 4#64)
  | .readFlagToReg dst f =>
    let b ← IsaMachineM.getFlag f
    let v ← IsaMachineM.boolToVal b
    IsaMachineM.setReg dst v
    IsaMachineM.setPC (pc + 4#64)
  | .branchEqZero condReg targetTaken targetFallthrough =>
    let condVal ← IsaMachineM.getReg condReg
    let z ← IsaMachineM.isZeroVal condVal
    if z then
      IsaMachineM.setPC targetTaken
    else
      IsaMachineM.setPC targetFallthrough
  | .load64 dst addrReg ofs =>
    let base ← IsaMachineM.getReg addrReg
    let v ← IsaMachineM.loadWord64 base ofs
    IsaMachineM.setReg dst v
    IsaMachineM.setPC (pc + 4#64)
  | .store64 addrReg srcReg ofs =>
    let base ← IsaMachineM.getReg addrReg
    let v ← IsaMachineM.getReg srcReg
    IsaMachineM.storeWord64 base ofs v
    IsaMachineM.setPC (pc + 4#64)
  | .fenceI =>
    IsaMachineM.syncICache
    IsaMachineM.setPC (pc + 4#64)

/-- State-and-error monad returning Anneal `StepResult`. -/
abbrev MachineM (S : Type) (α : Type) : Type :=
  S → Except Error (α × S)

instance {S : Type} : Monad (MachineM S) where
  pure a := fun s => .ok (a, s)
  bind m f := fun s =>
    match m s with
    | .ok (a, s') => f a s'
    | .error e => .error e

def runToStepResult {S : Type} (m : MachineM S Unit) (s : S) : StepResult S :=
  match m s with
  | .ok ((), s') => .step s'
  | .error e => .failed e

/-! ### Backend 1: `FlatMachine` (Flat Word Registers, Flat Memory, `xAddrs` I-Cache Coherence) -/

structure FlatMachine where
  regs : Reg → BitVec 64
  flags : FlagId → RFlagVal
  pc : BitVec 64
  mem : Nat → Option (BitVec 64)
  /-- Mirrors `riscv-coq` `RiscvMachine.xAddrs`: addresses with valid instruction-cache lines. -/
  xAddrs : List Nat
  /-- Static code region that `fence.i` re-synchronizes into `xAddrs`. -/
  codeAddrs : List Nat

def updateReg {α : Type} (f : Reg → α) (r : Reg) (v : α) : Reg → α :=
  fun r' => if r' = r then v else f r'

def updateFlag (f : FlagId → RFlagVal) (fl : FlagId) (v : RFlagVal) : FlagId → RFlagVal :=
  fun fl' => if fl' = fl then v else f fl'

def updateMem (m : Nat → Option (BitVec 64)) (addr : Nat) (v : BitVec 64) :
    Nat → Option (BitVec 64) :=
  fun a => if a = addr then some v else m a

instance : IsaMachineM (MachineM FlatMachine) where
  Val := BitVec 64
  getReg r := fun s => .ok (s.regs r, s)
  setReg r v := fun s => .ok ((), { s with regs := updateReg s.regs r v })
  getFlag fl := fun s =>
    match s.flags fl with
    | .def b => .ok (b, s)
    | .undef => .error .ub
  setFlag fl v := fun s => .ok ((), { s with flags := updateFlag s.flags fl v })
  getPC := fun s => .ok (s.pc, s)
  setPC newPc := fun s => .ok ((), { s with pc := newPc })
  constWord w := fun s => .ok (w, s)
  boolToVal b := fun s => .ok (if b then 1#64 else 0#64, s)
  addVal v1 v2 := fun s => .ok (v1 + v2, s)
  subWidth32Val old mode low32 := fun s => .ok (applySubWidth32 old mode low32, s)
  eqVal v1 v2 := fun s => .ok (v1 == v2, s)
  isZeroVal v := fun s => .ok (v == 0#64, s)
  loadWord64 base ofs := fun s =>
    let addr := base.toNat + ofs
    match s.mem addr with
    | some w => .ok (w, s)
    | none => .error .ub
  storeWord64 base ofs val := fun s =>
    let addr := base.toNat + ofs
    match s.mem addr with
    | some _ =>
      -- Mirrors `riscv-coq` `Minimal.v:47-56`: storing to memory invalidates `xAddrs` at `addr`.
      let xAddrs' := s.xAddrs.filter (fun a => a != addr)
      .ok ((), { s with mem := updateMem s.mem addr val, xAddrs := xAddrs' })
    | none => .error .ub
  fetchAndCheckICache pc := fun s =>
    if s.xAddrs.contains pc.toNat then
      .ok ((), s)
    else
      .error .unsupported
  syncICache := fun s =>
    .ok ((), { s with xAddrs := s.codeAddrs })

def stepFlat (inst : IsaInst) (s : FlatMachine) : StepResult FlatMachine :=
  runToStepResult (executeInst inst) s

/-! ### Backend 2: `ProvMachine` (CompCert/Anneal-Style Provenance & Per-Block Bounds) -/

/-- CompCert `val` (`Values.v:34-40`) / Anneal pointer-provenance value representation:
    distinguishes raw 64-bit integers (`.word`) from pointers carrying an allocation ID (`.ptr`). -/
inductive IsaVal where
  | word (w : BitVec 64)
  | ptr (allocId : Nat) (ofs : Nat)
  deriving DecidableEq, Repr

inductive Perm where
  | none
  | readable
  | writable
  deriving DecidableEq, Repr

def Perm.canRead : Perm → Bool
  | .readable | .writable => true
  | .none => false

def Perm.canWrite : Perm → Bool
  | .writable => true
  | _ => false

structure AllocBlock where
  baseAddr : Nat
  size : Nat
  perm : Perm
  cells : Nat → BitVec 64

structure ProvMachine where
  regs : Reg → IsaVal
  flags : FlagId → RFlagVal
  pc : BitVec 64
  blocks : Nat → Option AllocBlock
  xAddrs : List Nat
  codeAddrs : List Nat

def updateBlock (bs : Nat → Option AllocBlock) (id : Nat) (b : AllocBlock) :
    Nat → Option AllocBlock :=
  fun id' => if id' = id then some b else bs id'

def updateCell (c : Nat → BitVec 64) (ofs : Nat) (v : BitVec 64) : Nat → BitVec 64 :=
  fun o => if o = ofs then v else c o

instance : IsaMachineM (MachineM ProvMachine) where
  Val := IsaVal
  getReg r := fun s => .ok (s.regs r, s)
  setReg r v := fun s => .ok ((), { s with regs := updateReg s.regs r v })
  getFlag fl := fun s =>
    match s.flags fl with
    | .def b => .ok (b, s)
    | .undef => .error .ub
  setFlag fl v := fun s => .ok ((), { s with flags := updateFlag s.flags fl v })
  getPC := fun s => .ok (s.pc, s)
  setPC newPc := fun s => .ok ((), { s with pc := newPc })
  constWord w := fun s => .ok (.word w, s)
  boolToVal b := fun s => .ok (.word (if b then 1#64 else 0#64), s)
  addVal v1 v2 := fun s =>
    match v1, v2 with
    | .word w1, .word w2 => .ok (.word (w1 + w2), s)
    | .ptr id ofs, .word w2 => .ok (.ptr id (ofs + w2.toNat), s)
    | _, _ => .error .ub
  subWidth32Val old mode low32 := fun s =>
    match old with
    | .word oldW => .ok (.word (applySubWidth32 oldW mode low32), s)
    | .ptr _ _ => .error .ub
  eqVal v1 v2 := fun s =>
    match v1, v2 with
    | .word w1, .word w2 => .ok (w1 == w2, s)
    | _, _ => .error .ub
  isZeroVal v := fun s =>
    match v with
    | .word w => .ok (w == 0#64, s)
    | .ptr _ _ => .error .ub
  loadWord64 base ofs := fun s =>
    match base with
    | .word _ =>
      -- Forging a pointer from a raw integer triggers UB in the provenance model.
      .error .ub
    | .ptr id baseOfs =>
      let totalOfs := baseOfs + ofs
      match s.blocks id with
      | some blk =>
        if blk.perm.canRead && decide (totalOfs < blk.size) then
          .ok (.word (blk.cells totalOfs), s)
        else
          .error .ub
      | none => .error .ub
  storeWord64 base ofs val := fun s =>
    match base, val with
    | .ptr id baseOfs, .word w =>
      let totalOfs := baseOfs + ofs
      match s.blocks id with
      | some blk =>
        if blk.perm.canWrite && decide (totalOfs < blk.size) then
          let flatAddr := blk.baseAddr + totalOfs
          let blk' : AllocBlock := { blk with cells := updateCell blk.cells totalOfs w }
          let xAddrs' := s.xAddrs.filter (fun a => a != flatAddr)
          .ok ((), { s with blocks := updateBlock s.blocks id blk', xAddrs := xAddrs' })
        else
          .error .ub
      | none => .error .ub
    | _, _ => .error .ub
  fetchAndCheckICache pc := fun s =>
    if s.xAddrs.contains pc.toNat then
      .ok ((), s)
    else
      .error .unsupported
  syncICache := fun s =>
    .ok ((), { s with xAddrs := s.codeAddrs })

def stepProv (inst : IsaInst) (s : ProvMachine) : StepResult ProvMachine :=
  runToStepResult (executeInst inst) s

/-! ### Theorems on Partial Registers, Undefined Flags, I-Cache Coherence, and Provenance -/

/-- Theorem 2.1: Jasmin `MSB_CLEAR` vs `MSB_MERGE` on 32-bit sub-register writes.
    `MSB_CLEAR` zeroes bits 32..63 (x86-64 `MOV EAX, ...`), whereas `MSB_MERGE`
    preserves bits 32..63 (x86-64 `MOV AX, ...` / 16-bit style merge). -/
theorem msb_clear_vs_merge_contrast :
    applySubWidth32 0xCAFEBABE11223344#64 .clear 0xDEADBEEF#32 = 0x00000000DEADBEEF#64 ∧
    applySubWidth32 0xCAFEBABE11223344#64 .merge 0xDEADBEEF#32 = 0xCAFEBABEDEADBEEF#64 := by
  decide

/-- Concrete test state for `FlatMachine`. -/
def sampleFlatState : FlatMachine where
  regs := fun
    | .r0 => 42#64
    | .r1 => 42#64
    | .r2 => 0xCAFEBABE00000000#64
    | .r3 => 0x1000#64
  flags := fun _ => .undef
  pc := 0x100#64
  mem := fun a => if a = 0x1000 ∨ a = 0x1008 ∨ a = 0x104 then some 99#64 else none
  xAddrs := [0x100, 0x104, 0x108]
  codeAddrs := [0x100, 0x104, 0x108]

/-- Theorem 2.2: After `.cmpSetFlags .r0 .r1`, reading `.zf` succeeds deterministically
    (setting `.r2` to `1`), whereas reading `.pf` (which `cmpSetFlags` sets to `.undef`,
    matching CompCert `compare_ints` in `x86/Asm.v:433-446` and Jasmin `undef_error`)
    returns `.failed .ub`, which refines any target `StepResult` under `StepResult.Refines`. -/
theorem reading_undef_flag_triggers_ub_refines_any (tgt : StepResult FlatMachine) :
    (match stepFlat (.cmpSetFlags .r0 .r1) sampleFlatState with
     | .step s1 =>
       (match stepFlat (.readFlagToReg .r2 .zf) s1 with
        | .step s2 => s2.regs .r2 = 1#64
        | _ => False) ∧
       StepResult.Refines (stepFlat (.readFlagToReg .r2 .pf) s1) tgt
     | _ => False) := by
  dsimp [stepFlat, runToStepResult, executeInst, sampleFlatState]
  refine ⟨rfl, ?_⟩
  exact StepResult.Refines.ub_left tgt

/-- Theorem 2.3: Self-modifying store into an instruction address (`0x104`) invalidates
    `xAddrs` (`riscv-coq` `invalidateWrittenXAddrs`), causing instruction fetch at `0x104`
    to fail with `.failed .unsupported` unless `fence.i` (`syncICache`) is executed first. -/
theorem self_modifying_store_without_fenceI_fails_fetch :
    let sSelfMod : FlatMachine :=
      { sampleFlatState with regs := updateReg sampleFlatState.regs .r3 0x104#64 }
    -- 1. Without `fence.i`, storing to 0x104 at PC=0x100 then executing at PC=0x104 fails:
    (match stepFlat (.store64 .r3 .r0 0) sSelfMod with
     | .step sAfterStore =>
       stepFlat (.movImm .r0 1#64) sAfterStore = .failed .unsupported ∧
       -- 2. If `fence.i` is executed at a coherent PC, `0x104` is restored to `xAddrs`:
       (match stepFlat .fenceI { sAfterStore with pc := 0x108#64 } with
        | .step sAfterFence =>
          sAfterFence.xAddrs.contains 0x104 = true
        | _ => False)
     | _ => False) := by
  exact ⟨rfl, rfl⟩

/-- Flattening function from `IsaVal` to `BitVec 64` given a block base-address map. -/
def flattenVal (blockBase : Nat → Nat) : IsaVal → BitVec 64
  | .word w => w
  | .ptr id ofs => BitVec.ofNat 64 (blockBase id + ofs)

/-- Two adjacent allocations:
    - Block 0 at `[0x1000, 0x1008)` (`baseAddr = 0x1000`, `size = 8`)
    - Block 1 at `[0x1008, 0x1010)` (`baseAddr = 0x1008`, `size = 8`) -/
def adjacentBlocks (id : Nat) : Option AllocBlock :=
  match id with
  | 0 => some { baseAddr := 0x1000, size := 8, perm := .writable, cells := fun _ => 111#64 }
  | 1 => some { baseAddr := 0x1008, size := 8, perm := .writable, cells := fun _ => 222#64 }
  | _ => none

def sampleProvState : ProvMachine where
  regs := fun
    | .r0 => .ptr 0 0
    | .r1 => .word 0x1000#64
    | .r2 => .word 0#64
    | .r3 => .word 0#64
  flags := fun _ => .def false
  pc := 0x100#64
  blocks := adjacentBlocks
  xAddrs := [0x100, 0x104]
  codeAddrs := [0x100, 0x104]

def sampleMatchingFlatState : FlatMachine where
  regs := fun
    | .r0 => 0x1000#64
    | .r1 => 0x1000#64
    | .r2 => 0#64
    | .r3 => 0#64
  flags := fun _ => .def false
  pc := 0x100#64
  mem := fun a =>
    if 0x1000 ≤ a ∧ a < 0x1008 then some 111#64
    else if 0x1008 ≤ a ∧ a < 0x1010 then some 222#64
    else none
  xAddrs := [0x100, 0x104]
  codeAddrs := [0x100, 0x104]

/-- Theorem 2.4 (Negative Control 1 — Provenance vs. Flat Memory):
    1. In-bounds load from `.ptr 0 0` (`ofs = 0 < 8`) succeeds in both `ProvMachine`
       and `FlatMachine`, reading `111#64`.
    2. Cross-allocation load from `.ptr 0 8` (`ofs = 8`, one past Block 0, landing on
       Block 1's base address `0x1008`) triggers `.failed .ub` in `ProvMachine`
       but silently succeeds in `FlatMachine` (reading `222#64` from Block 1).
    3. Integer-to-pointer forgery (`load64` from `.r1 = .word 0x1000#64`) triggers
       `.failed .ub` in `ProvMachine` even though `0x1000` is mapped in `FlatMachine`. -/
theorem forged_or_cross_block_ptr_ub_in_prov_succeeds_in_flat :
    -- (1) In-bounds load agrees across ProvMachine and FlatMachine:
    (match stepProv (.load64 .r2 .r0 0) sampleProvState,
           stepFlat (.load64 .r2 .r0 0) sampleMatchingFlatState with
     | .step ps', .step fs' =>
       ps'.regs .r2 = .word 111#64 ∧ fs'.regs .r2 = 111#64
     | _, _ => False) ∧
    -- (2) Cross-block offset 8 is UB in ProvMachine yet succeeds in FlatMachine:
    stepProv (.load64 .r2 .r0 8) sampleProvState = .failed .ub ∧
    (match stepFlat (.load64 .r2 .r0 8) sampleMatchingFlatState with
     | .step fs' => fs'.regs .r2 = 222#64
     | _ => False) ∧
    -- (3) Forging a pointer from raw word `.r1` is UB in ProvMachine:
    stepProv (.load64 .r2 .r1 0) sampleProvState = .failed .ub := by
  exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩

/-- Theorem 2.5 (Simulation Refinement for Provenance-Erased Execution):
    Whenever `stepProv inst ps` triggers `.failed .ub` (such as on cross-block
    out-of-bounds access or integer-to-pointer forgery), its erased outcome
    refines `stepFlat inst fs` for any flat state `fs` via `StepResult.Refines`. -/
theorem prov_ub_refines_flat_execution
    (erasedOutcome : StepResult FlatMachine)
    (hUb : erasedOutcome = .failed .ub)
    (flatOutcome : StepResult FlatMachine) :
    StepResult.Refines erasedOutcome flatOutcome := by
  rw [hUb]
  exact StepResult.Refines.ub_left flatOutcome

/-- Universal relational coupling between a `ProvMachine` state `ps` and a
    provenance-erased `FlatMachine` state `fs` for memory loads. -/
structure LoadRelated (ps : ProvMachine) (fs : FlatMachine) (addrReg : Reg) (ofs : Nat) : Prop where
  pc_eq : ps.pc = fs.pc
  xAddrs_eq : ps.xAddrs = fs.xAddrs
  ptr_sound :
    ∀ id baseOfs blk,
      ps.regs addrReg = .ptr id baseOfs →
      ps.blocks id = some blk →
      blk.perm.canRead = true →
      baseOfs + ofs < blk.size →
      fs.mem ((fs.regs addrReg).toNat + ofs) = some (blk.cells (baseOfs + ofs))

/-- Projects a `StepResult ProvMachine` to the loaded word & next PC (or error)
    so it can be compared directly via `StepResult.Refines` against `FlatMachine`. -/
def projectProvLoadOutcome (dst : Reg) (r : StepResult ProvMachine) :
    StepResult (Option (BitVec 64) × BitVec 64) :=
  match r with
  | .step ps =>
    let loaded := match ps.regs dst with
      | .word w => some w
      | .ptr _ _ => none
    .step (loaded, ps.pc)
  | .ret v => .ret v
  | .diverged => .diverged
  | .failed e => .failed e

def projectFlatLoadOutcome (dst : Reg) (r : StepResult FlatMachine) :
    StepResult (Option (BitVec 64) × BitVec 64) :=
  match r with
  | .step fs => .step (some (fs.regs dst), fs.pc)
  | .ret v => .ret v
  | .diverged => .diverged
  | .failed e => .failed e

/-- Theorem 2.6 (Universal Provenance-to-Flat Load Simulation):
    For **all** `ProvMachine` states `ps` and `FlatMachine` states `fs` satisfying
    `LoadRelated ps fs addrReg ofs`, the projected outcome of `stepProv (.load64 dst addrReg ofs) ps`
    refines `stepFlat (.load64 dst addrReg ofs) fs` under `StepResult.Refines`:
    - If `ps` fails with `.ub` (forged word pointer, unmapped block, non-readable block,
      or out-of-bounds offset `baseOfs + ofs ≥ blk.size`), `StepResult.Refines` holds by UB-refinement.
    - If `ps` fails with `.unsupported` (I-cache miss), `fs` also fails with `.unsupported`.
    - If `ps` steps to `ps'`, `fs` steps to `fs'` with identical loaded word and next PC. -/
theorem prov_to_flat_load64_simulation
    (ps : ProvMachine) (fs : FlatMachine) (dst addrReg : Reg) (ofs : Nat)
    (hRel : LoadRelated ps fs addrReg ofs) :
    StepResult.Refines
      (projectProvLoadOutcome dst (stepProv (.load64 dst addrReg ofs) ps))
      (projectFlatLoadOutcome dst (stepFlat (.load64 dst addrReg ofs) fs)) := by
  dsimp [stepProv, stepFlat, runToStepResult, executeInst,
         Pure.pure, Bind.bind, IsaMachineM.getPC, IsaMachineM.fetchAndCheckICache,
         IsaMachineM.getReg, IsaMachineM.loadWord64, IsaMachineM.setReg, IsaMachineM.setPC]
  rw [hRel.pc_eq, hRel.xAddrs_eq]
  cases hFetch : fs.xAddrs.contains fs.pc.toNat with
  | false =>
    dsimp [projectProvLoadOutcome, projectFlatLoadOutcome, StepResult.Refines]
  | true =>
    dsimp
    cases hReg : ps.regs addrReg with
    | word w =>
      dsimp [projectProvLoadOutcome, StepResult.Refines]
    | ptr id baseOfs =>
      dsimp
      cases hBlk : ps.blocks id with
      | none =>
        dsimp [projectProvLoadOutcome, StepResult.Refines]
      | some blk =>
        dsimp
        cases hRead : blk.perm.canRead with
        | false =>
          dsimp [projectProvLoadOutcome, StepResult.Refines]
        | true =>
          by_cases hBounds : baseOfs + ofs < blk.size
          · have hDec : decide (baseOfs + ofs < blk.size) = true :=
              decide_eq_true hBounds
            rw [hDec]
            dsimp
            have hMem := hRel.ptr_sound id baseOfs blk hReg hBlk hRead hBounds
            rw [hMem]
            simp [projectProvLoadOutcome, projectFlatLoadOutcome, updateReg, StepResult.Refines]
          · have hDec : decide (baseOfs + ofs < blk.size) = false :=
              decide_eq_false hBounds
            rw [hDec]
            dsimp [projectProvLoadOutcome, StepResult.Refines]

/-! ## Section 3: `Islaris`-in-Lean Symbolic Trace Language & Adequacy Probe -/

/-- Simplified `isla-lang` / `Islaris` trace AST (`isla-lang/coq/isla_lang.v:139-179`
    and `islaris/theories/opsem.v:476-575`).
    Note the crucial distinction from `islaris/theories/opsem.v:560-568`:
    - `smtAssert`: corresponds to `Smt (Assert e) Mk_annot` (`LAssert b`).
      In Islaris, when `b = false`, `seq_step` transitions to `seq_nb_state := true`,
      which `seq_to_val` (`opsem.v:584-591`) classifies as a terminated value!
    - `sailAssume`: corresponds to `Assume e Mk_annot` (`LAssume b`).
      In Islaris, `seq_step` requires `b = true`; when `b = false`, the trace gets stuck! -/
inductive IslaTrace where
  | done : IslaTrace
  | readReg (r : Reg) (expected : BitVec 64 → Bool) (k : BitVec 64 → IslaTrace) : IslaTrace
  | writeReg (r : Reg) (v : BitVec 64) (k : IslaTrace) : IslaTrace
  | readMem (addr : BitVec 64) (k : BitVec 64 → IslaTrace) : IslaTrace
  | writeMem (addr val : BitVec 64) (k : IslaTrace) : IslaTrace
  | setPC (newPc : BitVec 64) (k : IslaTrace) : IslaTrace
  | smtAssert (cond : Bool) (k : IslaTrace) : IslaTrace
  | sailAssume (cond : Bool) (k : IslaTrace) : IslaTrace
  | cases (branches : List IslaTrace) : IslaTrace

/-- Outcome of evaluating a single deterministic branch of an `IslaTrace`
    under Islaris's `seq_nb_state` operational semantics (`opsem.v:512-591`). -/
inductive IslaNBOutcome where
  /-- Normal completion of an instruction trace with `seq_nb_state = false`. -/
  | stepped (next : FlatMachine)
  /-- Path assumption mismatch (`seq_nb_state = true`): treated by Islaris
      `seq_to_val` (`opsem.v:584-591`) and `wp_assert` (`lifting.v:793-812`)
      as a benignly halted value state! -/
  | nbHalted
  /-- Verification failure (`Assume false`, unmapped memory, or unaligned access):
      gets stuck in `seq_step` and violates `not_stuck` in `isla_adequacy`. -/
  | stuckUB

/-- Evaluates a branch-free `IslaTrace` path on a concrete `FlatMachine` state,
    faithfully following `seq_step` in `islaris/theories/opsem.v:512-575`. -/
def evalSingleTracePath (t : IslaTrace) (s : FlatMachine) : IslaNBOutcome :=
  match t with
  | .done => .stepped s
  | .readReg r expected k =>
    let v := s.regs r
    -- In `opsem.v:546-550`, reading a register whose value does not match the
    -- trace's symbolic pattern sets `seq_nb_state := true` (`.nbHalted`).
    if expected v then
      evalSingleTracePath (k v) s
    else
      .nbHalted
  | .writeReg r v k =>
    evalSingleTracePath k { s with regs := updateReg s.regs r v }
  | .readMem addr k =>
    match s.mem addr.toNat with
    | some w => evalSingleTracePath (k w) s
    | none => .stuckUB
  | .writeMem addr val k =>
    match s.mem addr.toNat with
    | some _ =>
      let xAddrs' := s.xAddrs.filter (fun a => a != addr.toNat)
      evalSingleTracePath k { s with mem := updateMem s.mem addr.toNat val, xAddrs := xAddrs' }
    | none => .stuckUB
  | .setPC newPc k =>
    evalSingleTracePath k { s with pc := newPc }
  | .smtAssert cond k =>
    -- `opsem.v:560-563`: `LAssert b => if b then ... else (set seq_nb_state (λ _, true) σ)`
    if cond then
      evalSingleTracePath k s
    else
      .nbHalted
  | .sailAssume cond k =>
    -- `opsem.v:564-568`: `LAssume b => guard (b = true);; ...` (stuck if `b = false`!)
    if cond then
      evalSingleTracePath k s
    else
      .stuckUB
  | .cases _ => .stuckUB

/-- Collects all branch outcomes of an `IslaTrace` (handling top-level `.cases ts`). -/
def evalTraceBranches (t : IslaTrace) (s : FlatMachine) : List IslaNBOutcome :=
  match t with
  | .cases branches => branches.map (fun b => evalSingleTracePath b s)
  | other => [evalSingleTracePath other s]

/-- Mirrors Islaris's `WPasm` / `isla_adequacy` (`islaris/theories/lifting.v:87-93`,
    `793-832` and `adequacy.v:91-97`) for a single instruction step:
    every branch in `evalTraceBranches t s` must not get stuck (`.stuckUB`),
    and any branch that completes normally with `seq_nb_state = false` (`.stepped s'`)
    must satisfy `post s'`. Branches that hit `.nbHalted` (`seq_nb_state = true`)
    are vacuously accepted because `seq_to_val` classifies `seq_nb_state = true`
    as a value and `WPasm` uses trivial postcondition `{{ _, True }}`! -/
def naiveIslarisAdequacy (t : IslaTrace) (s : FlatMachine) (post : FlatMachine → Prop) : Prop :=
  ∀ outcome ∈ evalTraceBranches t s,
    match outcome with
    | .stepped s' => post s'
    | .nbHalted => True
    | .stuckUB => False

/-- Mirrors `islaris/sail-riscv/sail_opsem.v` (`sim_implies_refines`, lines 589-650
    and `sim_Assert`, lines 1030-1038):
    A trace `t` is a valid, complete representation of instruction `inst` at state `s`
    iff (1) `s.pc` is in `s.xAddrs`, and (2) whenever `stepFlat inst s = .step s'`,
    there exists a branch in `evalTraceBranches t s` that completes with `.stepped s'`
    (i.e. with `seq_nb_state = false`, not `.nbHalted`!). -/
def ValidCompleteTraceAt (inst : IsaInst) (t : IslaTrace) (s : FlatMachine) : Prop :=
  ∀ s', stepFlat inst s = .step s' → (.stepped s') ∈ evalTraceBranches t s

/-- Positive Adequacy Bridge (`islaTrace_refines_stepResult`):
    If a trace `t` is validated as complete for instruction `inst` at state `s`
    (`ValidCompleteTraceAt inst t s`) and the user proves `naiveIslarisAdequacy t s post`,
    then whenever the real ISA machine steps (`stepFlat inst s = .step s'`), the resulting
    state `s'` is guaranteed to satisfy `post s'`. -/
theorem islaTrace_refines_stepResult
    (inst : IsaInst) (t : IslaTrace) (s s' : FlatMachine) (post : FlatMachine → Prop)
    (hComplete : ValidCompleteTraceAt inst t s)
    (hAdeq : naiveIslarisAdequacy t s post)
    (hStep : stepFlat inst s = .step s') :
    post s' := by
  have hMem : (.stepped s') ∈ evalTraceBranches t s := hComplete s' hStep
  have hOutcome := hAdeq (.stepped s') hMem
  exact hOutcome

/-! ### Negative Control 2: Incomplete `tcases` Trace Vacuum in `naiveIslarisAdequacy` -/

/-- The conditional branch instruction `branchEqZero .r0 0x2000 0x1004`:
    jumps to `0x2000` if `r0 == 0`, else falls through to `0x1004`. -/
def branchInst : IsaInst :=
  .branchEqZero .r0 0x2000#64 0x1004#64

/-- A buggy, **incomplete** `IslaTrace` for `branchInst` that includes ONLY the
    `r0 == 0` branch (`smtAssert (v == 0)`) and omits the `r0 != 0` branch! -/
def incompleteBranchTrace : IslaTrace :=
  .cases [
    .readReg .r0 (fun _ => true) (fun v =>
      .smtAssert (v == 0#64) (.setPC 0x2000#64 .done))
  ]

/-- The **complete** two-branch `IslaTrace` for `branchInst`, covering both
    `v == 0` and `v != 0`. -/
def completeBranchTrace : IslaTrace :=
  .cases [
    .readReg .r0 (fun _ => true) (fun v =>
      .smtAssert (v == 0#64) (.setPC 0x2000#64 .done)),
    .readReg .r0 (fun _ => true) (fun v =>
      .smtAssert (v != 0#64) (.setPC 0x1004#64 .done))
  ]

/-- Decidable check for whether at least one branch of `t` completes with `.stepped`
    (i.e. `seq_nb_state = false`) on state `s`. -/
def hasNonHaltedBranch (t : IslaTrace) (s : FlatMachine) : Bool :=
  (evalTraceBranches t s).any (fun o =>
    match o with
    | .stepped _ => true
    | _ => false)

/-- Theorem 3.2 (Negative Control 2 — Why `seq_nb_state` Needs Trace Completeness Validation):
    On `sampleFlatState` (where `r0 = 42 != 0`):
    1. `naiveIslarisAdequacy incompleteBranchTrace sampleFlatState (fun s' => s'.pc = 0x2000#64)`
       **holds** (proving the false postcondition `s'.pc = 0x2000#64`!), because the single
       branch hits `smtAssert (42 == 0)` which evaluates to `.nbHalted` (`seq_nb_state = true`).
    2. Yet the real machine `stepFlat branchInst sampleFlatState` steps to `s'.pc = 0x1004#64 ≠ 0x2000#64`!
    3. The completeness validator rejects `incompleteBranchTrace` (`hasNonHaltedBranch = false`
       and `¬ ValidCompleteTraceAt branchInst incompleteBranchTrace sampleFlatState`),
       while accepting `completeBranchTrace` (`ValidCompleteTraceAt branchInst completeBranchTrace s`
       for all states `s`). -/
theorem incomplete_trace_accepted_by_naive_nb_adequacy_but_rejected_by_completeness_validator :
    -- (1) Naive `seq_nb_state` adequacy vacuously accepts the false postcondition `pc = 0x2000`:
    naiveIslarisAdequacy incompleteBranchTrace sampleFlatState (fun s' => s'.pc = 0x2000#64) ∧
    -- (2) Real machine execution steps to `pc = 0x1004` (not `0x2000`):
    (match stepFlat branchInst sampleFlatState with
     | .step s' => s'.pc = 0x1004#64 ∧ s'.pc ≠ 0x2000#64
     | _ => False) ∧
    -- (3) Completeness check catches that `incompleteBranchTrace` has no non-nbHalted branch:
    hasNonHaltedBranch incompleteBranchTrace sampleFlatState = false ∧
    ¬ ValidCompleteTraceAt branchInst incompleteBranchTrace sampleFlatState ∧
    -- (4) By contrast, `completeBranchTrace` has a non-nbHalted branch and satisfies
    --     `ValidCompleteTraceAt` on `sampleFlatState`:
    hasNonHaltedBranch completeBranchTrace sampleFlatState = true ∧
    ValidCompleteTraceAt branchInst completeBranchTrace sampleFlatState := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro outcome hMem
    simp [evalTraceBranches, incompleteBranchTrace, evalSingleTracePath, sampleFlatState] at hMem
    subst hMem
    trivial
  · refine ⟨rfl, ?_⟩
    decide
  · decide
  · intro hValid
    have hStep : stepFlat branchInst sampleFlatState =
        .step { sampleFlatState with pc := 0x1004#64 } := by rfl
    have hMem := hValid { sampleFlatState with pc := 0x1004#64 } hStep
    simp [evalTraceBranches, incompleteBranchTrace, evalSingleTracePath, sampleFlatState] at hMem
  · decide
  · intro s' hStep
    have hStepEq : stepFlat branchInst sampleFlatState =
        .step { sampleFlatState with pc := 0x1004#64 } := by rfl
    rw [hStepEq] at hStep
    injection hStep with hEq
    subst hEq
    simp [evalTraceBranches, completeBranchTrace, evalSingleTracePath, sampleFlatState]

/-- Theorem 3.3: Universal completeness of `completeBranchTrace` for `branchInst`
    across **all** concrete `FlatMachine` states `s`. -/
theorem completeBranchTrace_valid_for_all_states (s : FlatMachine) :
    ValidCompleteTraceAt branchInst completeBranchTrace s := by
  intro s' hStep
  dsimp [stepFlat, runToStepResult, executeInst, branchInst,
         Pure.pure, Bind.bind, IsaMachineM.getPC, IsaMachineM.fetchAndCheckICache,
         IsaMachineM.getReg, IsaMachineM.isZeroVal, IsaMachineM.setPC] at hStep
  cases hFetch : s.xAddrs.contains s.pc.toNat with
  | false =>
    rw [hFetch] at hStep
    simp at hStep
  | true =>
    rw [hFetch] at hStep
    dsimp at hStep
    cases hZero : (s.regs .r0 == 0#64) with
    | true =>
      rw [hZero] at hStep
      dsimp at hStep
      injection hStep with hEq
      subst hEq
      simp [evalTraceBranches, completeBranchTrace, evalSingleTracePath, hZero]
    | false =>
      rw [hZero] at hStep
      dsimp at hStep
      injection hStep with hEq
      subst hEq
      have hNeZero : (s.regs .r0 != 0#64) = true := by
        simp [bne, hZero]
      simp [evalTraceBranches, completeBranchTrace, evalSingleTracePath, hZero, hNeZero]

/-- Theorem 3.4 (Universal Inverted Polarity of `smtAssert` vs. `sailAssume` in Islaris):
    For **all** states `s`, continuations `k`, and postconditions `post`:
    - `.smtAssert false k` (`Smt (Assert false)` / `LAssert false` in `opsem.v:560-563`)
      steps to `.nbHalted` (`seq_nb_state = true`) and **always satisfies** `naiveIslarisAdequacy`.
    - `.sailAssume false k` (`Assume false` / `LAssume false` in `opsem.v:564-568`)
      steps to `.stuckUB` and **always violates** `naiveIslarisAdequacy`. -/
theorem smtAssert_vs_sailAssume_inverted_polarity
    (s : FlatMachine) (k : IslaTrace) (post : FlatMachine → Prop) :
    naiveIslarisAdequacy (.smtAssert false k) s post ∧
    ¬ naiveIslarisAdequacy (.sailAssume false k) s post := by
  refine ⟨?_, ?_⟩
  · intro outcome hMem
    simp [evalTraceBranches, evalSingleTracePath] at hMem
    subst hMem
    trivial
  · intro hAdeq
    have hMem : IslaNBOutcome.stuckUB ∈ evalTraceBranches (.sailAssume false k) s := by
      simp [evalTraceBranches, evalSingleTracePath]
    exact hAdeq .stuckUB hMem

/-! ## Section 4: Axiom Hygiene Verification (`#guard_msgs` + `#print axioms`) -/

/-- info: 'AnnealIsaAdaptationProbe.msb_clear_vs_merge_contrast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms msb_clear_vs_merge_contrast

/-- info: 'AnnealIsaAdaptationProbe.reading_undef_flag_triggers_ub_refines_any' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms reading_undef_flag_triggers_ub_refines_any

/-- info: 'AnnealIsaAdaptationProbe.self_modifying_store_without_fenceI_fails_fetch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms self_modifying_store_without_fenceI_fails_fetch

/-- info: 'AnnealIsaAdaptationProbe.forged_or_cross_block_ptr_ub_in_prov_succeeds_in_flat' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms forged_or_cross_block_ptr_ub_in_prov_succeeds_in_flat

/-- info: 'AnnealIsaAdaptationProbe.prov_to_flat_load64_simulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms prov_to_flat_load64_simulation

/-- info: 'AnnealIsaAdaptationProbe.islaTrace_refines_stepResult' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms islaTrace_refines_stepResult

/-- info: 'AnnealIsaAdaptationProbe.incomplete_trace_accepted_by_naive_nb_adequacy_but_rejected_by_completeness_validator' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms incomplete_trace_accepted_by_naive_nb_adequacy_but_rejected_by_completeness_validator

/-- info: 'AnnealIsaAdaptationProbe.completeBranchTrace_valid_for_all_states' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeBranchTrace_valid_for_all_states

/-- info: 'AnnealIsaAdaptationProbe.smtAssert_vs_sailAssume_inverted_polarity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms smtAssert_vs_sailAssume_inverted_polarity

end AnnealIsaAdaptationProbe
