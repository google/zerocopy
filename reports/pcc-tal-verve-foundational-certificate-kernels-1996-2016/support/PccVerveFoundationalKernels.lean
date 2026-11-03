/-
  PccVerveFoundationalKernels.lean
  Certificate-Verifying Kernels — Foundational PCC, TAL,
  Verve OS Two-Regime Seam, and Certified Kernel Extension Admission (1996–2016).

  Toolchain: Lean 4.34.1 (`leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`)
  Axiom Audit: Zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`.
-/

namespace PccVerveFoundationalKernels

/-!
## Constructive Arithmetic & Boolean Helpers (Axiom-Free)

We use primitive recursive `Nat.beq` and `Nat.ble` with structural induction lemmas
so that no proof ever invokes `Decidable` / `LawfulBEq` instances that depend on
`Classical.choice`.
-/

theorem nat_beq_refl : (n : Nat) → Nat.beq n n = true
  | 0 => rfl
  | n + 1 => nat_beq_refl n

theorem nat_beq_eq : {a b : Nat} → Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (nat_beq_eq h)

/-- Strict inequality `a < b` in `Bool`, defined constructively as `Nat.ble (a + 1) b`. -/
def natBlt (a b : Nat) : Bool := Nat.ble (a + 1) b

theorem nat_ble_refl : (n : Nat) → Nat.ble n n = true
  | 0 => rfl
  | n + 1 => nat_ble_refl n

theorem nat_ble_add_right : (a k : Nat) → Nat.ble a (a + k) = true
  | 0, _ => rfl
  | a + 1, k => by
      rw [Nat.succ_add]
      exact nat_ble_add_right a k

theorem natBlt_add_left : (k a b : Nat) → natBlt a b = true → natBlt (k + a) (k + b) = true
  | 0, a, b, h => by
      unfold natBlt at h ⊢
      rw [Nat.zero_add, Nat.zero_add]
      exact h
  | k + 1, a, b, h => by
      unfold natBlt
      rw [Nat.succ_add, Nat.succ_add, Nat.succ_add]
      exact natBlt_add_left k a b h

theorem nat_ble_trans : (a b c : Nat) →
    Nat.ble a b = true → Nat.ble b c = true → Nat.ble a c = true
  | 0, _, _, _, _ => rfl
  | _ + 1, 0, _, hab, _ => Bool.noConfusion hab
  | _ + 1, _ + 1, 0, _, hbc => Bool.noConfusion hbc
  | a + 1, b + 1, c + 1, hab, hbc => nat_ble_trans a b c hab hbc

theorem nat_ble_add_right_mono : {a b : Nat} → (k : Nat) →
    Nat.ble a b = true → Nat.ble (a + k) (b + k) = true
  | a, b, 0, h => by
      rw [Nat.add_zero, Nat.add_zero]
      exact h
  | a, b, k + 1, h => by
      rw [Nat.add_succ, Nat.add_succ]
      exact nat_ble_add_right_mono k h

theorem nat_ble_succ_of_ble_false : (bound r : Nat) →
    Nat.ble bound r = false → Nat.ble (r + 1) bound = true
  | 0, _, h => Bool.noConfusion h
  | _ + 1, 0, _ => rfl
  | bound + 1, r + 1, h => nat_ble_succ_of_ble_false bound r h

/-!
## Part 1: Necula & Lee OSDI 1996 / CMU-CS-98-154 Cutpoint-Annotated PCC Kernel Extension Loader

Models the DEC Alpha / SAL machine-code verification condition generator (`VCGen`)
and LF proof certificate checker from:
- George C. Necula & Peter Lee, *Safe Kernel Extensions Without Run-Time Checking*,
  OSDI 1996, pp. 229–243 (DOI `10.1145/238721.238781`), §3–§4, Table 1.
- George C. Necula, *Compiling with Proofs*, CMU-CS-98-154, Sept 1998, Fig. 4.6 (`SE`),
  Theorem 4.3 (`Safety of VCGen`), and §3.4.3 (`SafeRET_F`).
-/

/-- Register identifiers for our kernel-extension RISC/Alpha machine:
    - `r0`: return value / accumulator
    - `r1`: packet buffer base address (`pktBase`)
    - `r2`: packet buffer length (`pktLen`)
    - `r3`: scratch memory base address (`scratchBase`)
    - `r4`: general-purpose working register / offset
    - `rFp`: callee-saved kernel frame pointer (`CS_F` in CMU-CS-98-154 §3.4.3)
    - `rIpl`: callee-saved kernel interrupt priority level / status mask -/
inductive Reg where
  | r0 : Reg
  | r1 : Reg
  | r2 : Reg
  | r3 : Reg
  | r4 : Reg
  | rFp : Reg
  | rIpl : Reg
  deriving DecidableEq, Repr

/-- Register file mapping each `Reg` to a natural number word. -/
structure RegFile where
  r0 : Nat
  r1 : Nat
  r2 : Nat
  r3 : Nat
  r4 : Nat
  rFp : Nat
  rIpl : Nat
  deriving DecidableEq, Repr

def RegFile.get (rf : RegFile) : Reg → Nat
  | .r0 => rf.r0
  | .r1 => rf.r1
  | .r2 => rf.r2
  | .r3 => rf.r3
  | .r4 => rf.r4
  | .rFp => rf.rFp
  | .rIpl => rf.rIpl

def RegFile.set (rf : RegFile) (r : Reg) (v : Nat) : RegFile :=
  match r with
  | .r0 => { rf with r0 := v }
  | .r1 => { rf with r1 := v }
  | .r2 => { rf with r2 := v }
  | .r3 => { rf with r3 := v }
  | .r4 => { rf with r4 := v }
  | .rFp => { rf with rFp := v }
  | .rIpl => { rf with rIpl := v }

/-- Kernel extension safety policy (OSDI '96 §3.1, CMU-CS-98-154 §8.1):
    - Readable packet buffer `[pktBase, pktBase + pktLen)`
    - Writable scratch region `[scratchBase, scratchBase + scratchLen)`
    - Required initial values of callee-saved kernel registers `initFp` and `initIpl` -/
structure SafetyPolicy where
  pktBase : Nat
  pktLen : Nat
  scratchBase : Nat
  scratchLen : Nat
  initFp : Nat
  initIpl : Nat
  deriving DecidableEq, Repr

/-- Address `addr` is a valid readable address (either inside the packet buffer
    or inside the extension's writable scratch memory). -/
def SafetyPolicy.validRead (pol : SafetyPolicy) (addr : Nat) : Bool :=
  (Nat.ble pol.pktBase addr && natBlt addr (pol.pktBase + pol.pktLen)) ||
  (Nat.ble pol.scratchBase addr && natBlt addr (pol.scratchBase + pol.scratchLen))

/-- Address `addr` is a valid writable address (strictly inside the extension's
    scratch memory `[scratchBase, scratchBase + scratchLen)`). -/
def SafetyPolicy.validWrite (pol : SafetyPolicy) (addr : Nat) : Bool :=
  Nat.ble pol.scratchBase addr && natBlt addr (pol.scratchBase + pol.scratchLen)

/-- Non-aliasing precondition from Necula & Lee OSDI '96 §3.1 (`necula96_osdi.txt:775`):
    the packet buffer and scratch memory are disjoint. -/
def SafetyPolicy.regionsDisjoint (pol : SafetyPolicy) : Bool :=
  Nat.ble (pol.pktBase + pol.pktLen) pol.scratchBase ||
  Nat.ble (pol.scratchBase + pol.scratchLen) pol.pktBase

/-- KernelABI preservation predicate (`SafeRET_F` in CMU-CS-98-154 §3.4.3, p. 49):
    upon `ret`, callee-saved registers `rFp` and `rIpl` must equal their entry values. -/
def SafetyPolicy.preservesKernelABI (pol : SafetyPolicy) (rf : RegFile) : Bool :=
  Nat.beq rf.rFp pol.initFp && Nat.beq rf.rIpl pol.initIpl

/-- Cutpoint-annotated RISC/Alpha instruction set (`SAL` in CMU-CS-98-154 Fig. 4.4):
    - `movi dst imm`: `dst := imm`
    - `addi dst src imm`: `dst := src + imm`
    - `load dst base off`: `dst := Mem[base + off]`
    - `store base off src`: `Mem[base + off] := src`
    - `bge reg bound target`: if `reg ≥ bound` jump to `target` else fall through
    - `jmp target`: unconditional jump to `target`
    - `inv cutId`: loop-invariant cutpoint marker (`INV` pseudo-instruction)
    - `ret`: return to host kernel -/
inductive Instr where
  | movi (dst : Reg) (imm : Nat)
  | addi (dst : Reg) (src : Reg) (imm : Nat)
  | load (dst : Reg) (base : Reg) (off : Nat)
  | store (base : Reg) (off : Nat) (src : Reg)
  | bge (reg : Reg) (bound : Nat) (target : Nat)
  | jmp (target : Nat)
  | inv (cutId : Nat)
  | ret
  deriving DecidableEq, Repr

/-- Machine state of an executing kernel extension. -/
structure MachineState where
  pc : Nat
  regs : RegFile
  mem : Nat → Nat
  halted : Bool

/-- Update memory at address `a` with value `v`. -/
def updateMem (m : Nat → Nat) (a v : Nat) : Nat → Nat :=
  fun x => if Nat.beq x a then v else m x

/-- Fetch instruction at `pc` from `prog`. -/
def fetchInstr : List Instr → Nat → Option Instr
  | [], _ => none
  | i :: _, 0 => some i
  | _ :: rest, n + 1 => fetchInstr rest n

/-- Immediate single-step safety predicate (`SafeStep`) checked at the current PC:
    - `load` must read from a valid readable address (`pol.validRead`).
    - `store` must write to a valid writable address (`pol.validWrite`).
    - `ret` must preserve the kernel's callee-saved ABI (`pol.preservesKernelABI`).
    - Branch/jump targets must lie within `prog.length`. -/
def SafeStep (prog : List Instr) (pol : SafetyPolicy) (s : MachineState) : Bool :=
  if s.halted then true
  else
    match fetchInstr prog s.pc with
    | none => false
    | some (.movi _ _) => natBlt (s.pc + 1) prog.length
    | some (.addi _ _ _) => natBlt (s.pc + 1) prog.length
    | some (.load _ base off) =>
        pol.validRead (s.regs.get base + off) && natBlt (s.pc + 1) prog.length
    | some (.store base off _) =>
        pol.validWrite (s.regs.get base + off) && natBlt (s.pc + 1) prog.length
    | some (.bge _ _ target) =>
        natBlt target prog.length && natBlt (s.pc + 1) prog.length
    | some (.jmp target) =>
        natBlt target prog.length
    | some (.inv _) =>
        natBlt (s.pc + 1) prog.length
    | some .ret =>
        pol.preservesKernelABI s.regs

/-- Operational semantics of a single instruction step (zero runtime checks!). -/
def stepInstr (prog : List Instr) (s : MachineState) : MachineState :=
  if s.halted then s
  else
    match fetchInstr prog s.pc with
    | none => { s with halted := true }
    | some (.movi dst imm) =>
        { s with pc := s.pc + 1, regs := s.regs.set dst imm }
    | some (.addi dst src imm) =>
        { s with pc := s.pc + 1, regs := s.regs.set dst (s.regs.get src + imm) }
    | some (.load dst base off) =>
        let addr := s.regs.get base + off
        { s with pc := s.pc + 1, regs := s.regs.set dst (s.mem addr) }
    | some (.store base off src) =>
        let addr := s.regs.get base + off
        { s with pc := s.pc + 1, mem := updateMem s.mem addr (s.regs.get src) }
    | some (.bge reg bound target) =>
        if Nat.ble bound (s.regs.get reg) then
          { s with pc := target }
        else
          { s with pc := s.pc + 1 }
    | some (.jmp target) =>
        { s with pc := target }
    | some (.inv _) =>
        { s with pc := s.pc + 1 }
    | some .ret =>
        { s with halted := true }

/-- Iterate `stepInstr` for `n` steps. -/
def stepN (prog : List Instr) : Nat → MachineState → MachineState
  | 0, s => s
  | n + 1, s => stepN prog n (stepInstr prog s)

/-- Run the machine for `fuel` steps, returning `true` iff every step satisfies `SafeStep`. -/
def runSafeFor (prog : List Instr) (pol : SafetyPolicy) : Nat → MachineState → Bool
  | 0, _ => true
  | fuel + 1, s =>
      SafeStep prog pol s && runSafeFor prog pol fuel (stepInstr prog s)

/-- Check whether instruction at `target` in `prog` is an `inv` cutpoint marker.
    In Necula's `SE` (CMU-CS-98-154 Fig. 4.6, `necula98_thesis.txt:3834`), every
    backward branch (`target ≤ pc`) MUST target an `inv` instruction. -/
def isInvAt (prog : List Instr) (target : Nat) : Bool :=
  match fetchInstr prog target with
  | some (.inv _) => true
  | _ => false

/-- Check that every backward jump/branch (`target ≤ pc`) in `prog` lands on an `inv`
    cutpoint instruction (`dominatesAllBackEdges`). -/
def dominatesAllBackEdgesAux (prog : List Instr) : Nat → List Instr → Bool
  | _, [] => true
  | pc, instr :: rest =>
      let okHere :=
        match instr with
        | .jmp target => if Nat.ble target pc then isInvAt prog target else true
        | .bge _ _ target => if Nat.ble target pc then isInvAt prog target else true
        | _ => true
      okHere && dominatesAllBackEdgesAux prog (pc + 1) rest

def dominatesAllBackEdges (prog : List Instr) : Bool :=
  dominatesAllBackEdgesAux prog 0 prog

/-- Abstract range descriptor for `r4` (offset register) and ABI preservation at each PC,
    representing the cutpoint/block assertions checked by the LF proof checker. -/
structure PCAssertion where
  /-- Upper bound `r4 ≤ maxR4` guaranteed at this PC (`none` if unconstrained). -/
  maxR4 : Option Nat
  /-- Whether `r1 = pol.pktBase`, `r3 = pol.scratchBase`, `rFp = pol.initFp`,
      and `rIpl = pol.initIpl` hold at this PC. -/
  abiAndBasesIntact : Bool
  deriving DecidableEq, Repr

/-- Default contradictory assertion returned for out-of-range PCs. -/
def defaultAssertion : PCAssertion :=
  { maxR4 := some 0, abiAndBasesIntact := false }

/-- Total lookup of the assertion at `pc` in certificate `cert`. -/
def lookupAssertion : List PCAssertion → Nat → PCAssertion
  | [], _ => defaultAssertion
  | a :: _, 0 => a
  | _ :: rest, n + 1 => lookupAssertion rest n

/-- Semantic meaning of a `PCAssertion` on a concrete `MachineState`. -/
def PCAssertion.holds (pol : SafetyPolicy) (a : PCAssertion) (s : MachineState) : Bool :=
  let basesOk :=
    if a.abiAndBasesIntact then
      Nat.beq s.regs.r1 pol.pktBase &&
      Nat.beq s.regs.r3 pol.scratchBase &&
      Nat.beq s.regs.rFp pol.initFp &&
      Nat.beq s.regs.rIpl pol.initIpl
    else true
  let r4Ok :=
    match a.maxR4 with
    | none => true
    | some bound => Nat.ble s.regs.r4 bound
  basesOk && r4Ok

/-- Check implication `aSrc ⊢ aDst` between two `PCAssertion`s. -/
def impliesAssertion (aSrc aDst : PCAssertion) : Bool :=
  (if aDst.abiAndBasesIntact then aSrc.abiAndBasesIntact else true) &&
  (match aDst.maxR4 with
   | none => true
   | some dstBound =>
       match aSrc.maxR4 with
       | none => false
       | some srcBound => Nat.ble srcBound dstBound)

/-- Check that `aSrc` after `r4 := imm` implies `aDst`. -/
def impliesAfterMovR4 (aSrc : PCAssertion) (imm : Nat) (aDst : PCAssertion) : Bool :=
  (if aDst.abiAndBasesIntact then aSrc.abiAndBasesIntact else true) &&
  (match aDst.maxR4 with
   | none => true
   | some dstBound => Nat.ble imm dstBound)

/-- Check that `aSrc` after `r4 := r4 + imm` implies `aDst`. -/
def impliesAfterAddR4 (aSrc : PCAssertion) (imm : Nat) (aDst : PCAssertion) : Bool :=
  (if aDst.abiAndBasesIntact then aSrc.abiAndBasesIntact else true) &&
  (match aDst.maxR4 with
   | none => true
   | some dstBound =>
       match aSrc.maxR4 with
       | none => false
       | some srcBound => Nat.ble (srcBound + imm) dstBound)

/-- Check that `aSrc` on the fall-through branch of `bge r4 bound target`
    (where `r4 < bound`, so `r4 + 1 ≤ bound`) implies `aDst`. -/
def impliesFallthroughBgeR4 (aSrc : PCAssertion) (bound : Nat) (aDst : PCAssertion) : Bool :=
  (if aDst.abiAndBasesIntact then aSrc.abiAndBasesIntact else true) &&
  (match aDst.maxR4 with
   | none => true
   | some dstBound => Nat.ble bound (dstBound + 1))

/-- Verify local VC obligation and successor implication at a single PC (`checkInstrVC`). -/
def checkInstrVC (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion)
    (pc : Nat) (instr : Instr) (a : PCAssertion) : Bool :=
  match instr with
  | .movi .r0 _ =>
      natBlt (pc + 1) prog.length &&
      impliesAssertion a (lookupAssertion cert (pc + 1))
  | .movi .r4 imm =>
      natBlt (pc + 1) prog.length &&
      impliesAfterMovR4 a imm (lookupAssertion cert (pc + 1))
  | .movi _ _ => false
  | .addi .r4 .r4 imm =>
      natBlt (pc + 1) prog.length &&
      impliesAfterAddR4 a imm (lookupAssertion cert (pc + 1))
  | .addi _ _ _ => false
  | .load .r0 .r1 off =>
      a.abiAndBasesIntact &&
      natBlt off pol.pktLen &&
      natBlt (pc + 1) prog.length &&
      impliesAssertion a (lookupAssertion cert (pc + 1))
  | .load .r0 .r3 off =>
      a.abiAndBasesIntact &&
      natBlt off pol.scratchLen &&
      natBlt (pc + 1) prog.length &&
      impliesAssertion a (lookupAssertion cert (pc + 1))
  | .load _ _ _ => false
  | .store .r3 off _ =>
      a.abiAndBasesIntact &&
      natBlt off pol.scratchLen &&
      natBlt (pc + 1) prog.length &&
      impliesAssertion a (lookupAssertion cert (pc + 1))
  | .store _ _ _ => false
  | .bge .r4 bound target =>
      natBlt target prog.length &&
      natBlt (pc + 1) prog.length &&
      impliesAssertion a (lookupAssertion cert target) &&
      impliesFallthroughBgeR4 a bound (lookupAssertion cert (pc + 1))
  | .bge _ _ _ => false
  | .jmp target =>
      natBlt target prog.length &&
      impliesAssertion a (lookupAssertion cert target)
  | .inv _ =>
      natBlt (pc + 1) prog.length &&
      impliesAssertion a (lookupAssertion cert (pc + 1))
  | .ret =>
      a.abiAndBasesIntact

/-- Check all instructions in `prog` against certificate `cert`. -/
def checkAllInstrVCs (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion) :
    Nat → List Instr → Bool
  | _, [] => true
  | pc, i :: irest =>
      checkInstrVC prog pol cert pc i (lookupAssertion cert pc) &&
      checkAllInstrVCs prog pol cert (pc + 1) irest

/-- Top-level PCC certificate checker (`checkCert`):
    1. Checks `dominatesAllBackEdges prog` (every backward jump/branch targets `inv`).
    2. Checks `natBlt 0 prog.length` (non-empty program) and entry assertion `maxR4.isNone`.
    3. Checks `checkAllInstrVCs prog pol cert 0 prog`. -/
def checkCert (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion) : Bool :=
  dominatesAllBackEdges prog &&
  natBlt 0 prog.length &&
  (lookupAssertion cert 0).maxR4.isNone &&
  checkAllInstrVCs prog pol cert 0 prog

/-- Valid kernel entry state `InitKernelState pol s₀`. -/
def InitKernelState (pol : SafetyPolicy) (s : MachineState) : Bool :=
  Nat.beq s.pc 0 &&
  (!s.halted) &&
  Nat.beq s.regs.r1 pol.pktBase &&
  Nat.beq s.regs.r3 pol.scratchBase &&
  Nat.beq s.regs.rFp pol.initFp &&
  Nat.beq s.regs.rIpl pol.initIpl

/-- Concrete Example: Necula & Lee OSDI '96 Packet Filter 1 (`filter1Prog`),
    which loads Ethernet type word (`r1 + 12`), stores to scratch (`r3 + 0`),
    loops over header words with an `inv` cutpoint at PC 3, and returns cleanly. -/
def filter1Policy : SafetyPolicy :=
  { pktBase := 1000
  , pktLen := 64
  , scratchBase := 2000
  , scratchLen := 16
  , initFp := 9000
  , initIpl := 7 }

def filter1Prog : List Instr :=
  [ .load .r0 .r1 12      -- PC 0: load EtherType at pktBase + 12
  , .store .r3 0 .r0      -- PC 1: spill to scratchBase + 0
  , .movi .r4 0           -- PC 2: initialize loop counter r4 := 0
  , .inv 0                -- PC 3: loop cutpoint (r4 <= 4)
  , .bge .r4 4 7          -- PC 4: if r4 >= 4 jump to PC 7 (ret)
  , .addi .r4 .r4 1       -- PC 5: r4 := r4 + 1
  , .jmp 3                -- PC 6: back-edge jump to cutpoint PC 3
  , .ret                  -- PC 7: return to kernel
  ]

def filter1Cert : List PCAssertion :=
  [ { maxR4 := none,   abiAndBasesIntact := true } -- PC 0
  , { maxR4 := none,   abiAndBasesIntact := true } -- PC 1
  , { maxR4 := none,   abiAndBasesIntact := true } -- PC 2
  , { maxR4 := some 4, abiAndBasesIntact := true } -- PC 3 (cutpoint invariant: r4 <= 4)
  , { maxR4 := some 4, abiAndBasesIntact := true } -- PC 4
  , { maxR4 := some 3, abiAndBasesIntact := true } -- PC 5 (fallthrough of r4 < 4: r4 <= 3)
  , { maxR4 := some 4, abiAndBasesIntact := true } -- PC 6 (after r4 + 1: r4 <= 4)
  , { maxR4 := some 4, abiAndBasesIntact := true } -- PC 7 (ret)
  ]

/-- Theorem: Necula & Lee's PCC checker admits `filter1Prog` with `filter1Cert`
    and `dominatesAllBackEdges` holds. -/
theorem filter1_pcc_verified :
    checkCert filter1Prog filter1Policy filter1Cert = true := rfl

def filter1InitState : MachineState :=
  { pc := 0
  , regs := { r0 := 0, r1 := 1000, r2 := 64, r3 := 2000, r4 := 0, rFp := 9000, rIpl := 7 }
  , mem := fun _ => 0x0800
  , halted := false }

/-- Theorem: Running `filter1Prog` from the canonical entry state executes to
    completion in 22 steps with `runSafeFor = true` and zero runtime checks. -/
theorem filter1_executes_safely :
    runSafeFor filter1Prog filter1Policy 22 filter1InitState = true ∧
    (stepN filter1Prog 22 filter1InitState).halted = true :=
  ⟨rfl, rfl⟩

/-- Inductive state invariant induced by `cert`:
    Either `s.halted = true`, or `s.pc < prog.length` and `(lookupAssertion cert s.pc).holds pol s = true`. -/
def PCCStateInv (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion)
    (s : MachineState) : Bool :=
  if s.halted then true
  else
    natBlt s.pc prog.length &&
    (lookupAssertion cert s.pc).holds pol s

/-- Structural lemma: if `natBlt pc rest.length = true`, `fetchInstr rest pc` returns `some instr`. -/
theorem fetchInstr_some_of_blt :
    (rest : List Instr) → (pc : Nat) → natBlt pc rest.length = true →
    ∃ instr, fetchInstr rest pc = some instr
  | [], _, h => Bool.noConfusion h
  | i :: _, 0, _ => ⟨i, rfl⟩
  | _ :: rest, pc + 1, h => fetchInstr_some_of_blt rest pc h

/-- Structural lemma: if `checkAllInstrVCs prog pol cert basePc rest = true` and
    `fetchInstr rest idx = some instr`, then `checkInstrVC` holds at `basePc + idx`. -/
theorem checkAllInstrVCs_at_fetch
    (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion) :
    (basePc idx : Nat) → (rest : List Instr) → (instr : Instr) →
    checkAllInstrVCs prog pol cert basePc rest = true →
    fetchInstr rest idx = some instr →
    checkInstrVC prog pol cert (basePc + idx) instr (lookupAssertion cert (basePc + idx)) = true
  | basePc, 0, i :: _, instr, hAll, hFetch => by
      unfold fetchInstr at hFetch
      injection hFetch with hEq
      subst hEq
      unfold checkAllInstrVCs at hAll
      rw [Nat.add_zero]
      exact (Bool.and_eq_true_iff.mp hAll).1
  | basePc, idx + 1, _ :: rest, instr, hAll, hFetch => by
      unfold fetchInstr at hFetch
      unfold checkAllInstrVCs at hAll
      have hRest := (Bool.and_eq_true_iff.mp hAll).2
      have ih := checkAllInstrVCs_at_fetch prog pol cert (basePc + 1) idx rest instr hRest hFetch
      rw [Nat.add_right_comm, Nat.add_assoc] at ih
      exact ih

theorem checkAllInstrVCs_at_pc
    (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion)
    (pc : Nat) (instr : Instr)
    (hAll : checkAllInstrVCs prog pol cert 0 prog = true)
    (hFetch : fetchInstr prog pc = some instr) :
    checkInstrVC prog pol cert pc instr (lookupAssertion cert pc) = true := by
  have h := checkAllInstrVCs_at_fetch prog pol cert 0 pc prog instr hAll hFetch
  rw [Nat.zero_add] at h
  exact h

/-- Implication preservation helper for instructions that do not modify `r1, r3, r4, rFp, rIpl`. -/
theorem impliesAssertion_preserves_holds
    (pol : SafetyPolicy) (aSrc aDst : PCAssertion) (s s' : MachineState)
    (hHolds : aSrc.holds pol s = true)
    (hImp : impliesAssertion aSrc aDst = true)
    (hR1 : s'.regs.r1 = s.regs.r1)
    (hR3 : s'.regs.r3 = s.regs.r3)
    (hR4 : s'.regs.r4 = s.regs.r4)
    (hFp : s'.regs.rFp = s.regs.rFp)
    (hIpl : s'.regs.rIpl = s.regs.rIpl) :
    aDst.holds pol s' = true := by
  unfold PCAssertion.holds at hHolds ⊢
  unfold impliesAssertion at hImp
  rw [hR1, hR3, hR4, hFp, hIpl]
  rcases Bool.and_eq_true_iff.mp hHolds with ⟨hBasesSrc, hR4Src⟩
  rcases Bool.and_eq_true_iff.mp hImp with ⟨hBasesImp, hR4Imp⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, ?_⟩
  · cases hDstAbi : aDst.abiAndBasesIntact
    · rfl
    · rw [hDstAbi] at hBasesImp
      change aSrc.abiAndBasesIntact = true at hBasesImp
      rw [hBasesImp] at hBasesSrc
      exact hBasesSrc
  · cases hDstR4 : aDst.maxR4 with
    | none => rfl
    | some dstBound =>
        rw [hDstR4] at hR4Imp
        cases hSrcR4 : aSrc.maxR4 with
        | none =>
            rw [hSrcR4] at hR4Imp
            exact Bool.noConfusion hR4Imp
        | some srcBound =>
            rw [hSrcR4] at hR4Imp hR4Src
            exact nat_ble_trans s.regs.r4 srcBound dstBound hR4Src hR4Imp

theorem impliesAfterMovR4_preserves_holds
    (pol : SafetyPolicy) (aSrc aDst : PCAssertion) (s : MachineState) (imm nextPc : Nat)
    (hHolds : aSrc.holds pol s = true)
    (hImp : impliesAfterMovR4 aSrc imm aDst = true) :
    aDst.holds pol { s with pc := nextPc, regs := s.regs.set .r4 imm } = true := by
  unfold PCAssertion.holds at hHolds ⊢
  unfold impliesAfterMovR4 at hImp
  unfold RegFile.set
  rcases Bool.and_eq_true_iff.mp hHolds with ⟨hBasesSrc, _⟩
  rcases Bool.and_eq_true_iff.mp hImp with ⟨hBasesImp, hR4Imp⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, ?_⟩
  · cases hDstAbi : aDst.abiAndBasesIntact
    · rfl
    · rw [hDstAbi] at hBasesImp
      change aSrc.abiAndBasesIntact = true at hBasesImp
      rw [hBasesImp] at hBasesSrc
      exact hBasesSrc
  · cases hDstR4 : aDst.maxR4 with
    | none => rfl
    | some dstBound =>
        rw [hDstR4] at hR4Imp
        exact hR4Imp

theorem impliesAfterAddR4_preserves_holds
    (pol : SafetyPolicy) (aSrc aDst : PCAssertion) (s : MachineState) (imm nextPc : Nat)
    (hHolds : aSrc.holds pol s = true)
    (hImp : impliesAfterAddR4 aSrc imm aDst = true) :
    aDst.holds pol { s with pc := nextPc, regs := s.regs.set .r4 (s.regs.r4 + imm) } = true := by
  unfold PCAssertion.holds at hHolds ⊢
  unfold impliesAfterAddR4 at hImp
  unfold RegFile.set
  rcases Bool.and_eq_true_iff.mp hHolds with ⟨hBasesSrc, hR4Src⟩
  rcases Bool.and_eq_true_iff.mp hImp with ⟨hBasesImp, hR4Imp⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, ?_⟩
  · cases hDstAbi : aDst.abiAndBasesIntact
    · rfl
    · rw [hDstAbi] at hBasesImp
      change aSrc.abiAndBasesIntact = true at hBasesImp
      rw [hBasesImp] at hBasesSrc
      exact hBasesSrc
  · cases hDstR4 : aDst.maxR4 with
    | none => rfl
    | some dstBound =>
        rw [hDstR4] at hR4Imp
        cases hSrcR4 : aSrc.maxR4 with
        | none =>
            rw [hSrcR4] at hR4Imp
            exact Bool.noConfusion hR4Imp
        | some srcBound =>
            rw [hSrcR4] at hR4Imp hR4Src
            have hAdd : Nat.ble (s.regs.r4 + imm) (srcBound + imm) = true :=
              nat_ble_add_right_mono imm hR4Src
            exact nat_ble_trans (s.regs.r4 + imm) (srcBound + imm) dstBound hAdd hR4Imp

theorem impliesFallthroughBgeR4_preserves_holds
    (pol : SafetyPolicy) (aSrc aDst : PCAssertion) (s : MachineState) (bound nextPc : Nat)
    (hHolds : aSrc.holds pol s = true)
    (hBranchFalse : Nat.ble bound s.regs.r4 = false)
    (hImp : impliesFallthroughBgeR4 aSrc bound aDst = true) :
    aDst.holds pol { s with pc := nextPc } = true := by
  unfold PCAssertion.holds at hHolds ⊢
  unfold impliesFallthroughBgeR4 at hImp
  rcases Bool.and_eq_true_iff.mp hHolds with ⟨hBasesSrc, _⟩
  rcases Bool.and_eq_true_iff.mp hImp with ⟨hBasesImp, hR4Imp⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, ?_⟩
  · cases hDstAbi : aDst.abiAndBasesIntact
    · rfl
    · rw [hDstAbi] at hBasesImp
      change aSrc.abiAndBasesIntact = true at hBasesImp
      rw [hBasesImp] at hBasesSrc
      exact hBasesSrc
  · cases hDstR4 : aDst.maxR4 with
    | none => rfl
    | some dstBound =>
        rw [hDstR4] at hR4Imp
        have hSucc : Nat.ble (s.regs.r4 + 1) bound = true :=
          nat_ble_succ_of_ble_false bound s.regs.r4 hBranchFalse
        exact nat_ble_trans (s.regs.r4 + 1) bound (dstBound + 1) hSucc hR4Imp

/-- Single-step safety theorem (`pcc_state_inv_implies_safe_step`):
    Whenever `checkAllInstrVCs prog pol cert 0 prog = true` and `PCCStateInv prog pol cert s = true`,
    `SafeStep prog pol s = true`. -/
theorem pcc_state_inv_implies_safe_step
    (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion) (s : MachineState)
    (hAll : checkAllInstrVCs prog pol cert 0 prog = true)
    (hInv : PCCStateInv prog pol cert s = true) :
    SafeStep prog pol s = true := by
  unfold PCCStateInv at hInv
  unfold SafeStep
  cases hHalted : s.halted
  · rw [hHalted] at hInv
    change (natBlt s.pc prog.length && (lookupAssertion cert s.pc).holds pol s) = true at hInv
    rcases Bool.and_eq_true_iff.mp hInv with ⟨hPcBlt, hHolds⟩
    rcases fetchInstr_some_of_blt prog s.pc hPcBlt with ⟨instr, hFetch⟩
    have hVC := checkAllInstrVCs_at_pc prog pol cert s.pc instr hAll hFetch
    rw [hFetch]
    cases instr with
    | movi dst imm =>
        cases dst <;> try exact Bool.noConfusion hVC
        · exact (Bool.and_eq_true_iff.mp hVC).1
        · exact (Bool.and_eq_true_iff.mp hVC).1
    | addi dst src imm =>
        cases dst <;> try exact Bool.noConfusion hVC
        cases src <;> try exact Bool.noConfusion hVC
        exact (Bool.and_eq_true_iff.mp hVC).1
    | load dst base off =>
        cases dst <;> try exact Bool.noConfusion hVC
        cases base <;> try exact Bool.noConfusion hVC
        · -- load .r0 .r1 off
          unfold checkInstrVC at hVC
          rcases Bool.and_eq_true_iff.mp hVC with ⟨hLeft1, _⟩
          rcases Bool.and_eq_true_iff.mp hLeft1 with ⟨hLeft2, hNextBlt⟩
          rcases Bool.and_eq_true_iff.mp hLeft2 with ⟨hAbi, hOffBlt⟩
          unfold PCAssertion.holds at hHolds
          rw [hAbi] at hHolds
          rcases Bool.and_eq_true_iff.mp hHolds with ⟨hBases, _⟩
          rcases Bool.and_eq_true_iff.mp hBases with ⟨hB1, _⟩
          rcases Bool.and_eq_true_iff.mp hB1 with ⟨hB2, _⟩
          rcases Bool.and_eq_true_iff.mp hB2 with ⟨hR1Beq, _⟩
          have hR1Eq : s.regs.r1 = pol.pktBase := nat_beq_eq hR1Beq
          change (pol.validRead (s.regs.r1 + off) && natBlt (s.pc + 1) prog.length) = true
          unfold SafetyPolicy.validRead
          rw [hR1Eq]
          have hBle : Nat.ble pol.pktBase (pol.pktBase + off) = true :=
            nat_ble_add_right pol.pktBase off
          have hBlt : natBlt (pol.pktBase + off) (pol.pktBase + pol.pktLen) = true :=
            natBlt_add_left pol.pktBase off pol.pktLen hOffBlt
          rw [hBle, hBlt, Bool.and_self, Bool.true_or, hNextBlt]
          rfl
        · -- load .r0 .r3 off
          unfold checkInstrVC at hVC
          rcases Bool.and_eq_true_iff.mp hVC with ⟨hLeft1, _⟩
          rcases Bool.and_eq_true_iff.mp hLeft1 with ⟨hLeft2, hNextBlt⟩
          rcases Bool.and_eq_true_iff.mp hLeft2 with ⟨hAbi, hOffBlt⟩
          unfold PCAssertion.holds at hHolds
          rw [hAbi] at hHolds
          rcases Bool.and_eq_true_iff.mp hHolds with ⟨hBases, _⟩
          rcases Bool.and_eq_true_iff.mp hBases with ⟨hB1, _⟩
          rcases Bool.and_eq_true_iff.mp hB1 with ⟨hB2, _⟩
          rcases Bool.and_eq_true_iff.mp hB2 with ⟨_, hR3Beq⟩
          have hR3Eq : s.regs.r3 = pol.scratchBase := nat_beq_eq hR3Beq
          change (pol.validRead (s.regs.r3 + off) && natBlt (s.pc + 1) prog.length) = true
          unfold SafetyPolicy.validRead
          rw [hR3Eq]
          have hBle : Nat.ble pol.scratchBase (pol.scratchBase + off) = true :=
            nat_ble_add_right pol.scratchBase off
          have hBlt : natBlt (pol.scratchBase + off) (pol.scratchBase + pol.scratchLen) = true :=
            natBlt_add_left pol.scratchBase off pol.scratchLen hOffBlt
          rw [hBle, hBlt, Bool.and_self, Bool.or_true, hNextBlt]
          rfl
    | store base off src =>
        cases base <;> try exact Bool.noConfusion hVC
        unfold checkInstrVC at hVC
        rcases Bool.and_eq_true_iff.mp hVC with ⟨hLeft1, _⟩
        rcases Bool.and_eq_true_iff.mp hLeft1 with ⟨hLeft2, hNextBlt⟩
        rcases Bool.and_eq_true_iff.mp hLeft2 with ⟨hAbi, hOffBlt⟩
        unfold PCAssertion.holds at hHolds
        rw [hAbi] at hHolds
        rcases Bool.and_eq_true_iff.mp hHolds with ⟨hBases, _⟩
        rcases Bool.and_eq_true_iff.mp hBases with ⟨hB1, _⟩
        rcases Bool.and_eq_true_iff.mp hB1 with ⟨hB2, _⟩
        rcases Bool.and_eq_true_iff.mp hB2 with ⟨_, hR3Beq⟩
        have hR3Eq : s.regs.r3 = pol.scratchBase := nat_beq_eq hR3Beq
        change (pol.validWrite (s.regs.r3 + off) && natBlt (s.pc + 1) prog.length) = true
        unfold SafetyPolicy.validWrite
        rw [hR3Eq]
        have hBle : Nat.ble pol.scratchBase (pol.scratchBase + off) = true :=
          nat_ble_add_right pol.scratchBase off
        have hBlt : natBlt (pol.scratchBase + off) (pol.scratchBase + pol.scratchLen) = true :=
          natBlt_add_left pol.scratchBase off pol.scratchLen hOffBlt
        rw [hBle, hBlt, hNextBlt]
        rfl
    | bge reg bound target =>
        cases reg <;> try exact Bool.noConfusion hVC
        unfold checkInstrVC at hVC
        rcases Bool.and_eq_true_iff.mp hVC with ⟨hLeft1, _⟩
        rcases Bool.and_eq_true_iff.mp hLeft1 with ⟨hLeft2, _⟩
        exact hLeft2
    | jmp target =>
        unfold checkInstrVC at hVC
        exact (Bool.and_eq_true_iff.mp hVC).1
    | inv _ =>
        unfold checkInstrVC at hVC
        exact (Bool.and_eq_true_iff.mp hVC).1
    | ret =>
        change (lookupAssertion cert s.pc).abiAndBasesIntact = true at hVC
        unfold PCAssertion.holds at hHolds
        rw [hVC] at hHolds
        rcases Bool.and_eq_true_iff.mp hHolds with ⟨hBases, _⟩
        rcases Bool.and_eq_true_iff.mp hBases with ⟨hB1, hIplBeq⟩
        rcases Bool.and_eq_true_iff.mp hB1 with ⟨_, hFpBeq⟩
        change (Nat.beq s.regs.rFp pol.initFp && Nat.beq s.regs.rIpl pol.initIpl) = true
        rw [hFpBeq, hIplBeq]
        rfl
  · rfl

/-- Inductive step preservation theorem (`pcc_step_preserves_state_inv`):
    Whenever `checkAllInstrVCs prog pol cert 0 prog = true` and `PCCStateInv prog pol cert s = true`,
    stepping the machine preserves `PCCStateInv prog pol cert (stepInstr prog s) = true`. -/
theorem pcc_step_preserves_state_inv
    (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion) (s : MachineState)
    (hAll : checkAllInstrVCs prog pol cert 0 prog = true)
    (hInv : PCCStateInv prog pol cert s = true) :
    PCCStateInv prog pol cert (stepInstr prog s) = true := by
  unfold PCCStateInv at hInv ⊢
  unfold stepInstr
  cases hHalted : s.halted
  · rw [hHalted] at hInv
    change (natBlt s.pc prog.length && (lookupAssertion cert s.pc).holds pol s) = true at hInv
    rcases Bool.and_eq_true_iff.mp hInv with ⟨hPcBlt, hHolds⟩
    rcases fetchInstr_some_of_blt prog s.pc hPcBlt with ⟨instr, hFetch⟩
    have hVC := checkAllInstrVCs_at_pc prog pol cert s.pc instr hAll hFetch
    rw [hFetch]
    cases instr with
    | movi dst imm =>
        cases dst <;> try exact Bool.noConfusion hVC
        · -- movi .r0 imm
          unfold checkInstrVC at hVC
          rcases Bool.and_eq_true_iff.mp hVC with ⟨hNextBlt, hImp⟩
          change (natBlt (s.pc + 1) prog.length &&
            (lookupAssertion cert (s.pc + 1)).holds pol
              { s with pc := s.pc + 1, regs := s.regs.set .r0 imm, halted := false }) = true
          apply Bool.and_eq_true_iff.mpr
          refine ⟨hNextBlt, ?_⟩
          exact impliesAssertion_preserves_holds pol
            (lookupAssertion cert s.pc) (lookupAssertion cert (s.pc + 1))
            s { s with pc := s.pc + 1, regs := s.regs.set .r0 imm, halted := false }
            hHolds hImp rfl rfl rfl rfl rfl
        · -- movi .r4 imm
          unfold checkInstrVC at hVC
          rcases Bool.and_eq_true_iff.mp hVC with ⟨hNextBlt, hImp⟩
          change (natBlt (s.pc + 1) prog.length &&
            (lookupAssertion cert (s.pc + 1)).holds pol
              { s with pc := s.pc + 1, regs := s.regs.set .r4 imm, halted := false }) = true
          apply Bool.and_eq_true_iff.mpr
          have hHoldNext := impliesAfterMovR4_preserves_holds pol _ _ s imm (s.pc + 1) hHolds hImp
          exact ⟨hNextBlt, hHoldNext⟩
    | addi dst src imm =>
        cases dst <;> try exact Bool.noConfusion hVC
        cases src <;> try exact Bool.noConfusion hVC
        unfold checkInstrVC at hVC
        rcases Bool.and_eq_true_iff.mp hVC with ⟨hNextBlt, hImp⟩
        change (natBlt (s.pc + 1) prog.length &&
          (lookupAssertion cert (s.pc + 1)).holds pol
            { s with pc := s.pc + 1, regs := s.regs.set .r4 (s.regs.r4 + imm), halted := false }) = true
        apply Bool.and_eq_true_iff.mpr
        have hHoldNext := impliesAfterAddR4_preserves_holds pol _ _ s imm (s.pc + 1) hHolds hImp
        exact ⟨hNextBlt, hHoldNext⟩
    | load dst base off =>
        cases dst <;> try exact Bool.noConfusion hVC
        cases base <;> try exact Bool.noConfusion hVC
        · -- load .r0 .r1 off
          unfold checkInstrVC at hVC
          rcases Bool.and_eq_true_iff.mp hVC with ⟨hLeft1, hImp⟩
          rcases Bool.and_eq_true_iff.mp hLeft1 with ⟨_, hNextBlt⟩
          change (natBlt (s.pc + 1) prog.length &&
            (lookupAssertion cert (s.pc + 1)).holds pol
              { s with pc := s.pc + 1, regs := s.regs.set .r0 (s.mem (s.regs.get .r1 + off)), halted := false }) = true
          apply Bool.and_eq_true_iff.mpr
          refine ⟨hNextBlt, ?_⟩
          exact impliesAssertion_preserves_holds pol
            (lookupAssertion cert s.pc) (lookupAssertion cert (s.pc + 1))
            s { s with pc := s.pc + 1, regs := s.regs.set .r0 (s.mem (s.regs.get .r1 + off)), halted := false }
            hHolds hImp rfl rfl rfl rfl rfl
        · -- load .r0 .r3 off
          unfold checkInstrVC at hVC
          rcases Bool.and_eq_true_iff.mp hVC with ⟨hLeft1, hImp⟩
          rcases Bool.and_eq_true_iff.mp hLeft1 with ⟨_, hNextBlt⟩
          change (natBlt (s.pc + 1) prog.length &&
            (lookupAssertion cert (s.pc + 1)).holds pol
              { s with pc := s.pc + 1, regs := s.regs.set .r0 (s.mem (s.regs.get .r3 + off)), halted := false }) = true
          apply Bool.and_eq_true_iff.mpr
          refine ⟨hNextBlt, ?_⟩
          exact impliesAssertion_preserves_holds pol
            (lookupAssertion cert s.pc) (lookupAssertion cert (s.pc + 1))
            s { s with pc := s.pc + 1, regs := s.regs.set .r0 (s.mem (s.regs.get .r3 + off)), halted := false }
            hHolds hImp rfl rfl rfl rfl rfl
    | store base off src =>
        cases base <;> try exact Bool.noConfusion hVC
        unfold checkInstrVC at hVC
        rcases Bool.and_eq_true_iff.mp hVC with ⟨hLeft1, hImp⟩
        rcases Bool.and_eq_true_iff.mp hLeft1 with ⟨_, hNextBlt⟩
        change (natBlt (s.pc + 1) prog.length &&
          (lookupAssertion cert (s.pc + 1)).holds pol
            { s with pc := s.pc + 1, mem := updateMem s.mem (s.regs.get .r3 + off) (s.regs.get src), halted := false }) = true
        apply Bool.and_eq_true_iff.mpr
        refine ⟨hNextBlt, ?_⟩
        exact impliesAssertion_preserves_holds pol
          (lookupAssertion cert s.pc) (lookupAssertion cert (s.pc + 1))
          s { s with pc := s.pc + 1, mem := updateMem s.mem (s.regs.get .r3 + off) (s.regs.get src), halted := false }
          hHolds hImp rfl rfl rfl rfl rfl
    | bge reg bound target =>
        cases reg <;> try exact Bool.noConfusion hVC
        unfold checkInstrVC at hVC
        rcases Bool.and_eq_true_iff.mp hVC with ⟨hLeft1, hFallImp⟩
        rcases Bool.and_eq_true_iff.mp hLeft1 with ⟨hLeft2, hTgtImp⟩
        rcases Bool.and_eq_true_iff.mp hLeft2 with ⟨hTgtBlt, hNextBlt⟩
        change (if (if Nat.ble bound s.regs.r4 = true then { s with pc := target, halted := false }
                    else { s with pc := s.pc + 1, halted := false }).halted = true then true
                else
                  natBlt (if Nat.ble bound s.regs.r4 = true then { s with pc := target, halted := false }
                          else { s with pc := s.pc + 1, halted := false }).pc prog.length &&
                  (lookupAssertion cert
                    (if Nat.ble bound s.regs.r4 = true then { s with pc := target, halted := false }
                     else { s with pc := s.pc + 1, halted := false }).pc).holds pol
                    (if Nat.ble bound s.regs.r4 = true then { s with pc := target, halted := false }
                     else { s with pc := s.pc + 1, halted := false })) = true
        cases hCond : Nat.ble bound s.regs.r4
        · -- fall-through branch: `Nat.ble bound s.regs.r4 = false`
          change (natBlt (s.pc + 1) prog.length &&
            (lookupAssertion cert (s.pc + 1)).holds pol { s with pc := s.pc + 1, halted := false }) = true
          apply Bool.and_eq_true_iff.mpr
          have hHoldFall := impliesFallthroughBgeR4_preserves_holds pol _ _ s bound (s.pc + 1) hHolds hCond hFallImp
          exact ⟨hNextBlt, hHoldFall⟩
        · -- taken branch: `Nat.ble bound s.regs.r4 = true`
          change (natBlt target prog.length &&
            (lookupAssertion cert target).holds pol { s with pc := target, halted := false }) = true
          apply Bool.and_eq_true_iff.mpr
          refine ⟨hTgtBlt, ?_⟩
          exact impliesAssertion_preserves_holds pol
            (lookupAssertion cert s.pc) (lookupAssertion cert target)
            s { s with pc := target, halted := false }
            hHolds hTgtImp rfl rfl rfl rfl rfl
    | jmp target =>
        unfold checkInstrVC at hVC
        rcases Bool.and_eq_true_iff.mp hVC with ⟨hTgtBlt, hTgtImp⟩
        change (natBlt target prog.length &&
          (lookupAssertion cert target).holds pol { s with pc := target, halted := false }) = true
        apply Bool.and_eq_true_iff.mpr
        refine ⟨hTgtBlt, ?_⟩
        exact impliesAssertion_preserves_holds pol
          (lookupAssertion cert s.pc) (lookupAssertion cert target)
          s { s with pc := target, halted := false }
          hHolds hTgtImp rfl rfl rfl rfl rfl
    | inv _ =>
        unfold checkInstrVC at hVC
        rcases Bool.and_eq_true_iff.mp hVC with ⟨hNextBlt, hNextImp⟩
        change (natBlt (s.pc + 1) prog.length &&
          (lookupAssertion cert (s.pc + 1)).holds pol { s with pc := s.pc + 1, halted := false }) = true
        apply Bool.and_eq_true_iff.mpr
        refine ⟨hNextBlt, ?_⟩
        exact impliesAssertion_preserves_holds pol
          (lookupAssertion cert s.pc) (lookupAssertion cert (s.pc + 1))
          s { s with pc := s.pc + 1, halted := false }
          hHolds hNextImp rfl rfl rfl rfl rfl
    | ret =>
        rfl
  · change (if s.halted = true then true else _) = true
    rw [hHalted]
    rfl

/-- Multi-step safety from `PCCStateInv`. -/
theorem pcc_runSafeFor_of_state_inv
    (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion)
    (hAll : checkAllInstrVCs prog pol cert 0 prog = true)
    (fuel : Nat) (s : MachineState)
    (hInv : PCCStateInv prog pol cert s = true) :
    runSafeFor prog pol fuel s = true := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
      unfold runSafeFor
      have hSafe := pcc_state_inv_implies_safe_step prog pol cert s hAll hInv
      have hNext := pcc_step_preserves_state_inv prog pol cert s hAll hInv
      rw [hSafe, Bool.true_and]
      exact ih (stepInstr prog s) hNext

/-- **Theorem 1 (`pcc_kernel_extension_soundness`)**:
    End-to-end soundness of Necula & Lee's cutpoint-based PCC kernel extension loader:
    If `checkCert prog pol cert = true`, then:
    1. Every backward branch in `prog` is dominated by an `inv` cutpoint (`dominatesAllBackEdges prog = true`), and
    2. Starting from any valid kernel entry state `s₀` (`InitKernelState pol s₀ = true`),
       every reachable state across any `fuel : Nat` execution steps satisfies `SafeStep`
       (`runSafeFor prog pol fuel s₀ = true`) with zero runtime bounds checks! -/
theorem pcc_kernel_extension_soundness
    (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion)
    (hCert : checkCert prog pol cert = true)
    (fuel : Nat) (s₀ : MachineState)
    (hInit : InitKernelState pol s₀ = true) :
    dominatesAllBackEdges prog = true ∧
    runSafeFor prog pol fuel s₀ = true := by
  unfold checkCert at hCert
  rcases Bool.and_eq_true_iff.mp hCert with ⟨hLeft1, hAll⟩
  rcases Bool.and_eq_true_iff.mp hLeft1 with ⟨hLeft2, hEntryNone⟩
  rcases Bool.and_eq_true_iff.mp hLeft2 with ⟨hDom, hLen0⟩
  refine ⟨hDom, ?_⟩
  apply pcc_runSafeFor_of_state_inv prog pol cert hAll fuel s₀
  unfold InitKernelState at hInit
  rcases Bool.and_eq_true_iff.mp hInit with ⟨hI1, hIpl⟩
  rcases Bool.and_eq_true_iff.mp hI1 with ⟨hI2, hFp⟩
  rcases Bool.and_eq_true_iff.mp hI2 with ⟨hI3, hR3⟩
  rcases Bool.and_eq_true_iff.mp hI3 with ⟨hI4, hR1⟩
  rcases Bool.and_eq_true_iff.mp hI4 with ⟨hPc0, hNotHalted⟩
  have hPcEq : s₀.pc = 0 := nat_beq_eq hPc0
  have hHaltedFalse : s₀.halted = false := by
    cases h : s₀.halted
    · rfl
    · rw [h] at hNotHalted
      exact Bool.noConfusion hNotHalted
  unfold PCCStateInv
  rw [hHaltedFalse, hPcEq]
  change (natBlt 0 prog.length && (lookupAssertion cert 0).holds pol s₀) = true
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hLen0, ?_⟩
  unfold PCAssertion.holds
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, ?_⟩
  · cases (lookupAssertion cert 0).abiAndBasesIntact
    · rfl
    · rw [hR1, hR3, hFp, hIpl]
      rfl
  · cases hMax0 : (lookupAssertion cert 0).maxR4 with
    | none => rfl
    | some _ =>
        rw [hMax0] at hEntryNone
        exact Bool.noConfusion hEntryNone

/-!
## Part 2: The Three Classic `VCGen` TCB Soundness Failure Modes

We formalize and prove all three classic `VCGen` TCB soundness bugs that motivated
Foundational PCC (Appel LICS 2001 `appel01_fpcc.pdf`; Hamid et al. LICS 2002 `hamid02_safpcc.pdf`;
Colby, Lee, Necula et al. PLDI 2000 `colby00_pldi_java.txt:884-901`; Necula CMU-CS-98-154).
-/

/-! ### Failure Mode 1: Missing Back-Edge Cutpoint Dominance (`vcgen_missing_cutpoint_dominance_unsound`) -/

inductive ExploitInstr1 where
  | moviR4 (imm : Nat)
  | addiR4 (imm : Nat)
  | storeScratchR4 (val : Nat)  -- stores `val` at `scratchBase + r4`
  | jmp (target : Nat)
  | inv (maxR4Bound : Nat)
  | ret
  deriving DecidableEq, Repr

def fetchExploit1 : List ExploitInstr1 → Nat → Option ExploitInstr1
  | [], _ => none
  | i :: _, 0 => some i
  | _ :: rest, n + 1 => fetchExploit1 rest n

def stepExploit1 (prog : List ExploitInstr1) (s : MachineState) : MachineState :=
  if s.halted then s
  else
    match fetchExploit1 prog s.pc with
    | none => { s with halted := true }
    | some (.moviR4 imm) => { s with pc := s.pc + 1, regs := s.regs.set .r4 imm }
    | some (.addiR4 imm) => { s with pc := s.pc + 1, regs := s.regs.set .r4 (s.regs.r4 + imm) }
    | some (.storeScratchR4 v) =>
        let addr := s.regs.r3 + s.regs.r4
        { s with pc := s.pc + 1, mem := updateMem s.mem addr v }
    | some (.jmp target) => { s with pc := target }
    | some (.inv _) => { s with pc := s.pc + 1 }
    | some .ret => { s with halted := true }

def safeStepExploit1 (prog : List ExploitInstr1) (pol : SafetyPolicy) (s : MachineState) : Bool :=
  if s.halted then true
  else
    match fetchExploit1 prog s.pc with
    | none => false
    | some (.moviR4 _) => natBlt (s.pc + 1) prog.length
    | some (.addiR4 _) => natBlt (s.pc + 1) prog.length
    | some (.storeScratchR4 _) =>
        pol.validWrite (s.regs.r3 + s.regs.r4) && natBlt (s.pc + 1) prog.length
    | some (.jmp target) => natBlt target prog.length
    | some (.inv _) => natBlt (s.pc + 1) prog.length
    | some .ret => pol.preservesKernelABI s.regs

def runSafeExploit1 (prog : List ExploitInstr1) (pol : SafetyPolicy) : Nat → MachineState → Bool
  | 0, _ => true
  | fuel + 1, s =>
      safeStepExploit1 prog pol s && runSafeExploit1 prog pol fuel (stepExploit1 prog s)

/-- Buggy `vcgenNoBackedgeCheck`: symbolic execution that terminates at backward jumps
    (`target ≤ pc`) without checking that `prog[target]` is an `inv` cutpoint whose invariant
    is implied by `r4Max`! -/
def vcgenNoBackedgeCheck (prog : List ExploitInstr1) (pol : SafetyPolicy) :
    Nat → Nat → List ExploitInstr1 → Bool
  | _, _, [] => true
  | pc, r4Max, instr :: rest =>
      match instr with
      | .moviR4 imm =>
          natBlt (pc + 1) prog.length && vcgenNoBackedgeCheck prog pol (pc + 1) imm rest
      | .addiR4 imm =>
          natBlt (pc + 1) prog.length && vcgenNoBackedgeCheck prog pol (pc + 1) (r4Max + imm) rest
      | .storeScratchR4 _ =>
          natBlt r4Max pol.scratchLen && natBlt (pc + 1) prog.length &&
          vcgenNoBackedgeCheck prog pol (pc + 1) r4Max rest
      | .jmp target =>
          -- BUG: Terminates backward path at `target ≤ pc` without checking that
          -- `fetchExploit1 prog target` is an `.inv bound` with `r4Max ≤ bound`!
          natBlt target prog.length
      | .inv bound =>
          Nat.ble r4Max bound && natBlt (pc + 1) prog.length &&
          vcgenNoBackedgeCheck prog pol (pc + 1) bound rest
      | .ret => true

/-- Sound `vcgenWithBackedgeDominance`: requires every backward jump `target ≤ pc` to
    land on `.inv bound` and proves `Nat.ble r4Max bound`. -/
def vcgenWithBackedgeDominance (prog : List ExploitInstr1) (pol : SafetyPolicy) :
    Nat → Nat → List ExploitInstr1 → Bool
  | _, _, [] => true
  | pc, r4Max, instr :: rest =>
      match instr with
      | .moviR4 imm =>
          natBlt (pc + 1) prog.length && vcgenWithBackedgeDominance prog pol (pc + 1) imm rest
      | .addiR4 imm =>
          natBlt (pc + 1) prog.length && vcgenWithBackedgeDominance prog pol (pc + 1) (r4Max + imm) rest
      | .storeScratchR4 _ =>
          natBlt r4Max pol.scratchLen && natBlt (pc + 1) prog.length &&
          vcgenWithBackedgeDominance prog pol (pc + 1) r4Max rest
      | .jmp target =>
          natBlt target prog.length &&
          if Nat.ble target pc then
            match fetchExploit1 prog target with
            | some (.inv bound) => Nat.ble r4Max bound
            | _ => false
          else false
      | .inv bound =>
          Nat.ble r4Max bound && natBlt (pc + 1) prog.length &&
          vcgenWithBackedgeDominance prog pol (pc + 1) bound rest
      | .ret => true

def attackBackEdgeProg : List ExploitInstr1 :=
  [ .moviR4 0
  , .addiR4 10
  , .storeScratchR4 0xDEAD
  , .jmp 1 ]

/-- **Theorem (`vcgen_missing_cutpoint_dominance_unsound`)**:
    1. Buggy `vcgenNoBackedgeCheck` ACCEPTS `attackBackEdgeProg` (`= true`).
    2. Iteration 1 (first 4 steps) is safe (`runSafeExploit1 ... 4 = true`).
    3. On Iteration 2 (step 6, PC 2), `attackBackEdgeProg` writes to `2020 >= 2016`,
       violating `safeStepExploit1` (`runSafeExploit1 ... 6 = false`)!
    4. Sound `vcgenWithBackedgeDominance` REJECTS `attackBackEdgeProg` (`= false`). -/
theorem vcgen_missing_cutpoint_dominance_unsound :
    vcgenNoBackedgeCheck attackBackEdgeProg filter1Policy 0 0 attackBackEdgeProg = true ∧
    runSafeExploit1 attackBackEdgeProg filter1Policy 4 filter1InitState = true ∧
    runSafeExploit1 attackBackEdgeProg filter1Policy 6 filter1InitState = false ∧
    vcgenWithBackedgeDominance attackBackEdgeProg filter1Policy 0 0 attackBackEdgeProg = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Failure Mode 2: Memory Aliasing / Missing Separation Obligation (`vcgen_memory_aliasing_unsound`) -/

structure AliasMachineState where
  rSpill : Nat
  rScratch : Nat
  rOffset : Nat
  mem : Nat → Nat

inductive AliasInstr where
  | spillValidatedOffset (imm : Nat)      -- checks `imm < 16`, stores `Mem[rSpill] := imm`
  | writeScratch (val : Nat)              -- stores `Mem[rScratch] := val`
  | reloadSpilledOffset                   -- loads `rOffset := Mem[rSpill]`
  | storeAtOffset (val : Nat)             -- stores `Mem[scratchBase + rOffset] := val`
  deriving DecidableEq, Repr

def stepAliasInstr (s : AliasMachineState) : AliasInstr → AliasMachineState
  | .spillValidatedOffset imm =>
      { s with mem := updateMem s.mem s.rSpill imm }
  | .writeScratch val =>
      { s with mem := updateMem s.mem s.rScratch val }
  | .reloadSpilledOffset =>
      { s with rOffset := s.mem s.rSpill }
  | .storeAtOffset val =>
      { s with mem := updateMem s.mem (s.rScratch + s.rOffset) val }

def runAliasProg : List AliasInstr → AliasMachineState → AliasMachineState
  | [], s => s
  | i :: rest, s => runAliasProg rest (stepAliasInstr s i)

def safeAliasProg (pol : SafetyPolicy) : List AliasInstr → AliasMachineState → Bool
  | [], _ => true
  | i :: rest, s =>
      let okNow :=
        match i with
        | .spillValidatedOffset _ => pol.validWrite s.rSpill
        | .writeScratch _ => pol.validWrite s.rScratch
        | .reloadSpilledOffset => pol.validRead s.rSpill
        | .storeAtOffset _ => pol.validWrite (s.rScratch + s.rOffset)
      okNow && safeAliasProg pol rest (stepAliasInstr s i)

/-- Buggy `vcgenNaiveSubst`: tracks `spilledBound` as an unaliased variable across
    `writeScratch` without emitting `rSpill ≠ rScratch` (omitting McCarthy rule `mc1`'s
    inequality side condition `E1 != E3` in `necula98_thesis.txt:4249` / `colby00_pldi_java.txt:889`). -/
def vcgenNaiveSubst (pol : SafetyPolicy) : Option Nat → Option Nat → List AliasInstr → Bool
  | _, _, [] => true
  | _, regBound, (.spillValidatedOffset imm) :: rest =>
      natBlt imm pol.scratchLen && vcgenNaiveSubst pol (some imm) regBound rest
  | spillBound, regBound, (.writeScratch _) :: rest =>
      vcgenNaiveSubst pol spillBound regBound rest
  | spillBound, _, .reloadSpilledOffset :: rest =>
      vcgenNaiveSubst pol spillBound spillBound rest
  | spillBound, some rBound, (.storeAtOffset _) :: rest =>
      natBlt rBound pol.scratchLen && vcgenNaiveSubst pol spillBound (some rBound) rest
  | _, none, (.storeAtOffset _) :: _ => false

/-- Sound `vcgenAliasingGuarded`: emits explicit disjointness `!Nat.beq rSpill rScratch`
    whenever `writeScratch` executes while `spillBound` is live. -/
def vcgenAliasingGuarded (pol : SafetyPolicy) (rSpill rScratch : Nat) :
    Option Nat → Option Nat → List AliasInstr → Bool
  | _, _, [] => true
  | _, regBound, (.spillValidatedOffset imm) :: rest =>
      Nat.beq rSpill pol.scratchBase &&
      natBlt imm pol.scratchLen &&
      vcgenAliasingGuarded pol rSpill rScratch (some imm) regBound rest
  | spillBound, regBound, (.writeScratch _) :: rest =>
      pol.validWrite rScratch &&
      (if spillBound.isSome then !Nat.beq rSpill rScratch else true) &&
      vcgenAliasingGuarded pol rSpill rScratch spillBound regBound rest
  | spillBound, _, .reloadSpilledOffset :: rest =>
      pol.validRead rSpill &&
      vcgenAliasingGuarded pol rSpill rScratch spillBound spillBound rest
  | spillBound, some rBound, (.storeAtOffset _) :: rest =>
      Nat.beq rScratch pol.scratchBase &&
      natBlt rBound pol.scratchLen &&
      vcgenAliasingGuarded pol rSpill rScratch spillBound (some rBound) rest
  | _, none, (.storeAtOffset _) :: _ => false

def attackAliasProg : List AliasInstr :=
  [ .spillValidatedOffset 4
  , .writeScratch 500
  , .reloadSpilledOffset
  , .storeAtOffset 0xBAD ]

def aliasedInitState : AliasMachineState :=
  { rSpill := 2000, rScratch := 2000, rOffset := 0, mem := fun _ => 0 }

def unaliasedInitState : AliasMachineState :=
  { rSpill := 2004, rScratch := 2000, rOffset := 0, mem := fun _ => 0 }

/-- **Theorem (`vcgen_memory_aliasing_unsound`)**:
    1. `vcgenNaiveSubst` ACCEPTS `attackAliasProg` (`= true`).
    2. Executing `attackAliasProg` on `aliasedInitState` violates memory safety
       (`safeAliasProg = false`) and writes `0xBAD` to out-of-bounds address `2500`!
    3. `vcgenAliasingGuarded` REJECTS `attackAliasProg` on `aliasedInitState` (`= false`). -/
theorem vcgen_memory_aliasing_unsound :
    vcgenNaiveSubst filter1Policy none none attackAliasProg = true ∧
    safeAliasProg filter1Policy attackAliasProg aliasedInitState = false ∧
    (runAliasProg attackAliasProg aliasedInitState).mem 2500 = 0xBAD ∧
    vcgenAliasingGuarded filter1Policy aliasedInitState.rSpill aliasedInitState.rScratch
      none none attackAliasProg = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Theorem (`vcgen_aliasing_guarded_sound`)**:
    When `rSpill` and `rScratch` are disjoint (`2004 ≠ 2000`), `safeAliasProg = true`
    and `rOffset` retains its validated bound `4`. -/
theorem vcgen_aliasing_guarded_sound :
    (!Nat.beq unaliasedInitState.rSpill unaliasedInitState.rScratch) = true ∧
    safeAliasProg filter1Policy attackAliasProg unaliasedInitState = true ∧
    (runAliasProg attackAliasProg unaliasedInitState).rOffset = 4 :=
  ⟨rfl, rfl, rfl⟩

/-! ### Failure Mode 3: Callee-Save / Kernel ABI Omission on `ret` (`vcgen_callee_save_omission_unsound`) -/

def InExtensionMemSafeOnly (prog : List Instr) (pol : SafetyPolicy) (s : MachineState) : Bool :=
  if s.halted then true
  else
    match fetchInstr prog s.pc with
    | none => false
    | some (.load _ base off) =>
        pol.validRead (s.regs.get base + off) && natBlt (s.pc + 1) prog.length
    | some (.store base off _) =>
        pol.validWrite (s.regs.get base + off) && natBlt (s.pc + 1) prog.length
    | some .ret =>
        -- BUG: Omits `pol.preservesKernelABI s.regs` (`SafeRET_F` in CMU-CS-98-154 p. 49)!
        true
    | some _ => natBlt (s.pc + 1) prog.length

def attackCalleeSaveProg : List Instr :=
  [ .load .r0 .r1 0         -- PC 0: valid packet read at pktBase + 0
  , .store .r3 0 .r0        -- PC 1: valid scratch write at scratchBase + 0
  , .movi .rFp 0xDEADBEEF   -- PC 2: clobber kernel callee-saved frame pointer!
  , .movi .rIpl 0           -- PC 3: clobber kernel interrupt priority mask!
  , .ret                    -- PC 4: return to kernel with corrupted ABI state
  ]

def attackCalleeSaveCert : List PCAssertion :=
  [ { maxR4 := none, abiAndBasesIntact := true }
  , { maxR4 := none, abiAndBasesIntact := true }
  , { maxR4 := none, abiAndBasesIntact := true }
  , { maxR4 := none, abiAndBasesIntact := true }
  , { maxR4 := none, abiAndBasesIntact := true } ]

/-- **Theorem (`vcgen_callee_save_omission_unsound`)**:
    1. Every step of `attackCalleeSaveProg` satisfies `InExtensionMemSafeOnly` (all in-extension
       loads/stores are within bounds).
    2. At `ret` (step 4), `SafeStep` fails (`= false`) because `rFp = 0xDEADBEEF ≠ 9000`
       and `rIpl = 0 ≠ 7`.
    3. The sound `checkCert` REJECTS `attackCalleeSaveProg` (`= false`). -/
theorem vcgen_callee_save_omission_unsound :
    InExtensionMemSafeOnly attackCalleeSaveProg filter1Policy filter1InitState = true ∧
    InExtensionMemSafeOnly attackCalleeSaveProg filter1Policy
      (stepN attackCalleeSaveProg 1 filter1InitState) = true ∧
    InExtensionMemSafeOnly attackCalleeSaveProg filter1Policy
      (stepN attackCalleeSaveProg 2 filter1InitState) = true ∧
    SafeStep attackCalleeSaveProg filter1Policy
      (stepN attackCalleeSaveProg 4 filter1InitState) = false ∧
    checkCert attackCalleeSaveProg filter1Policy attackCalleeSaveCert = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-!
## Part 3: Foundational Proof-Carrying Code (`fpcc_semantic_certificate_soundness`)

Formalizes Andrew W. Appel, *Foundational Proof-Carrying Code*, LICS 2001
(DOI `10.1109/LICS.2001.932501`, `appel01_fpcc.pdf`) and Hamid, Shao, Trifonov,
Monnier, Ni, *A Syntactic Approach to Foundational Proof-Carrying Code*, LICS 2002
(`safpcc_coq8/translate_ftal.v:5156-5325`).
-/

structure FPCCCertificate (State : Type) (Init : State → Bool)
    (Step : State → State) (SafeState : State → Bool) where
  Inv : State → Bool
  init_inv : ∀ s, Init s = true → Inv s = true
  inv_safe : ∀ s, Inv s = true → SafeState s = true
  inv_pres : ∀ s, Inv s = true → Inv (Step s) = true

def fpccMultiStep (Step : State → State) : Nat → State → State
  | 0, s => s
  | n + 1, s => fpccMultiStep Step n (Step s)

def fpccSafeRun (Step : State → State) (SafeState : State → Bool) : Nat → State → Bool
  | 0, _ => true
  | fuel + 1, s => SafeState s && fpccSafeRun Step SafeState fuel (Step s)

theorem fpcc_inv_preserved_at_any_step
    {State : Type} {Init : State → Bool} {Step : State → State} {SafeState : State → Bool}
    (cert : FPCCCertificate State Init Step SafeState)
    (n : Nat) (s : State) (hInv : cert.Inv s = true) :
    cert.Inv (fpccMultiStep Step n s) = true := by
  induction n generalizing s with
  | zero => exact hInv
  | succ m ih =>
      unfold fpccMultiStep
      exact ih (Step s) (cert.inv_pres s hInv)

theorem fpcc_semantic_certificate_soundness
    {State : Type} {Init : State → Bool} {Step : State → State} {SafeState : State → Bool}
    (cert : FPCCCertificate State Init Step SafeState)
    (s₀ : State) (hInit : Init s₀ = true) (n : Nat) :
    SafeState (fpccMultiStep Step n s₀) = true := by
  have hInv0 : cert.Inv s₀ = true := cert.init_inv s₀ hInit
  have hInvN : cert.Inv (fpccMultiStep Step n s₀) = true :=
    fpcc_inv_preserved_at_any_step cert n s₀ hInv0
  exact cert.inv_safe (fpccMultiStep Step n s₀) hInvN

theorem fpcc_prefix_run_soundness
    {State : Type} {Init : State → Bool} {Step : State → State} {SafeState : State → Bool}
    (cert : FPCCCertificate State Init Step SafeState)
    (fuel : Nat) (s : State) (hInv : cert.Inv s = true) :
    fpccSafeRun Step SafeState fuel s = true := by
  induction fuel generalizing s with
  | zero => rfl
  | succ m ih =>
      unfold fpccSafeRun
      rw [cert.inv_safe s hInv, Bool.true_and]
      exact ih (Step s) (cert.inv_pres s hInv)

theorem fpcc_syntactic_type_bridge_soundness
    {State AbsState : Type}
    (Step : State → State) (SafeState : State → Bool)
    (WF : AbsState → Bool) (Tr : AbsState → State → Bool)
    (hProgressSafe : ∀ a s, WF a = true → Tr a s = true → SafeState s = true)
    (hPreservation : ∀ a s, WF a = true → Tr a s = true →
      ∃ a', WF a' = true ∧ Tr a' (Step s) = true)
    (n : Nat) (a₀ : AbsState) (s₀ : State)
    (hWF₀ : WF a₀ = true) (hTr₀ : Tr a₀ s₀ = true) :
    SafeState (fpccMultiStep Step n s₀) = true := by
  induction n generalizing a₀ s₀ with
  | zero =>
      exact hProgressSafe a₀ s₀ hWF₀ hTr₀
  | succ m ih =>
      rcases hPreservation a₀ s₀ hWF₀ hTr₀ with ⟨a₁, hWF₁, hTr₁⟩
      exact ih a₁ (Step s₀) hWF₁ hTr₁

/-!
## Part 4: Verve Operating System Two-Regime Verification Seam (Yang & Hawblitzel PLDI 2010)

Models the Verve Nucleus (Boogie/Z3 Hoare logic) + Kernel/App (Bartok TALx86) boundary from:
- Jean Yang & Chris Hawblitzel, *Safe to the Last Instruction: Automated Verification of a
  Type-Safe Operating System*, PLDI 2010 (DOI `10.1145/1806596.1806610`).
- Microsoft Research `Ironclad` (`https://github.com/Microsoft/Ironclad`, commit
  `2fe4dcdc323b92e93f759cc3e373521366b7f691`), `SimpleGcMemory.ifc.beat`, `SimpleCommon.ifc.beat`,
  `SimpleCollector.ifc.beat`, `SimpleCollector.imp.beat`, `Stacks.ifc.beat`.
-/

inductive AbsVal where
  | prim (w : Nat)
  | absNode (id : Nat)
  deriving DecidableEq, Repr

inductive ConcreteWord where
  | raw (w : Nat)
  | heapPtr (addr : Nat)
  deriving DecidableEq, Repr

/-- Constructive association-list lookup using `Nat.beq` (avoids `LawfulBEq` / `Classical.choice`). -/
def lookupToAbs : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (k, v) :: rest, addr =>
      if Nat.beq addr k then some v else lookupToAbs rest addr

/-- Verve `Value(objLayouts, isPtr, $toAbs, val, abs)` predicate from
    `SimpleGcMemory.ifc.beat:71-83`. -/
def VerveValueMatch (isPtr : Bool) (toAbs : List (Nat × Nat))
    (val : ConcreteWord) (abs : AbsVal) : Bool :=
  if isPtr then
    match val, abs with
    | .heapPtr addr, .absNode id =>
        match lookupToAbs toAbs addr with
        | some mappedId => Nat.beq mappedId id
        | none => false
    | _, _ => false
  else
    match val, abs with
    | .raw w, .prim aw => Nat.beq w aw
    | _, _ => false

structure GCFrameDescriptor where
  slot0IsPtr : Bool
  slot1IsPtr : Bool
  isSafePoint : Bool
  deriving DecidableEq, Repr

inductive VerveStackState where
  | running
  | yielded
  | interrupted (pc : Nat)
  deriving DecidableEq, Repr

structure VerveSeamState where
  pc : Nat
  stackState : VerveStackState
  slot0 : ConcreteWord
  slot1 : ConcreteWord
  absSlot0 : AbsVal
  absSlot1 : AbsVal
  toAbs : List (Nat × Nat)
  fk : Nat
  ti : Nat
  nextAbsId : Nat
  deriving DecidableEq, Repr

def MutatorStackInv (s : VerveSeamState) (slot0HasPtr slot1HasPtr : Bool) : Bool :=
  VerveValueMatch slot0HasPtr s.toAbs s.slot0 s.absSlot0 &&
  VerveValueMatch slot1HasPtr s.toAbs s.slot1 s.absSlot1

def ScanStackInv (s : VerveSeamState) (desc : GCFrameDescriptor) : Bool :=
  desc.isSafePoint &&
  VerveValueMatch desc.slot0IsPtr s.toAbs s.slot0 s.absSlot0 &&
  VerveValueMatch desc.slot1IsPtr s.toAbs s.slot1 s.absSlot1

def gcForwardWord (isPtrAccordingToGCDesc : Bool) (oldToAbs : List (Nat × Nat))
    (ti : Nat) (w : ConcreteWord) : ConcreteWord × List (Nat × Nat) :=
  if isPtrAccordingToGCDesc then
    match w with
    | .heapPtr oldAddr =>
        match lookupToAbs oldToAbs oldAddr with
        | some absId =>
            let newAddr := ti + absId * 4
            (.heapPtr newAddr, (newAddr, absId) :: oldToAbs)
        | none =>
            (.raw 0xBADCAFE, oldToAbs)
    | .raw _ =>
        (.raw 0xBADCAFE, oldToAbs)
  else
    (w, oldToAbs)

def nucleusGarbageCollect (s : VerveSeamState) (desc : GCFrameDescriptor) : VerveSeamState :=
  let slot0' := (gcForwardWord desc.slot0IsPtr s.toAbs s.ti s.slot0).1
  let slot1' := (gcForwardWord desc.slot1IsPtr s.toAbs s.ti s.slot1).1
  let newToAbs :=
    (match desc.slot0IsPtr, s.slot0 with
     | true, .heapPtr old0 =>
         match lookupToAbs s.toAbs old0 with
         | some id0 => [(s.ti + id0 * 4, id0)]
         | none => []
     | _, _ => []) ++
    (match desc.slot1IsPtr, s.slot1 with
     | true, .heapPtr old1 =>
         match lookupToAbs s.toAbs old1 with
         | some id1 => [(s.ti + id1 * 4, id1)]
         | none => []
     | _, _ => [])
  { s with
    slot0 := slot0'
    slot1 := slot1'
    toAbs := newToAbs
    fk := s.ti + 64
    ti := s.fk }

def midAllocState : VerveSeamState :=
  { pc := 42
  , stackState := .interrupted 42
  , slot0 := .heapPtr 100
  , slot1 := .raw 77
  , absSlot0 := .absNode 1
  , absSlot1 := .prim 77
  , toAbs := [(100, 1)]
  , fk := 200
  , ti := 500
  , nextAbsId := 2 }

def midAllocInaccurateDesc : GCFrameDescriptor :=
  { slot0IsPtr := false, slot1IsPtr := false, isSafePoint := false }

def uninitSlotDesc : GCFrameDescriptor :=
  { slot0IsPtr := true, slot1IsPtr := true, isSafePoint := false }

/-- **Theorem (`verve_mid_allocation_interrupt_hazard`)**:
    Preempting a TAL mutator at an intermediate non-safe-point PC (`midAllocState`) and
    running `nucleusGarbageCollect` with an inaccurate descriptor leaves `slot0` dangling in
    reclaimed Fromspace (`100`), violating `MutatorStackInv`! -/
theorem verve_mid_allocation_interrupt_hazard :
    MutatorStackInv midAllocState true false = true ∧
    ScanStackInv midAllocState midAllocInaccurateDesc = false ∧
    MutatorStackInv (nucleusGarbageCollect midAllocState midAllocInaccurateDesc) true false = false :=
  ⟨rfl, rfl, rfl⟩

/-- **Theorem (`verve_uninitialized_pointer_slot_gc_hazard`)**:
    Preempting a TAL mutator before an allocated pointer is written into `slot1` (while
    the block-level descriptor `uninitSlotDesc` already marks `slot1IsPtr = true`) causes
    `nucleusGarbageCollect` to misinterpret `.raw 77` as a heap pointer and corrupt `slot1`! -/
theorem verve_uninitialized_pointer_slot_gc_hazard :
    VerveValueMatch true midAllocState.toAbs midAllocState.slot0 midAllocState.absSlot0 = true ∧
    (nucleusGarbageCollect midAllocState uninitSlotDesc).slot1 = .raw 0xBADCAFE :=
  ⟨rfl, rfl⟩

def nucleusAllocObject (s : VerveSeamState) : VerveSeamState :=
  let newAddr := s.fk
  let newAbs := s.nextAbsId
  { s with
    slot0 := .heapPtr newAddr
    absSlot0 := .absNode newAbs
    toAbs := (newAddr, newAbs) :: s.toAbs
    fk := s.fk + 16
    nextAbsId := s.nextAbsId + 1 }

def nucleusYield (s : VerveSeamState) : VerveSeamState :=
  { s with stackState := .yielded }

inductive VerveTransition where
  | talWritePrim1 (w : Nat)
  | callAllocObject
  | callYield
  | callGarbageCollect
  deriving DecidableEq, Repr

def stepVerveSeam (s : VerveSeamState) (desc : GCFrameDescriptor)
    (t : VerveTransition) : VerveSeamState × GCFrameDescriptor :=
  match t with
  | .talWritePrim1 w =>
      ( { s with slot1 := .raw w, absSlot1 := .prim w }
      , { desc with slot1IsPtr := false, isSafePoint := true } )
  | .callAllocObject =>
      ( nucleusAllocObject s
      , { desc with slot0IsPtr := true, isSafePoint := true } )
  | .callYield =>
      ( nucleusYield s, desc )
  | .callGarbageCollect =>
      ( nucleusGarbageCollect s desc, desc )

theorem verveValueMatch_prim_refl (toAbs : List (Nat × Nat)) (w : Nat) :
    VerveValueMatch false toAbs (.raw w) (.prim w) = true := by
  unfold VerveValueMatch
  exact nat_beq_refl w

theorem verveValueMatch_head_ptr (toAbs : List (Nat × Nat)) (addr id : Nat) :
    VerveValueMatch true ((addr, id) :: toAbs) (.heapPtr addr) (.absNode id) = true := by
  change (match if Nat.beq addr addr = true then some id else lookupToAbs toAbs addr with
          | some mappedId => Nat.beq mappedId id
          | none => false) = true
  rw [nat_beq_refl addr]
  exact nat_beq_refl id

theorem verve_alloc_preserves_scanStackInv
    (s : VerveSeamState) (desc : GCFrameDescriptor)
    (hScan : ScanStackInv s desc = true)
    (hSlot1Prim : desc.slot1IsPtr = false) :
    ScanStackInv (stepVerveSeam s desc .callAllocObject).1
      (stepVerveSeam s desc .callAllocObject).2 = true := by
  unfold ScanStackInv at hScan ⊢
  unfold stepVerveSeam nucleusAllocObject
  rw [hSlot1Prim] at hScan ⊢
  rcases Bool.and_eq_true_iff.mp hScan with ⟨_, hMatch1⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, ?_⟩
  · apply Bool.and_eq_true_iff.mpr
    exact ⟨rfl, verveValueMatch_head_ptr s.toAbs s.fk s.nextAbsId⟩
  · unfold VerveValueMatch at hMatch1 ⊢
    exact hMatch1

theorem verve_gc_preserves_scanStackInv
    (s : VerveSeamState) (desc : GCFrameDescriptor)
    (hScan : ScanStackInv s desc = true)
    (hSlot0Ptr : desc.slot0IsPtr = true)
    (hSlot1Prim : desc.slot1IsPtr = false) :
    ScanStackInv (nucleusGarbageCollect s desc) desc = true ∧
    MutatorStackInv (nucleusGarbageCollect s desc) true false = true := by
  unfold ScanStackInv at hScan
  rw [hSlot0Ptr, hSlot1Prim] at hScan
  rcases Bool.and_eq_true_iff.mp hScan with ⟨hLeft, hMatch1⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨hSafePt, hMatch0⟩
  unfold VerveValueMatch at hMatch0
  cases hS0 : s.slot0
  · rw [hS0] at hMatch0
    exact Bool.noConfusion hMatch0
  case heapPtr oldAddr =>
    rw [hS0] at hMatch0
    cases hA0 : s.absSlot0
    · rw [hA0] at hMatch0
      exact Bool.noConfusion hMatch0
    case absNode absId =>
      rw [hA0] at hMatch0
      change (match lookupToAbs s.toAbs oldAddr with
              | some mappedId => Nat.beq mappedId absId
              | none => false) = true at hMatch0
      cases hLook : lookupToAbs s.toAbs oldAddr
      · rw [hLook] at hMatch0
        exact Bool.noConfusion hMatch0
      case some mappedId =>
        rw [hLook] at hMatch0
        have hEqId : mappedId = absId := nat_beq_eq hMatch0
        subst hEqId
        have hMatch0After :
            VerveValueMatch true [(s.ti + mappedId * 4, mappedId)]
              (.heapPtr (s.ti + mappedId * 4)) (.absNode mappedId) = true :=
          verveValueMatch_head_ptr [] (s.ti + mappedId * 4) mappedId
        have hMatch1After :
            VerveValueMatch false [(s.ti + mappedId * 4, mappedId)]
              s.slot1 s.absSlot1 = true := by
          unfold VerveValueMatch at hMatch1 ⊢
          exact hMatch1
        have hGCState : nucleusGarbageCollect s desc =
            { s with
              slot0 := .heapPtr (s.ti + mappedId * 4)
              slot1 := s.slot1
              toAbs := [(s.ti + mappedId * 4, mappedId)]
              fk := s.ti + 64
              ti := s.fk } := by
          unfold nucleusGarbageCollect gcForwardWord
          rw [hSlot0Ptr, hSlot1Prim, hS0]
          change { s with
            slot0 := (match lookupToAbs s.toAbs oldAddr with
              | some absId => (ConcreteWord.heapPtr (s.ti + absId * 4), (s.ti + absId * 4, absId) :: s.toAbs)
              | none => (ConcreteWord.raw 0xBADCAFE, s.toAbs)).1
            slot1 := s.slot1
            toAbs := (match lookupToAbs s.toAbs oldAddr with
              | some id0 => [(s.ti + id0 * 4, id0)]
              | none => []) ++ []
            fk := s.ti + 64
            ti := s.fk } = _
          rw [hLook]
          rfl
        rw [hGCState]
        unfold ScanStackInv MutatorStackInv
        rw [hSlot0Ptr, hSlot1Prim, hSafePt, hA0]
        refine ⟨?_, ?_⟩
        · apply Bool.and_eq_true_iff.mpr
          refine ⟨?_, hMatch1After⟩
          apply Bool.and_eq_true_iff.mpr
          exact ⟨rfl, hMatch0After⟩
        · apply Bool.and_eq_true_iff.mpr
          exact ⟨hMatch0After, hMatch1After⟩

def runVerveTrace : List VerveTransition → VerveSeamState → GCFrameDescriptor →
    VerveSeamState × GCFrameDescriptor
  | [], s, d => (s, d)
  | t :: rest, s, d =>
      let next := stepVerveSeam s d t
      runVerveTrace rest next.1 next.2

/-- **Theorem (`verve_two_regime_seam_soundness`)**:
    When the TAL checker enforces GC safe-point descriptor accuracy (`ScanStackInv`) and the
    Nucleus satisfies its Hoare specification, arbitrary finite sequences of TAL instructions,
    `AllocObject`, `YieldTo`, and `GarbageCollect` preserve both `ScanStackInv` and `MutatorStackInv`! -/
theorem verve_two_regime_seam_soundness
    (trace : List VerveTransition) (s : VerveSeamState) (desc : GCFrameDescriptor)
    (hScan : ScanStackInv s desc = true)
    (hSlot0 : desc.slot0IsPtr = true)
    (hSlot1 : desc.slot1IsPtr = false) :
    ScanStackInv (runVerveTrace trace s desc).1 (runVerveTrace trace s desc).2 = true ∧
    MutatorStackInv (runVerveTrace trace s desc).1 true false = true := by
  induction trace generalizing s desc with
  | nil =>
      unfold runVerveTrace
      refine ⟨hScan, ?_⟩
      unfold ScanStackInv at hScan
      unfold MutatorStackInv
      rw [hSlot0, hSlot1] at hScan
      rcases Bool.and_eq_true_iff.mp hScan with ⟨hLeft, h1⟩
      rcases Bool.and_eq_true_iff.mp hLeft with ⟨_, h0⟩
      exact Bool.and_eq_true_iff.mpr ⟨h0, h1⟩
  | cons t rest ih =>
      unfold runVerveTrace
      cases t with
      | talWritePrim1 w =>
          have hNext : ScanStackInv (stepVerveSeam s desc (.talWritePrim1 w)).1
              (stepVerveSeam s desc (.talWritePrim1 w)).2 = true := by
            unfold ScanStackInv at hScan ⊢
            unfold stepVerveSeam
            rw [hSlot0] at hScan ⊢
            rcases Bool.and_eq_true_iff.mp hScan with ⟨hLeft, _⟩
            rcases Bool.and_eq_true_iff.mp hLeft with ⟨_, h0⟩
            apply Bool.and_eq_true_iff.mpr
            refine ⟨?_, verveValueMatch_prim_refl s.toAbs w⟩
            exact Bool.and_eq_true_iff.mpr ⟨rfl, h0⟩
          exact ih _ _ hNext hSlot0 rfl
      | callAllocObject =>
          have hNext := verve_alloc_preserves_scanStackInv s desc hScan hSlot1
          exact ih _ _ hNext rfl hSlot1
      | callYield =>
          have hNext : ScanStackInv (stepVerveSeam s desc .callYield).1
              (stepVerveSeam s desc .callYield).2 = true := by
            unfold stepVerveSeam nucleusYield ScanStackInv
            exact hScan
          exact ih _ _ hNext hSlot0 hSlot1
      | callGarbageCollect =>
          have hGC := (verve_gc_preserves_scanStackInv s desc hScan hSlot0 hSlot1).1
          exact ih _ _ hGC hSlot0 hSlot1

/-!
## Part 5: Certified Abstraction Layers (`CertiKOS` OSDI 2016) + Dynamic Certificate Admission & Mapping to Anneal

Unifies CertiKOS contextual layer refinement (`gu16_certikos.txt:433`) with load-time
PCC/FPCC certificate verification inside Anneal's `Partial` refinement lattice
(`joshlf/anneal` commit `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`,
`trusted/lean/Trusted/Refinement.lean:244-458` & `theory/Anneal/Refinement.lean:185-253`).
-/

structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def PartialLe {Out : Type} (p₁ p₂ : Partial (Out → Prop)) : Prop :=
  ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, ∀ o, p₁.val h₁ o → p₂.val h₂ o

def BehaviorLe {Query Out : Type}
    (b₁ b₂ : Query → Partial (Out → Prop)) : Prop :=
  ∀ q, PartialLe (b₁ q) (b₂ q)

theorem BehaviorLe.refl {Query Out : Type} (b : Query → Partial (Out → Prop)) :
    BehaviorLe b b :=
  fun _ h => ⟨h, fun _ ho => ho⟩

theorem BehaviorLe.trans {Query Out : Type}
    {b₁ b₂ b₃ : Query → Partial (Out → Prop)}
    (h₁₂ : BehaviorLe b₁ b₂) (h₂₃ : BehaviorLe b₂ b₃) :
    BehaviorLe b₁ b₃ := by
  intro q h₃
  rcases h₂₃ q h₃ with ⟨h₂, hVal₂₃⟩
  rcases h₁₂ q h₂ with ⟨h₁, hVal₁₂⟩
  exact ⟨h₁, fun o ho => hVal₂₃ o (hVal₁₂ o ho)⟩

def SpecOn {Query Out : Type} (pre : Query → Prop) (post : Query → Out → Prop) :
    Query → Partial (Out → Prop) :=
  fun q => { defined := pre q, val := fun _ o => post q o }

def WellFormedOn {Query Out : Type} (pre : Query → Prop) :
    Query → Partial (Out → Prop) :=
  SpecOn pre (fun _ _ => True)

def MonotoneMap {Q₁ O₁ Q₂ O₂ : Type}
    (π : (Q₁ → Partial (O₁ → Prop)) → (Q₂ → Partial (O₂ → Prop))) : Prop :=
  ∀ b₁ b₂, BehaviorLe b₁ b₂ → BehaviorLe (π b₁) (π b₂)

def CertiKOSContextualRefinement
    {ExtProg QAbs OAbs QHw OHw : Type}
    (semAbs : ExtProg → QAbs → Partial (OAbs → Prop))
    (semHw : ExtProg → QHw → Partial (OHw → Prop))
    (π : (QAbs → Partial (OAbs → Prop)) → (QHw → Partial (OHw → Prop))) : Prop :=
  MonotoneMap π ∧ ∀ (P : ExtProg), BehaviorLe (semHw P) (π (semAbs P))

theorem certikos_layered_host_with_certified_extension_soundness
    {ExtProg QAbs OAbs QHw OHw : Type}
    {semAbs : ExtProg → QAbs → Partial (OAbs → Prop)}
    {semHw : ExtProg → QHw → Partial (OHw → Prop)}
    {π : (QAbs → Partial (OAbs → Prop)) → (QHw → Partial (OHw → Prop))}
    (hKernel : CertiKOSContextualRefinement semAbs semHw π)
    (P : ExtProg)
    (pre : QAbs → Prop) (post : QAbs → OAbs → Prop)
    (hCert : BehaviorLe (semAbs P) (SpecOn pre post)) :
    BehaviorLe (semHw P) (π (SpecOn pre post)) ∧
    BehaviorLe (semHw P) (π (WellFormedOn pre)) := by
  rcases hKernel with ⟨hMono, hCtx⟩
  have hSpec : BehaviorLe (semHw P) (π (SpecOn pre post)) :=
    BehaviorLe.trans (hCtx P) (hMono (semAbs P) (SpecOn pre post) hCert)
  have hWfWeaken : BehaviorLe (SpecOn pre post) (WellFormedOn pre) :=
    fun _ hPre => ⟨hPre, fun _ _ => True.intro⟩
  have hWf : BehaviorLe (semHw P) (π (WellFormedOn pre)) :=
    BehaviorLe.trans hSpec (hMono (SpecOn pre post) (WellFormedOn pre) hWfWeaken)
  exact ⟨hSpec, hWf⟩

/-!
## Part 6: Closing the `Axiom Super` Gap in Hamid & Shao (TPHOLs 2004)
`rtpcc_coq/tphols/axtalp-cap.v:25,1701,1711-1731,1950,1953,2182`

In `rtpcc_coq/tphols/axtalp-cap.v`, Hamid & Shao interface an external Certified Assembly
Programming (Hoare-logic) array library (`cmds_arrayget`, lines 1416–1420) with a polymorphically
typed assembly language (`iXTAL`, `type_arrayget`, lines 1422–1466). While their modular Hoare
proof of the 6-instruction body (`extcodewf_arrayget_alt`, lines 1787–1887) is completely
axiom-free, their interface lemmas (`extcodewf_arrayget` at lines 1701, 1711–1731, `Q_arrayget_cpinv`
at lines 1950, 1953, and the `InstCodeTy` Remark at line 2182) resorted to
`Axiom Super : forall P:Prop, P` for three specific reasons:

1. **Intensional Function Equality on `Reg -> OmegaL` during De Bruijn Substitution (`lines 1701, 2179-2182`)**:
   `axtalp.v` represented register-file types as Coq functions `Reg -> OmegaL` and required
   propositional equality `=` of functions in `ListSubstL`, blocking reduction of `subst_aux`
   inside `fun r : Reg => match r with ...` without functional extensionality.
2. **Re-establishing `WFRegFile` and `TrRegFile` with an Updated Abstract Register File `R'` (`lines 1569-1572, 1722, 1950`)**:
   In `extcodewf_arrayget` (`line 1572`), the proof instantiated the post-state existential with
   the *unchanged* entry abstract register file `R` (where `R r0` is an array label `wl l_arr` of
   type `arrty`) instead of updating `R` at `r0` (the loaded `intty` element `MM(1 + a + i)`) and
   `r1` (the clobbered index `i + 1`).
3. **Unifying the Internal `iXTAL` Return Target (`CH l = code`, `line 1950`) and External `CAP`
   Stub Target (`CH l = stub`, `line 1953`)**:
   In `Q_arrayget_cpinv`, jumping to `r7` can land either in an `iXTAL` code block or in another
   `CAP` stub in `CH`.

Below we mechanize all three components constructively and prove the complete `iXTAL <-> CAP`
return-continuation bridge with **zero axioms** (`0 sorryAx`, `0 Classical.choice`).
-/

/-- The 8 architectural registers of `iXTAL` (`axtalp-cap.v:1429-1465`):
    - `r0` (`rA`): array pointer on entry / loaded `intty` element on return
    - `r1` (`rB`): array index on entry / clobbered `intty` scratch on return
    - `r2 .. r6`: callee-saved polymorphic registers (`\alpha_2 .. \alpha_6`)
    - `r7` (`rH`): return continuation code pointer -/
inductive TALReg where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7
  deriving DecidableEq, Repr

/-- Closed primitive/data types in `iXTAL` (`intty` and `arrty` in `axtalp.v`). -/
inductive PrimOrArrTy where
  | intty : PrimOrArrTy
  | arrty : PrimOrArrTy
  deriving DecidableEq, Repr

/-- Closed `iXTAL` register types, including code pointers `codety` parameterized by the
    expected types of `r0 .. r6` (with `r7` self-typed as the continuation). -/
inductive TALClosedTy where
  | prim : PrimOrArrTy → TALClosedTy
  | codety :
      PrimOrArrTy → PrimOrArrTy →
      PrimOrArrTy → PrimOrArrTy → PrimOrArrTy → PrimOrArrTy → PrimOrArrTy →
      TALClosedTy
  deriving DecidableEq, Repr

/-- Open `iXTAL` register types inside a polymorphic code signature `\forall \alpha_0 .. \alpha_4`:
    - `openPrim t`: closed primitive/array type
    - `tyVar idx`: De Bruijn / positional type variable `\alpha_{idx}` (`idx \in 0..4`)
    - `retContPoly`: the polymorphic return continuation type in `r7` of `type_arrayget`
      (`axtalp-cap.v:1438-1465`), which expects `r0 : intty`, `r1 : \beta_1`, and
      `r2 .. r6 : \alpha_0 .. \alpha_4`. -/
inductive TALOpenTy where
  | openPrim : PrimOrArrTy → TALOpenTy
  | tyVar : Nat → TALOpenTy
  | retContPoly : TALOpenTy
  deriving DecidableEq, Repr

/-- The polymorphic code signature `type_arrayget` (`axtalp-cap.v:1422-1466`). -/
def type_arrayget : TALReg → TALOpenTy
  | .r0 => .openPrim .arrty
  | .r1 => .openPrim .intty
  | .r2 => .tyVar 0
  | .r3 => .tyVar 1
  | .r4 => .tyVar 2
  | .r5 => .tyVar 3
  | .r6 => .tyVar 4
  | .r7 => .retContPoly

/-- Type-variable lookup for the 5 callee-saved register type variables `(t2, t3, t4, t5, t6)`. -/
def lookupTyVar5 (t2 t3 t4 t5 t6 : PrimOrArrTy) : Nat → PrimOrArrTy
  | 0 => t2
  | 1 => t3
  | 2 => t4
  | 3 => t5
  | _ => t6

/-- Substitutes the 5 polymorphic callee-saved type variables `(t2, t3, t4, t5, t6)` and
    instantiates the return continuation's clobbered `r1` type parameter `\beta_1 := intty`
    (`axtalp-cap.v:1573, 1667`). -/
def substOpenTy (t2 t3 t4 t5 t6 : PrimOrArrTy) : TALOpenTy → TALClosedTy
  | .openPrim p => .prim p
  | .tyVar idx => .prim (lookupTyVar5 t2 t3 t4 t5 t6 idx)
  | .retContPoly => .codety .intty .intty t2 t3 t4 t5 t6

/-- The closed entry register-file type environment after instantiating `type_arrayget` with
    `(t2, t3, t4, t5, t6)`. -/
def entryArrayGetEnv (t2 t3 t4 t5 t6 : PrimOrArrTy) : TALReg → TALClosedTy
  | .r0 => .prim .arrty
  | .r1 => .prim .intty
  | .r2 => .prim t2
  | .r3 => .prim t3
  | .r4 => .prim t4
  | .r5 => .prim t5
  | .r6 => .prim t6
  | .r7 => .codety .intty .intty t2 t3 t4 t5 t6

/-- The closed return-continuation register-file type environment `G0` expected by `r7`
    when `cmds_arrayget` executes `_jmp rH` (`axtalp-cap.v:1443-1465, 1667-1684`):
    `r0` now holds the loaded `intty` array element, `r1` holds `intty` (`i + 1`),
    `r2 .. r6` still hold `t2 .. t6`, and `r7` still holds the code pointer. -/
def returnContEnv (t2 t3 t4 t5 t6 : PrimOrArrTy) : TALReg → TALClosedTy
  | .r0 => .prim .intty
  | .r1 => .prim .intty
  | .r2 => .prim t2
  | .r3 => .prim t3
  | .r4 => .prim t4
  | .r5 => .prim t5
  | .r6 => .prim t6
  | .r7 => .codety .intty .intty t2 t3 t4 t5 t6

/-- **Theorem (`tal_polymorphic_inst_pointwise_sound`)**:
    Closes the `apply Super` at `axtalp-cap.v:1701, 2182` by formulating polymorphic code-type
    instantiation pointwise over `r : TALReg`. Case analysis over the finite register inductive
    `TALReg` reduces substitution definitionally (`rfl`) for every register without functional
    extensionality or `Super`! -/
theorem tal_polymorphic_inst_pointwise_sound
    (t2 t3 t4 t5 t6 : PrimOrArrTy) (r : TALReg) :
    substOpenTy t2 t3 t4 t5 t6 (type_arrayget r) = entryArrayGetEnv t2 t3 t4 t5 t6 r := by
  cases r <;> rfl

/-- Abstract `iXTAL` word values (`WordVal` in `axtalp.v` / `axtalp-cap.v:100-104`):
    - `wi n`: immediate integer literal `n`
    - `wlArr l`: data-heap label `l` pointing to an array block
    - `wlCode l`: code-heap label `l` pointing to an `iXTAL` block or `CAP` stub -/
inductive TALWordVal where
  | wi : Nat → TALWordVal
  | wlArr : Nat → TALWordVal
  | wlCode : Nat → TALWordVal
  deriving DecidableEq, Repr

/-- Data-heap array entry (`TrHeapVal (array Ns) (n :: Ns)` in `axtalp-cap.v:129-131, 155-169`). -/
structure TALArrayBlock where
  baseAddr : Nat
  len : Nat
  elemAt : Nat → Nat

/-- Code-heap entry (`CHeapVal` in `axtalp-cap.v:122-127, 233-265`):
    - `talCode`: an internal `iXTAL` instruction sequence with expected register environment
    - `capStub`: an external Hoare-certified `CAP` stub with the same signature interface -/
inductive CHeapEntry where
  | talCode :
      PrimOrArrTy → PrimOrArrTy →
      PrimOrArrTy → PrimOrArrTy → PrimOrArrTy → PrimOrArrTy → PrimOrArrTy →
      Nat → CHeapEntry
  | capStub :
      PrimOrArrTy → PrimOrArrTy →
      PrimOrArrTy → PrimOrArrTy → PrimOrArrTy → PrimOrArrTy → PrimOrArrTy →
      Nat → CHeapEntry
  deriving DecidableEq, Repr

def CHeapEntry.matchesCodeTy (entry : CHeapEntry) (ty : TALClosedTy) : Bool :=
  match entry, ty with
  | .talCode a0 a1 a2 a3 a4 a5 a6 _, .codety b0 b1 b2 b3 b4 b5 b6 =>
      decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2) &&
      decide (a3 = b3) && decide (a4 = b4) && decide (a5 = b5) && decide (a6 = b6)
  | .capStub a0 a1 a2 a3 a4 a5 a6 _, .codety b0 b1 b2 b3 b4 b5 b6 =>
      decide (a0 = b0) && decide (a1 = b1) && decide (a2 = b2) &&
      decide (a3 = b3) && decide (a4 = b4) && decide (a5 = b5) && decide (a6 = b6)
  | _, _ => false

/-- Abstract typing of an `iXTAL` word value (`WFWordVal` in `axtalp-cap.v:1926, 1544`). -/
def WFWordVal (cHeap : Nat → Option CHeapEntry) (dHeap : Nat → Option TALArrayBlock)
    (wv : TALWordVal) (ty : TALClosedTy) : Bool :=
  match wv, ty with
  | .wi _, .prim .intty => true
  | .wlArr l, .prim .arrty =>
      match dHeap l with
      | some _ => true
      | none => false
  | .wlCode l, .codety _ _ _ _ _ _ _ =>
      match cHeap l with
      | some entry => entry.matchesCodeTy ty
      | none => false
  | _, _ => false

/-- Translation of an abstract `iXTAL` word value to a concrete machine word
    (`TrWordVal` in `axtalp-cap.v:100-104`). -/
def TrWordVal (cLyt : Nat → Nat) (dHeap : Nat → Option TALArrayBlock)
    (wv : TALWordVal) (w : Nat) : Bool :=
  match wv with
  | .wi n => Nat.beq w n
  | .wlArr l =>
      match dHeap l with
      | some blk => Nat.beq w blk.baseAddr
      | none => false
  | .wlCode l => Nat.beq w (cLyt l)

/-- Pointwise abstract register-file typing (`WFRegFile` in `axtalp-cap.v:217`). -/
def WFRegFile (cHeap : Nat → Option CHeapEntry) (dHeap : Nat → Option TALArrayBlock)
    (R : TALReg → TALWordVal) (G : TALReg → TALClosedTy) : Bool :=
  WFWordVal cHeap dHeap (R .r0) (G .r0) &&
  WFWordVal cHeap dHeap (R .r1) (G .r1) &&
  WFWordVal cHeap dHeap (R .r2) (G .r2) &&
  WFWordVal cHeap dHeap (R .r3) (G .r3) &&
  WFWordVal cHeap dHeap (R .r4) (G .r4) &&
  WFWordVal cHeap dHeap (R .r5) (G .r5) &&
  WFWordVal cHeap dHeap (R .r6) (G .r6) &&
  WFWordVal cHeap dHeap (R .r7) (G .r7)

/-- Pointwise register-file translation (`TrRegFile` in `axtalp-cap.v:133-134, 220`). -/
def TrRegFile (cLyt : Nat → Nat) (dHeap : Nat → Option TALArrayBlock)
    (R : TALReg → TALWordVal) (RR : TALReg → Nat) : Bool :=
  TrWordVal cLyt dHeap (R .r0) (RR .r0) &&
  TrWordVal cLyt dHeap (R .r1) (RR .r1) &&
  TrWordVal cLyt dHeap (R .r2) (RR .r2) &&
  TrWordVal cLyt dHeap (R .r3) (RR .r3) &&
  TrWordVal cLyt dHeap (R .r4) (RR .r4) &&
  TrWordVal cLyt dHeap (R .r5) (RR .r5) &&
  TrWordVal cLyt dHeap (R .r6) (RR .r6) &&
  TrWordVal cLyt dHeap (R .r7) (RR .r7)

/-- Demonstrates why `axtalp-cap.v:1572` (`Exists4 DLyt H R HT` with the *unmodified* entry
    register file `R`) failed and forced `apply Super`:
    At entry to `cmds_arrayget`, `R .r0 = .wlArr l` (an array pointer of type `.prim .arrty`),
    whereas the return continuation `G_ret` expects `.r0 : .prim .intty`. -/
theorem cap_naive_unmodified_regfile_unsound
    (cHeap : Nat → Option CHeapEntry) (dHeap : Nat → Option TALArrayBlock)
    (R : TALReg → TALWordVal) (l : Nat)
    (t2 t3 t4 t5 t6 : PrimOrArrTy)
    (hR0 : R .r0 = .wlArr l) :
    WFRegFile cHeap dHeap R (returnContEnv t2 t3 t4 t5 t6) = false := by
  unfold WFRegFile returnContEnv
  rw [hR0]
  rfl

/-- Updates the abstract `iXTAL` register file `R` after `cmds_arrayget` loads `elemVal` into
    `r0` and increments `r1` to `newR1Val` (`axtalp-cap.v:1948-1950`). -/
def updatePostArrayGetR (R : TALReg → TALWordVal) (elemVal newR1Val : Nat) :
    TALReg → TALWordVal
  | .r0 => .wi elemVal
  | .r1 => .wi newR1Val
  | .r2 => R .r2
  | .r3 => R .r3
  | .r4 => R .r4
  | .r5 => R .r5
  | .r6 => R .r6
  | .r7 => R .r7

/-- Updates the concrete machine register file `RR` at the end of `cmds_arrayget`
    (`axtalp-cap.v:1899-1906`). -/
def updatePostArrayGetRR (RR : TALReg → Nat) (elemVal newR1Val : Nat) :
    TALReg → Nat
  | .r0 => elemVal
  | .r1 => newR1Val
  | .r2 => RR .r2
  | .r3 => RR .r3
  | .r4 => RR .r4
  | .r5 => RR .r5
  | .r6 => RR .r6
  | .r7 => RR .r7

/-- **Theorem (`cap_arrayget_return_env_preservation`)**:
    Closes the `apply Super` at `axtalp-cap.v:1722, 1950`:
    If `(R, RR)` satisfies `WFRegFile` and `TrRegFile` for `entryArrayGetEnv t2 t3 t4 t5 t6`
    on entry to `cmds_arrayget`, then for any loaded element `elemVal` and updated index `newR1Val`,
    `(updatePostArrayGetR R elemVal newR1Val, updatePostArrayGetRR RR elemVal newR1Val)`
    satisfies both `WFRegFile` and `TrRegFile` for `returnContEnv t2 t3 t4 t5 t6`! -/
theorem cap_arrayget_return_env_preservation
    (cLyt : Nat → Nat)
    (cHeap : Nat → Option CHeapEntry) (dHeap : Nat → Option TALArrayBlock)
    (R : TALReg → TALWordVal) (RR : TALReg → Nat)
    (t2 t3 t4 t5 t6 : PrimOrArrTy)
    (elemVal newR1Val : Nat)
    (hWF : WFRegFile cHeap dHeap R (entryArrayGetEnv t2 t3 t4 t5 t6) = true)
    (hTr : TrRegFile cLyt dHeap R RR = true) :
    WFRegFile cHeap dHeap (updatePostArrayGetR R elemVal newR1Val)
      (returnContEnv t2 t3 t4 t5 t6) = true ∧
    TrRegFile cLyt dHeap (updatePostArrayGetR R elemVal newR1Val)
      (updatePostArrayGetRR RR elemVal newR1Val) = true := by
  unfold WFRegFile entryArrayGetEnv at hWF
  unfold TrRegFile at hTr
  rcases Bool.and_eq_true_iff.mp hWF with ⟨hW1, hW7⟩
  rcases Bool.and_eq_true_iff.mp hW1 with ⟨hW2, hW6⟩
  rcases Bool.and_eq_true_iff.mp hW2 with ⟨hW3, hW5⟩
  rcases Bool.and_eq_true_iff.mp hW3 with ⟨hW4, hW4_reg⟩
  rcases Bool.and_eq_true_iff.mp hW4 with ⟨hW5', hW3_reg⟩
  rcases Bool.and_eq_true_iff.mp hW5' with ⟨_, hW2_reg⟩
  rcases Bool.and_eq_true_iff.mp hTr with ⟨hT1, hT7⟩
  rcases Bool.and_eq_true_iff.mp hT1 with ⟨hT2, hT6⟩
  rcases Bool.and_eq_true_iff.mp hT2 with ⟨hT3, hT5⟩
  rcases Bool.and_eq_true_iff.mp hT3 with ⟨hT4, hT4_reg⟩
  rcases Bool.and_eq_true_iff.mp hT4 with ⟨hT5', hT3_reg⟩
  rcases Bool.and_eq_true_iff.mp hT5' with ⟨_, hT2_reg⟩
  refine ⟨?_, ?_⟩
  · unfold WFRegFile updatePostArrayGetR returnContEnv
    change (true && true &&
      WFWordVal cHeap dHeap (R .r2) (.prim t2) &&
      WFWordVal cHeap dHeap (R .r3) (.prim t3) &&
      WFWordVal cHeap dHeap (R .r4) (.prim t4) &&
      WFWordVal cHeap dHeap (R .r5) (.prim t5) &&
      WFWordVal cHeap dHeap (R .r6) (.prim t6) &&
      WFWordVal cHeap dHeap (R .r7) (.codety .intty .intty t2 t3 t4 t5 t6)) = true
    rw [hW2_reg, hW3_reg, hW4_reg, hW5, hW6, hW7]
    rfl
  · unfold TrRegFile updatePostArrayGetR updatePostArrayGetRR TrWordVal
    change (Nat.beq elemVal elemVal && Nat.beq newR1Val newR1Val &&
      TrWordVal cLyt dHeap (R .r2) (RR .r2) &&
      TrWordVal cLyt dHeap (R .r3) (RR .r3) &&
      TrWordVal cLyt dHeap (R .r4) (RR .r4) &&
      TrWordVal cLyt dHeap (R .r5) (RR .r5) &&
      TrWordVal cLyt dHeap (R .r6) (RR .r6) &&
      TrWordVal cLyt dHeap (R .r7) (RR .r7)) = true
    rw [nat_beq_refl elemVal, nat_beq_refl newR1Val, hT2_reg, hT3_reg, hT4_reg, hT5, hT6, hT7]
    rfl

/-- Concrete machine state for the 6-instruction `cmds_arrayget` routine (`axtalp-cap.v:1416-1420`). -/
structure CAPMachineState where
  mem : Nat → Nat
  regs : TALReg → Nat
  rI : Nat
  pc : Nat

/-- Concrete execution of `cmds_arrayget` (`axtalp-cap.v:1416-1420`):
    1. `_ld rI rA 0`         (`rI := mem[r0]`, array length `n`)
    2. `_addi rB rB 1`       (`r1 := r1 + 1`, 1-based offset `i + 1`)
    3. `_bgt rB rI 0`        (if `rI < r1`, i.e., `n < i + 1`, jump to `lab_arroutbounds = 0`)
    4. `_add rA rA rB`       (`r0 := r0 + (i + 1)`)
    5. `_ld rA rA 0`         (`r0 := mem[r0 + i + 1]`)
    6. `_jmp rH`             (`pc := r7`) -/
def execCmdsArrayGet (st : CAPMachineState) : CAPMachineState :=
  if natBlt (st.mem (st.regs .r0)) (st.regs .r1 + 1) then
    { st with
      rI := st.mem (st.regs .r0)
      regs := fun r => match r with | .r1 => st.regs .r1 + 1 | other => st.regs other
      pc := 0 }
  else
    { st with
      rI := st.mem (st.regs .r0)
      regs := updatePostArrayGetRR st.regs
        (st.mem (st.regs .r0 + (st.regs .r1 + 1))) (st.regs .r1 + 1)
      pc := st.regs .r7 }

/-- `CpInv` at the return continuation target (`axtalp-cap.v:204-221, 1936`):
    Checks that `pc` resolves to a valid code entry in `cHeap` (either an `iXTAL` block
    `.talCode` or an external `CAP` stub `.capStub`, unifying lines 1950 and 1953!)
    and that `(R, st.regs)` satisfies `WFRegFile` and `TrRegFile` for `returnContEnv`. -/
def ReturnTargetCpInv
    (cLyt : Nat → Nat)
    (cHeap : Nat → Option CHeapEntry) (dHeap : Nat → Option TALArrayBlock)
    (t2 t3 t4 t5 t6 : PrimOrArrTy)
    (retLabel : Nat) (R : TALReg → TALWordVal) (st : CAPMachineState) : Bool :=
  Nat.beq st.pc (cLyt retLabel) &&
  (match cHeap retLabel with
   | some entry => entry.matchesCodeTy (.codety .intty .intty t2 t3 t4 t5 t6)
   | none => false) &&
  WFRegFile cHeap dHeap R (returnContEnv t2 t3 t4 t5 t6) &&
  TrRegFile cLyt dHeap R st.regs

/-- **Theorem (`cap_tal_return_continuation_bridge_soundness`)**:
    Completely closes `Q_arrayget_cpinv` (`axtalp-cap.v:1891-1957`, both line 1950 for returning
    to `iXTAL` code and line 1953 for jumping to another `CAP` stub) with **zero `Super` axioms**:
    Starting from any entry state `st` and abstract register file `R` satisfying `WFRegFile` and
    `TrRegFile` for `entryArrayGetEnv t2 t3 t4 t5 t6` where `R .r7 = .wlCode retLabel`:
    1. If the index is out of bounds (`natBlt (st.mem (st.regs .r0)) (st.regs .r1 + 1) = true`),
       `execCmdsArrayGet st` jumps to the trusted out-of-bounds handler `(execCmdsArrayGet st).pc = 0`.
    2. If the index is in bounds (`natBlt (st.mem (st.regs .r0)) (st.regs .r1 + 1) = false`),
       `execCmdsArrayGet st` establishes `ReturnTargetCpInv` at `(execCmdsArrayGet st).pc = cLyt retLabel`
       under the updated abstract register file
       `R' = updatePostArrayGetR R (st.mem (st.regs .r0 + (st.regs .r1 + 1))) (st.regs .r1 + 1)`
       — regardless of whether `cHeap retLabel` is a `.talCode` block (line 1950) or a `.capStub`
       block (line 1953)! -/
theorem cap_tal_return_continuation_bridge_soundness
    (cLyt : Nat → Nat)
    (cHeap : Nat → Option CHeapEntry) (dHeap : Nat → Option TALArrayBlock)
    (R : TALReg → TALWordVal) (st : CAPMachineState)
    (t2 t3 t4 t5 t6 : PrimOrArrTy) (retLabel : Nat)
    (hR7 : R .r7 = .wlCode retLabel)
    (hWF : WFRegFile cHeap dHeap R (entryArrayGetEnv t2 t3 t4 t5 t6) = true)
    (hTr : TrRegFile cLyt dHeap R st.regs = true) :
    (natBlt (st.mem (st.regs .r0)) (st.regs .r1 + 1) = true →
      (execCmdsArrayGet st).pc = 0) ∧
    (natBlt (st.mem (st.regs .r0)) (st.regs .r1 + 1) = false →
      ReturnTargetCpInv cLyt cHeap dHeap t2 t3 t4 t5 t6 retLabel
        (updatePostArrayGetR R
          (st.mem (st.regs .r0 + (st.regs .r1 + 1))) (st.regs .r1 + 1))
        (execCmdsArrayGet st) = true) := by
  refine ⟨?_, ?_⟩
  · intro hOob
    unfold execCmdsArrayGet
    rw [hOob]
    rfl
  · intro hInBounds
    unfold execCmdsArrayGet
    rw [hInBounds]
    have hPres := cap_arrayget_return_env_preservation
      cLyt cHeap dHeap R st.regs t2 t3 t4 t5 t6
      (st.mem (st.regs .r0 + (st.regs .r1 + 1))) (st.regs .r1 + 1) hWF hTr
    rcases hPres with ⟨hWF', hTr'⟩
    have hW7 : WFWordVal cHeap dHeap (R .r7) (.codety .intty .intty t2 t3 t4 t5 t6) = true := by
      unfold WFRegFile entryArrayGetEnv at hWF
      exact (Bool.and_eq_true_iff.mp hWF).2
    have hT7 : TrWordVal cLyt dHeap (R .r7) (st.regs .r7) = true := by
      unfold TrRegFile at hTr
      exact (Bool.and_eq_true_iff.mp hTr).2
    rw [hR7] at hW7 hT7
    change (match cHeap retLabel with
      | some entry => entry.matchesCodeTy (.codety .intty .intty t2 t3 t4 t5 t6)
      | none => false) = true at hW7
    change Nat.beq (st.regs .r7) (cLyt retLabel) = true at hT7
    change ((Nat.beq (st.regs .r7) (cLyt retLabel) &&
      (match cHeap retLabel with
       | some entry => entry.matchesCodeTy (.codety .intty .intty t2 t3 t4 t5 t6)
       | none => false)) &&
      WFRegFile cHeap dHeap
        (updatePostArrayGetR R (st.mem (st.regs .r0 + (st.regs .r1 + 1))) (st.regs .r1 + 1))
        (returnContEnv t2 t3 t4 t5 t6) &&
      TrRegFile cLyt dHeap
        (updatePostArrayGetR R (st.mem (st.regs .r0 + (st.regs .r1 + 1))) (st.regs .r1 + 1))
        (updatePostArrayGetRR st.regs
          (st.mem (st.regs .r0 + (st.regs .r1 + 1))) (st.regs .r1 + 1))) = true
    rw [hT7, hW7, hWF', hTr']
    rfl

/-!
## Part 7: Necula & Lee OSDI 1996 §3.3 / §4 & `CMU-CS-98-154` §2.3
Looping Packet Filter Termination & Ranking Certificates

In OSDI 1996 §4 (`necula96_osdi.txt:1164-1186`) and `CMU-CS-98-154` §2.3 (`necula98_thesis.txt:2126-2142`),
Necula & Lee note two fundamental facts about looping kernel extensions (such as the 39-instruction
DEC Alpha IP-header checksum / variable-length IPv4 options loop):
1. Cutpoint invariants (`inv`) alone establish **partial correctness / safety** (`SafeStep` holds at
   every finite prefix), NOT termination (`necula98_thesis.txt:2130-2131`).
2. However, **bounded termination within a certified instruction budget** (or via a strictly
   decreasing cutpoint/step ranking function `rank : MachineState -> Nat`) IS a safety property
   enforceable by `VCGen` (`necula98_thesis.txt:2132-2142`).

We mechanize both facts below and verify a concrete looping IPv4 options/checksum packet filter
(`filter3LoopProg`) with both safety and guaranteed termination.
-/

/-- A looping program `[inv 0, jmp 0]` whose backward jump targets the `inv 0` cutpoint. -/
def infiniteSafeLoopProg : List Instr :=
  [ .inv 0
  , .jmp 0 ]

def infiniteSafeLoopCert : List PCAssertion :=
  [ { abiAndBasesIntact := true, maxR4 := none }
  , { abiAndBasesIntact := true, maxR4 := none } ]

theorem stepN_step_comm (p : List Instr) (k : Nat) (s : MachineState) :
    stepN p (k + 1) s = stepInstr p (stepN p k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ m ihm =>
      unfold stepN
      exact ihm (stepInstr p s)

theorem infiniteSafeLoop_stays_at_0_or_1 (fuel : Nat) :
    ((stepN infiniteSafeLoopProg fuel filter1InitState).pc = 0 ∧
     (stepN infiniteSafeLoopProg fuel filter1InitState).halted = false) ∨
    ((stepN infiniteSafeLoopProg fuel filter1InitState).pc = 1 ∧
     (stepN infiniteSafeLoopProg fuel filter1InitState).halted = false) := by
  induction fuel with
  | zero =>
      left
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      rcases ih with ⟨hPc0, hHalt0⟩ | ⟨hPc1, hHalt1⟩
      · right
        rw [stepN_step_comm]
        unfold stepInstr
        rw [hHalt0, hPc0]
        exact ⟨rfl, rfl⟩
      · left
        rw [stepN_step_comm]
        unfold stepInstr
        rw [hHalt1, hPc1]
        exact ⟨rfl, rfl⟩

/-- **Theorem (`pcc_cutpoint_safety_without_ranking_diverges`)**:
    Proves that cutpoint dominance (`dominatesAllBackEdges = true`) and cutpoint VC verification
    (`checkCert = true`) guarantee memory safety across all steps (`runSafeFor = true`),
    yet allow an extension to loop forever in Ring 0 (`halted = false` for all `fuel : Nat`)
    unless paired with a ranking / instruction-budget termination certificate! -/
theorem pcc_cutpoint_safety_without_ranking_diverges (fuel : Nat) :
    dominatesAllBackEdges infiniteSafeLoopProg = true ∧
    checkCert infiniteSafeLoopProg filter1Policy infiniteSafeLoopCert = true ∧
    runSafeFor infiniteSafeLoopProg filter1Policy fuel filter1InitState = true ∧
    (stepN infiniteSafeLoopProg fuel filter1InitState).halted = false := by
  have hCert : checkCert infiniteSafeLoopProg filter1Policy infiniteSafeLoopCert = true := by
    decide
  have hSound := pcc_kernel_extension_soundness
    infiniteSafeLoopProg filter1Policy infiniteSafeLoopCert hCert fuel filter1InitState (by decide)
  refine ⟨hSound.1, hCert, hSound.2, ?_⟩
  rcases infiniteSafeLoop_stays_at_0_or_1 fuel with ⟨_, hHalt⟩ | ⟨_, hHalt⟩
  · exact hHalt
  · exact hHalt

theorem nat_ble_pred_of_succ_ble : (a b : Nat) →
    Nat.ble (a + 1) (b + 1) = true → Nat.ble a b = true
  | _, _, h => h

theorem nat_ble_zero_right_eq_zero : (a : Nat) →
    Nat.ble a 0 = true → a = 0
  | 0, _ => rfl
  | _ + 1, h => Bool.noConfusion h

/-- Strengthened PCC state invariant that also tracks kernel ABI preservation (`preservesKernelABI`)
    once the machine reaches `halted = true`. -/
def PCCStateInvWithABI (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion)
    (s : MachineState) : Bool :=
  if s.halted then
    pol.preservesKernelABI s.regs
  else
    natBlt s.pc prog.length && (lookupAssertion cert s.pc).holds pol s

theorem pcc_step_preserves_state_inv_with_abi
    (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion) (s : MachineState)
    (hAll : checkAllInstrVCs prog pol cert 0 prog = true)
    (hInv : PCCStateInvWithABI prog pol cert s = true) :
    PCCStateInvWithABI prog pol cert (stepInstr prog s) = true := by
  have hBaseInv : PCCStateInv prog pol cert s = true := by
    unfold PCCStateInvWithABI at hInv
    unfold PCCStateInv
    cases hH : s.halted
    · rw [hH] at hInv
      exact hInv
    · rfl
  have hNextBase := pcc_step_preserves_state_inv prog pol cert s hAll hBaseInv
  have hSafe := pcc_state_inv_implies_safe_step prog pol cert s hAll hBaseInv
  cases hHalted : s.halted
  · unfold PCCStateInvWithABI at hInv ⊢
    rw [hHalted] at hInv
    change (natBlt s.pc prog.length && (lookupAssertion cert s.pc).holds pol s) = true at hInv
    rcases Bool.and_eq_true_iff.mp hInv with ⟨hPcBlt, _⟩
    rcases fetchInstr_some_of_blt prog s.pc hPcBlt with ⟨instr, hFetch⟩
    cases instr with
    | movi dst imm =>
        have hStepHalt : (stepInstr prog s).halted = false := by
          unfold stepInstr; rw [hHalted, hFetch]; rfl
        unfold PCCStateInv at hNextBase
        rw [hStepHalt] at hNextBase ⊢
        exact hNextBase
    | addi dst src imm =>
        have hStepHalt : (stepInstr prog s).halted = false := by
          unfold stepInstr; rw [hHalted, hFetch]; rfl
        unfold PCCStateInv at hNextBase
        rw [hStepHalt] at hNextBase ⊢
        exact hNextBase
    | load dst base off =>
        have hStepHalt : (stepInstr prog s).halted = false := by
          unfold stepInstr; rw [hHalted, hFetch]; rfl
        unfold PCCStateInv at hNextBase
        rw [hStepHalt] at hNextBase ⊢
        exact hNextBase
    | store base off src =>
        have hStepHalt : (stepInstr prog s).halted = false := by
          unfold stepInstr; rw [hHalted, hFetch]; rfl
        unfold PCCStateInv at hNextBase
        rw [hStepHalt] at hNextBase ⊢
        exact hNextBase
    | bge reg bound target =>
        have hStepHalt : (stepInstr prog s).halted = false := by
          unfold stepInstr; rw [hHalted, hFetch]
          change (if Nat.ble bound (s.regs.get reg) = true then { s with pc := target, halted := false }
                  else { s with pc := s.pc + 1, halted := false }).halted = false
          cases Nat.ble bound (s.regs.get reg) <;> rfl
        unfold PCCStateInv at hNextBase
        rw [hStepHalt] at hNextBase ⊢
        exact hNextBase
    | jmp target =>
        have hStepHalt : (stepInstr prog s).halted = false := by
          unfold stepInstr; rw [hHalted, hFetch]; rfl
        unfold PCCStateInv at hNextBase
        rw [hStepHalt] at hNextBase ⊢
        exact hNextBase
    | inv cutId =>
        have hStepHalt : (stepInstr prog s).halted = false := by
          unfold stepInstr; rw [hHalted, hFetch]; rfl
        unfold PCCStateInv at hNextBase
        rw [hStepHalt] at hNextBase ⊢
        exact hNextBase
    | ret =>
        unfold SafeStep at hSafe
        rw [hHalted, hFetch] at hSafe
        have hStepRet : stepInstr prog s = { s with halted := true } := by
          unfold stepInstr; rw [hHalted, hFetch]; rfl
        rw [hStepRet]
        exact hSafe
  · have hStepSame : stepInstr prog s = s := by
      unfold stepInstr; rw [hHalted]; rfl
    rw [hStepSame]
    exact hInv

/-- Multi-step termination + ABI preservation from a decreasing ranking function `rank`. -/
theorem pcc_ranking_halts_within_budget
    (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion)
    (rank : MachineState → Nat)
    (hAll : checkAllInstrVCs prog pol cert 0 prog = true)
    (hRankDec : ∀ s, PCCStateInv prog pol cert s = true → s.halted = false →
      Nat.ble (rank (stepInstr prog s) + 1) (rank s) = true)
    (fuel : Nat) (s : MachineState)
    (hInv : PCCStateInvWithABI prog pol cert s = true)
    (hBudget : Nat.ble (rank s) fuel = true) :
    (stepN prog fuel s).halted = true ∧
    pol.preservesKernelABI (stepN prog fuel s).regs = true := by
  induction fuel generalizing s with
  | zero =>
      unfold stepN
      have hRank0 : rank s = 0 := nat_ble_zero_right_eq_zero (rank s) hBudget
      cases hHalt : s.halted
      · have hBaseInv : PCCStateInv prog pol cert s = true := by
          unfold PCCStateInvWithABI at hInv
          unfold PCCStateInv
          rw [hHalt] at hInv ⊢
          exact hInv
        have hDec := hRankDec s hBaseInv hHalt
        rw [hRank0] at hDec
        exact Bool.noConfusion hDec
      · unfold PCCStateInvWithABI at hInv
        rw [hHalt] at hInv
        exact ⟨rfl, hInv⟩
  | succ n ih =>
      unfold stepN
      cases hHalt : s.halted
      · have hBaseInv : PCCStateInv prog pol cert s = true := by
          unfold PCCStateInvWithABI at hInv
          unfold PCCStateInv
          rw [hHalt] at hInv ⊢
          exact hInv
        have hDec := hRankDec s hBaseInv hHalt
        have hStepLeSucc : Nat.ble (rank (stepInstr prog s) + 1) (n + 1) = true :=
          nat_ble_trans (rank (stepInstr prog s) + 1) (rank s) (n + 1) hDec hBudget
        have hStepBudget : Nat.ble (rank (stepInstr prog s)) n = true :=
          nat_ble_pred_of_succ_ble (rank (stepInstr prog s)) n hStepLeSucc
        have hNextInv := pcc_step_preserves_state_inv_with_abi prog pol cert s hAll hInv
        exact ih (stepInstr prog s) hNextInv hStepBudget
      · have hStepSame : stepInstr prog s = s := by
          unfold stepInstr
          rw [hHalt]
          rfl
        rw [hStepSame]
        have hStayHalted : ∀ k, stepN prog k s = s := by
          intro k
          induction k with
          | zero => rfl
          | succ m ihm =>
              unfold stepN
              rw [hStepSame]
              exact ihm
        rw [hStayHalted n]
        unfold PCCStateInvWithABI at hInv
        rw [hHalt] at hInv
        exact ⟨hHalt, hInv⟩

/-- **Theorem (`pcc_loop_ranking_termination_soundness`)**:
    General soundness of Necula & Lee's cutpoint PCC with a ranking / instruction-budget witness:
    If `checkCert prog pol cert = true` and `rank : MachineState -> Nat` strictly decreases on
    every non-halted step from a `PCCStateInv` state, then starting from any valid kernel entry
    state `s₀` and any step budget `fuel` with `Nat.ble (rank s₀) fuel = true`:
    1. Every backward branch is dominated by an `inv` cutpoint (`dominatesAllBackEdges prog = true`),
    2. Every step executes safely with zero runtime bounds checks (`runSafeFor prog pol fuel s₀ = true`),
    3. The extension is guaranteed to terminate (`(stepN prog fuel s₀).halted = true`), and
    4. Upon return, all callee-saved kernel ABI registers are preserved
       (`pol.preservesKernelABI (stepN prog fuel s₀).regs = true`). -/
theorem pcc_loop_ranking_termination_soundness
    (prog : List Instr) (pol : SafetyPolicy) (cert : List PCAssertion)
    (rank : MachineState → Nat)
    (hCert : checkCert prog pol cert = true)
    (hRankDec : ∀ s, PCCStateInv prog pol cert s = true → s.halted = false →
      Nat.ble (rank (stepInstr prog s) + 1) (rank s) = true)
    (fuel : Nat) (s₀ : MachineState)
    (hInit : InitKernelState pol s₀ = true)
    (hBudget : Nat.ble (rank s₀) fuel = true) :
    dominatesAllBackEdges prog = true ∧
    runSafeFor prog pol fuel s₀ = true ∧
    (stepN prog fuel s₀).halted = true ∧
    pol.preservesKernelABI (stepN prog fuel s₀).regs = true := by
  have hSafety := pcc_kernel_extension_soundness prog pol cert hCert fuel s₀ hInit
  refine ⟨hSafety.1, hSafety.2, ?_⟩
  unfold checkCert at hCert
  rcases Bool.and_eq_true_iff.mp hCert with ⟨hLeft1, hAll⟩
  rcases Bool.and_eq_true_iff.mp hLeft1 with ⟨hLeft2, hEntryNone⟩
  rcases Bool.and_eq_true_iff.mp hLeft2 with ⟨_, hLen0⟩
  have hInitInv : PCCStateInvWithABI prog pol cert s₀ = true := by
    unfold InitKernelState at hInit
    rcases Bool.and_eq_true_iff.mp hInit with ⟨hI1, hIpl⟩
    rcases Bool.and_eq_true_iff.mp hI1 with ⟨hI2, hFp⟩
    rcases Bool.and_eq_true_iff.mp hI2 with ⟨hI3, hR3⟩
    rcases Bool.and_eq_true_iff.mp hI3 with ⟨hI4, hR1⟩
    rcases Bool.and_eq_true_iff.mp hI4 with ⟨hPc0, hNotHalted⟩
    have hPcEq : s₀.pc = 0 := nat_beq_eq hPc0
    have hHaltedFalse : s₀.halted = false := by
      cases h : s₀.halted
      · rfl
      · rw [h] at hNotHalted
        exact Bool.noConfusion hNotHalted
    unfold PCCStateInvWithABI
    rw [hHaltedFalse, hPcEq]
    change (natBlt 0 prog.length && (lookupAssertion cert 0).holds pol s₀) = true
    apply Bool.and_eq_true_iff.mpr
    refine ⟨hLen0, ?_⟩
    unfold PCAssertion.holds
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, ?_⟩
    · cases (lookupAssertion cert 0).abiAndBasesIntact
      · rfl
      · rw [hR1, hR3, hFp, hIpl]
        rfl
    · cases hMax0 : (lookupAssertion cert 0).maxR4 with
      | none => rfl
      | some _ =>
          rw [hMax0] at hEntryNone
          exact Bool.noConfusion hEntryNone
  exact pcc_ranking_halts_within_budget prog pol cert rank hAll hRankDec fuel s₀ hInitInv hBudget

/-- Concrete looping packet filter / IPv4 header options scanner (`filter3LoopProg`, modeling
    Necula & Lee OSDI '96 §3.3 / §4):
    - `0: movi r4, 0`       (initialize header scan counter `r4 := 0`)
    - `1: inv 0`            (loop invariant cutpoint dominating backward jump from PC 5)
    - `2: bge r4, 24, 6`    (exit loop to PC 6 when `r4 >= 24`, after 3 iterations: `0, 8, 16`)
    - `3: load r0, 16(r1)`  (read aligned IPv4 header word within `[pktBase, pktBase + 64)`)
    - `4: addi r4, r4, 8`   (advance scan counter by 8 bytes)
    - `5: jmp 1`            (backward jump to `inv 0` at PC 1)
    - `6: ret`              (return cleanly to kernel with ABI preserved) -/
def filter3LoopProg : List Instr :=
  [ .movi .r4 0
  , .inv 0
  , .bge .r4 24 6
  , .load .r0 .r1 16
  , .addi .r4 .r4 8
  , .jmp 1
  , .ret ]

/-- Cutpoint-anchored PCC certificate for `filter3LoopProg`.
    Notice that at the `inv 0` loop header (PC 1), `maxR4 = some 31`, which holds on initial
    entry (`0 <= 31`) and is re-established on the backward jump at PC 5 because the fall-through
    of `bge r4, 24, 6` at PC 2 strengthens the bound to `maxR4 = some 23` (`r4 + 1 <= 24`),
    and `addi r4, r4, 8` at PC 4 produces `maxR4 = some 31` (`23 + 8 = 31 <= 31`)! -/
def filter3LoopCert : List PCAssertion :=
  [ { abiAndBasesIntact := true, maxR4 := none }     -- PC 0: entry
  , { abiAndBasesIntact := true, maxR4 := some 31 }  -- PC 1: `inv 0` loop invariant (`r4 <= 31`)
  , { abiAndBasesIntact := true, maxR4 := some 31 }  -- PC 2: `bge r4, 24, 6`
  , { abiAndBasesIntact := true, maxR4 := some 23 }  -- PC 3: fall-through (`r4 + 1 <= 24`, so `r4 <= 23`)
  , { abiAndBasesIntact := true, maxR4 := some 23 }  -- PC 4: `addi r4, r4, 8`
  , { abiAndBasesIntact := true, maxR4 := some 31 }  -- PC 5: `jmp 1` (`23 + 8 = 31 <= 31`)
  , { abiAndBasesIntact := true, maxR4 := some 31 }  -- PC 6: `ret`
  ]

/-- **Theorem (`filter3_loop_pcc_verified_and_terminates`)**:
    Verifies that the looping packet filter `filter3LoopProg`:
    1. Satisfies back-edge cutpoint dominance (`dominatesAllBackEdges filter3LoopProg = true`),
    2. Passes the cutpoint PCC certificate checker (`checkCert filter3LoopProg filter1Policy filter3LoopCert = true`),
    3. Executes safely across all loop iterations (`runSafeFor filter3LoopProg filter1Policy 19 filter1InitState = true`), and
    4. Terminates cleanly within its 19-step instruction budget with the kernel ABI intact! -/
theorem filter3_loop_pcc_verified_and_terminates :
    dominatesAllBackEdges filter3LoopProg = true ∧
    checkCert filter3LoopProg filter1Policy filter3LoopCert = true ∧
    runSafeFor filter3LoopProg filter1Policy 19 filter1InitState = true ∧
    (stepN filter3LoopProg 19 filter1InitState).halted = true ∧
    filter1Policy.preservesKernelABI (stepN filter3LoopProg 19 filter1InitState).regs = true := by
  decide

end PccVerveFoundationalKernels

/-! ## Axiom Verification Audit -/
#print axioms PccVerveFoundationalKernels.filter1_pcc_verified
#print axioms PccVerveFoundationalKernels.filter1_executes_safely
#print axioms PccVerveFoundationalKernels.pcc_state_inv_implies_safe_step
#print axioms PccVerveFoundationalKernels.pcc_step_preserves_state_inv
#print axioms PccVerveFoundationalKernels.pcc_kernel_extension_soundness
#print axioms PccVerveFoundationalKernels.vcgen_missing_cutpoint_dominance_unsound
#print axioms PccVerveFoundationalKernels.vcgen_memory_aliasing_unsound
#print axioms PccVerveFoundationalKernels.vcgen_aliasing_guarded_sound
#print axioms PccVerveFoundationalKernels.vcgen_callee_save_omission_unsound
#print axioms PccVerveFoundationalKernels.fpcc_inv_preserved_at_any_step
#print axioms PccVerveFoundationalKernels.fpcc_semantic_certificate_soundness
#print axioms PccVerveFoundationalKernels.fpcc_prefix_run_soundness
#print axioms PccVerveFoundationalKernels.fpcc_syntactic_type_bridge_soundness
#print axioms PccVerveFoundationalKernels.verve_mid_allocation_interrupt_hazard
#print axioms PccVerveFoundationalKernels.verve_uninitialized_pointer_slot_gc_hazard
#print axioms PccVerveFoundationalKernels.verve_alloc_preserves_scanStackInv
#print axioms PccVerveFoundationalKernels.verve_gc_preserves_scanStackInv
#print axioms PccVerveFoundationalKernels.verve_two_regime_seam_soundness
#print axioms PccVerveFoundationalKernels.certikos_layered_host_with_certified_extension_soundness
#print axioms PccVerveFoundationalKernels.tal_polymorphic_inst_pointwise_sound
#print axioms PccVerveFoundationalKernels.cap_naive_unmodified_regfile_unsound
#print axioms PccVerveFoundationalKernels.cap_arrayget_return_env_preservation
#print axioms PccVerveFoundationalKernels.cap_tal_return_continuation_bridge_soundness
#print axioms PccVerveFoundationalKernels.pcc_cutpoint_safety_without_ranking_diverges
#print axioms PccVerveFoundationalKernels.pcc_loop_ranking_termination_soundness
#print axioms PccVerveFoundationalKernels.filter3_loop_pcc_verified_and_terminates
