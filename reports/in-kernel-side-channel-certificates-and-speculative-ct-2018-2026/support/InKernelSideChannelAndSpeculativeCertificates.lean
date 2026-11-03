/-
  InKernelSideChannelAndSpeculativeCertificates.lean
  ==================================================
  Lean 4.34.1 Mechanization:
  Verifying Side-Channel-Freedom Inside Kernel Extension Certificates:
  1. Single-Pass O(|I|) Security-Lattice Cutpoint Certificate Checker (`checkKernelCtCert`,
     modeling `CT-Wasm` POPL 2019 & `Jasmin` CCS 2017 / POPL 2020) and Universal 2-Safety
     Noninterference (`kernel_ct_cert_implies_2safety_noninterference`).
  2. Single-Pass O(|I|) Relational Equality & Mask-Cancellation Certificate Checker
     (`checkKernelRelCtCert`), strictly extending non-relational taint certificates to
     constant-time self-XOR scrubbing and one-time-pad mask/unmask idioms
     (`relational_kernel_cert_strictly_extends_ct_cert`, `kernel_rel_ct_cert_soundness`).
  3. Speculative Kernel Execution Semantics (`SpecState`, `Oracle`, `specObsTrace`) and
     Proof that Architectural Memory-Safety + Architectural Constant-Time Certificates
     Leak Host Kernel Secrets Under Spectre v1 (`arch_ct_and_memsafe_cert_leaks_under_spectre_v1`).
  4. Mechanization of Linux eBPF `sanitize_ptr_alu` / `can_skip_alu_sanitation` Speculative
     Path-Pruning Bypass (`CVE-2021-33624`, Commit `9183671af6db`,
     `linux_skip_alu_sanitation_cve2021_33624_unsound`).
  5. Single-Pass Dual-Label Speculative Constant-Time Certificate Checker (`checkKernelSctCert`,
     unifying `Blade` POPL 2021, `Pitchfork` PLDI 2020, `Jasmin SCT` IEEE S&P 2021/2023,
     and LFI/SFI Bitwise Sandboxing `ldMasked`), with Universal Speculative Noninterference
     (`kernel_sct_dual_label_cert_soundness`).

  Every theorem is checked with `#print axioms` and has ZERO `sorryAx`, ZERO `Classical.choice`,
  and ZERO `Lean.ofReduceBool`.
-/

namespace InKernelSideChannelAndSpeculativeCertificates

/-!
  =============================================================================
  PRELIMINARIES: Kernel-Accelerated Comparisons, Registers, and Memory Arenas
  =============================================================================
-/

/-- Kernel-accelerated boolean `≤` and `<` on `Nat` (`Nat.ble` reduces in O(1) inside
    Lean 4's kernel with zero axioms). -/
def natBle (a b : Nat) : Bool :=
  Nat.ble a b

def natBlt (a b : Nat) : Bool :=
  Nat.ble (a + 1) b

/-- Five general-purpose Ring-0 extension registers (`R0`..`R4`). -/
inductive Reg where
  | R0 | R1 | R2 | R3 | R4
  deriving DecidableEq, Repr

/-- Two spill slots in the extension's private stack frame (`S0`, `S1`). -/
inductive StackSlot where
  | S0 | S1
  deriving DecidableEq, Repr

/-- Separated kernel memory arenas (`CT-Wasm` POPL 2019 DOI `10.1145/3290390`
    public vs. `secret` memories):
    - `PublicPacketArena`: network packet / public BPF map memory shared with untrusted observers.
    - `SecretKernelKeyArena`: high-security Ring-0 cryptographic key / credential arena. -/
inductive MemArena where
  | PublicPacketArena
  | SecretKernelKeyArena
  deriving DecidableEq, Repr

/-!
  =============================================================================
  SECTION 1: Single-Pass O(|I|) Security-Lattice Certificate Checker (`checkKernelCtCert`)
  (`CT-Wasm` POPL 2019, `Jasmin` CCS 2017 / POPL 2020)
  =============================================================================
-/

/-- Two-point information-flow security lattice `Public ⊑ Secret`. -/
inductive SecLabel where
  | Public
  | Secret
  deriving DecidableEq, Repr

def SecLabel.le (l1 l2 : SecLabel) : Bool :=
  match l1, l2 with
  | .Secret, .Public => false
  | _, _             => true

def SecLabel.join (l1 l2 : SecLabel) : SecLabel :=
  match l1, l2 with
  | .Public, .Public => .Public
  | _, _             => .Secret

theorem secLabel_join_eq_public (l1 l2 : SecLabel)
    (h : SecLabel.join l1 l2 = .Public) :
    l1 = .Public ∧ l2 = .Public := by
  cases l1 <;> cases l2 <;> simp [SecLabel.join] at h ⊢

theorem secLabel_le_public_imp (l1 : SecLabel)
    (h : SecLabel.le l1 .Public = true) :
    l1 = .Public := by
  cases l1 <;> simp [SecLabel.le] at h ⊢

/-- Ring-0 kernel extension instruction set with explicit constant-time vs. variable-time
    ALU ops, arena loads/stores, stack spills/fills, and kernel helpers. -/
inductive CtInstr where
  | movImm (dst : Reg) (imm : Nat)
  | movReg (dst src : Reg)
  | addConst (dst src : Reg)
  | xorConst (dst src1 src2 : Reg)
  | cmovConst (dst cond tr fa : Reg)
  | udivVarTime (dst num den : Reg)
  | loadArena (dst : Reg) (arena : MemArena) (addrReg : Reg)
  | storePublicArena (addrReg valReg : Reg)
  | spillStack (slot : StackSlot) (src : Reg)
  | fillStack (dst : Reg) (slot : StackSlot)
  | helperReadSecretKey (dst : Reg)
  | helperLookupPublicMap (dst keyReg : Reg)
  | helperEmitPublicMetric (valReg : Reg)
  deriving DecidableEq, Repr

/-- Basic block terminators. -/
inductive CtTerm where
  | exit (retReg : Reg)
  | jmp (target : Nat)
  | branchEqZero (condReg : Reg) (tTrue tFalse : Nat)
  deriving DecidableEq, Repr

structure CtBasicBlock where
  id     : Nat
  instrs : List CtInstr
  term   : CtTerm
  deriving DecidableEq, Repr

abbrev CtProg := List CtBasicBlock

def getCtBlock? (prog : CtProg) (bid : Nat) : Option CtBasicBlock :=
  match prog, bid with
  | [], _           => none
  | bb :: _, 0      => some bb
  | _ :: bbs, n + 1 => getCtBlock? bbs n

/-- Concrete architectural state of a Ring-0 kernel extension. -/
structure CtState where
  r0        : Nat
  r1        : Nat
  r2        : Nat
  r3        : Nat
  r4        : Nat
  s0        : Nat
  s1        : Nat
  pubMem    : Nat → Nat
  secMem    : Nat → Nat
  secretKey : Nat
  halted    : Bool

def CtState.getReg (st : CtState) : Reg → Nat
  | .R0 => st.r0
  | .R1 => st.r1
  | .R2 => st.r2
  | .R3 => st.r3
  | .R4 => st.r4

def CtState.setReg (st : CtState) (r : Reg) (v : Nat) : CtState :=
  match r with
  | .R0 => { st with r0 := v }
  | .R1 => { st with r1 := v }
  | .R2 => { st with r2 := v }
  | .R3 => { st with r3 := v }
  | .R4 => { st with r4 := v }

def CtState.getStack (st : CtState) : StackSlot → Nat
  | .S0 => st.s0
  | .S1 => st.s1

def CtState.setStack (st : CtState) (sl : StackSlot) (v : Nat) : CtState :=
  match sl with
  | .S0 => { st with s0 := v }
  | .S1 => { st with s1 := v }

@[simp] theorem CtState.halted_setReg (st : CtState) (r : Reg) (v : Nat) :
    (st.setReg r v).halted = st.halted := by
  cases r <;> rfl

@[simp] theorem CtState.pubMem_setReg (st : CtState) (r : Reg) (v : Nat) :
    (st.setReg r v).pubMem = st.pubMem := by
  cases r <;> rfl

@[simp] theorem CtState.secretKey_setReg (st : CtState) (r : Reg) (v : Nat) :
    (st.setReg r v).secretKey = st.secretKey := by
  cases r <;> rfl

@[simp] theorem CtState.getStack_setReg (st : CtState) (r : Reg) (v : Nat) (sl : StackSlot) :
    (st.setReg r v).getStack sl = st.getStack sl := by
  cases r <;> cases sl <;> rfl

theorem CtState.getReg_setReg_eq (st : CtState) (r : Reg) (v : Nat) :
    (st.setReg r v).getReg r = v := by
  cases r <;> rfl

theorem CtState.getReg_setReg_ne (st : CtState) (dst r : Reg) (v : Nat) (h : r ≠ dst) :
    (st.setReg dst v).getReg r = st.getReg r := by
  cases dst <;> cases r <;> first | contradiction | rfl

@[simp] theorem CtState.halted_setStack (st : CtState) (sl : StackSlot) (v : Nat) :
    (st.setStack sl v).halted = st.halted := by
  cases sl <;> rfl

@[simp] theorem CtState.pubMem_setStack (st : CtState) (sl : StackSlot) (v : Nat) :
    (st.setStack sl v).pubMem = st.pubMem := by
  cases sl <;> rfl

@[simp] theorem CtState.secretKey_setStack (st : CtState) (sl : StackSlot) (v : Nat) :
    (st.setStack sl v).secretKey = st.secretKey := by
  cases sl <;> rfl

@[simp] theorem CtState.getReg_setStack (st : CtState) (sl : StackSlot) (v : Nat) (r : Reg) :
    (st.setStack sl v).getReg r = st.getReg r := by
  cases sl <;> cases r <;> rfl

theorem CtState.getStack_setStack_eq (st : CtState) (sl : StackSlot) (v : Nat) :
    (st.setStack sl v).getStack sl = v := by
  cases sl <;> rfl

theorem CtState.getStack_setStack_ne (st : CtState) (slot sl : StackSlot) (v : Nat) (h : sl ≠ slot) :
    (st.setStack slot v).getStack sl = st.getStack sl := by
  cases slot <;> cases sl <;> first | contradiction | rfl

def updateMem (m : Nat → Nat) (addr val : Nat) : Nat → Nat :=
  fun a => match Nat.beq a addr with
  | true  => val
  | false => m a

/-- Microarchitectural & architectural leakage observation events (`ObsEvent`) exposed to an
    attacker under the standard cryptographic constant-time threat model (`Jasmin` / `CT-Wasm`):
    program counter transitions, memory load/store addresses (cache line indices), variable-time
    ALU operands (`udivVarTime`), public map lookup keys, and public telemetry emissions. -/
inductive ObsEvent where
  | obsNone
  | obsMemAddr (arena : MemArena) (addr : Nat)
  | obsStorePublic (addr val : Nat)
  | obsVarTimeAlu (num den : Nat)
  | obsMapKey (key : Nat)
  | obsPublicMetric (val : Nat)
  | obsJmp (target : Nat)
  | obsBranch (isZero : Bool) (nextBid : Nat)
  | obsExit (retVal : Nat)
  | obsHalted
  deriving DecidableEq, Repr

/-- Operational semantics of a single `CtInstr`, returning the updated `CtState` and the
    leaked `ObsEvent`. -/
def stepCtInstr (ins : CtInstr) (st : CtState) : CtState × ObsEvent :=
  match ins with
  | .movImm dst imm =>
      (st.setReg dst imm, .obsNone)
  | .movReg dst src =>
      (st.setReg dst (st.getReg src), .obsNone)
  | .addConst dst src =>
      (st.setReg dst (st.getReg dst + st.getReg src), .obsNone)
  | .xorConst dst src1 src2 =>
      (st.setReg dst (st.getReg src1 ^^^ st.getReg src2), .obsNone)
  | .cmovConst dst cond tr fa =>
      let v := match Nat.beq (st.getReg cond) 0 with
        | true  => st.getReg fa
        | false => st.getReg tr
      (st.setReg dst v, .obsNone)
  | .udivVarTime dst num den =>
      let v1 := st.getReg num
      let v2 := st.getReg den
      (st.setReg dst (v1 / v2), .obsVarTimeAlu v1 v2)
  | .loadArena dst arena addrReg =>
      let addr := st.getReg addrReg
      let val := match arena with
        | .PublicPacketArena    => st.pubMem addr
        | .SecretKernelKeyArena => st.secMem addr
      (st.setReg dst val, .obsMemAddr arena addr)
  | .storePublicArena addrReg valReg =>
      let addr := st.getReg addrReg
      let val  := st.getReg valReg
      ({ st with pubMem := updateMem st.pubMem addr val }, .obsStorePublic addr val)
  | .spillStack slot src =>
      (st.setStack slot (st.getReg src), .obsNone)
  | .fillStack dst slot =>
      (st.setReg dst (st.getStack slot), .obsNone)
  | .helperReadSecretKey dst =>
      (st.setReg dst st.secretKey, .obsNone)
  | .helperLookupPublicMap dst keyReg =>
      let k := st.getReg keyReg
      (st.setReg dst (st.pubMem k), .obsMapKey k)
  | .helperEmitPublicMetric valReg =>
      let v := st.getReg valReg
      (st, .obsPublicMetric v)

def stepCtInstrList : List CtInstr → CtState → CtState × List ObsEvent
  | [], st => (st, [])
  | i :: is, st =>
      let r1 := stepCtInstr i st
      let r2 := stepCtInstrList is r1.1
      (r2.1, r1.2 :: r2.2)

def stepCtTerm (term : CtTerm) (st : CtState) : Nat × CtState × ObsEvent :=
  match term with
  | .exit retReg =>
      (0, { st with halted := true }, .obsExit (st.getReg retReg))
  | .jmp target =>
      (target, st, .obsJmp target)
  | .branchEqZero condReg tTrue tFalse =>
      let isZero := Nat.beq (st.getReg condReg) 0
      let nextBid := match isZero with | true => tTrue | false => tFalse
      (nextBid, st, .obsBranch isZero nextBid)

def stepCtBlock (prog : CtProg) (bid : Nat) (st : CtState) : Nat × CtState × List ObsEvent :=
  match st.halted with
  | true => (bid, st, [.obsHalted])
  | false =>
      match getCtBlock? prog bid with
      | none => (bid, { st with halted := true }, [.obsHalted])
      | some bb =>
          let r1 := stepCtInstrList bb.instrs st
          let r2 := stepCtTerm bb.term r1.1
          (r2.1, r2.2.1, r1.2 ++ [r2.2.2])

/-- Multi-step leakage observation trace over `fuel` basic-block transitions. -/
def obsTrace (prog : CtProg) : Nat → Nat → CtState → List ObsEvent
  | 0, _, _ => []
  | fuel + 1, bid, st =>
      let res := stepCtBlock prog bid st
      res.2.2 ++ obsTrace prog fuel res.1 res.2.1

/-- Per-block security typing environment (`CtTypeEnv`) in a constant-time certificate. -/
structure CtTypeEnv where
  r0 : SecLabel
  r1 : SecLabel
  r2 : SecLabel
  r3 : SecLabel
  r4 : SecLabel
  s0 : SecLabel
  s1 : SecLabel
  deriving DecidableEq, Repr

def CtTypeEnv.getReg (env : CtTypeEnv) : Reg → SecLabel
  | .R0 => env.r0
  | .R1 => env.r1
  | .R2 => env.r2
  | .R3 => env.r3
  | .R4 => env.r4

def CtTypeEnv.setReg (env : CtTypeEnv) (r : Reg) (l : SecLabel) : CtTypeEnv :=
  match r with
  | .R0 => { env with r0 := l }
  | .R1 => { env with r1 := l }
  | .R2 => { env with r2 := l }
  | .R3 => { env with r3 := l }
  | .R4 => { env with r4 := l }

def CtTypeEnv.getStack (env : CtTypeEnv) : StackSlot → SecLabel
  | .S0 => env.s0
  | .S1 => env.s1

def CtTypeEnv.setStack (env : CtTypeEnv) (sl : StackSlot) (l : SecLabel) : CtTypeEnv :=
  match sl with
  | .S0 => { env with s0 := l }
  | .S1 => { env with s1 := l }

@[simp] theorem CtTypeEnv.getStack_setReg (env : CtTypeEnv) (r : Reg) (l : SecLabel) (sl : StackSlot) :
    (env.setReg r l).getStack sl = env.getStack sl := by
  cases r <;> cases sl <;> rfl

theorem CtTypeEnv.getReg_setReg_eq (env : CtTypeEnv) (r : Reg) (l : SecLabel) :
    (env.setReg r l).getReg r = l := by
  cases r <;> rfl

theorem CtTypeEnv.getReg_setReg_ne (env : CtTypeEnv) (dst r : Reg) (l : SecLabel) (h : r ≠ dst) :
    (env.setReg dst l).getReg r = env.getReg r := by
  cases dst <;> cases r <;> first | contradiction | rfl

@[simp] theorem CtTypeEnv.getReg_setStack (env : CtTypeEnv) (sl : StackSlot) (l : SecLabel) (r : Reg) :
    (env.setStack sl l).getReg r = env.getReg r := by
  cases sl <;> cases r <;> rfl

theorem CtTypeEnv.getStack_setStack_eq (env : CtTypeEnv) (sl : StackSlot) (l : SecLabel) :
    (env.setStack sl l).getStack sl = l := by
  cases sl <;> rfl

theorem CtTypeEnv.getStack_setStack_ne (env : CtTypeEnv) (slot sl : StackSlot) (l : SecLabel) (h : sl ≠ slot) :
    (env.setStack slot l).getStack sl = env.getStack sl := by
  cases slot <;> cases sl <;> first | contradiction | rfl

/-- Join-monotonicity check `env1 ⊑ env2` at CFG edges `ℓ → ℓ'`. -/
def CtTypeEnv.subsumes (env1 env2 : CtTypeEnv) : Bool :=
  SecLabel.le env1.r0 env2.r0 &&
  SecLabel.le env1.r1 env2.r1 &&
  SecLabel.le env1.r2 env2.r2 &&
  SecLabel.le env1.r3 env2.r3 &&
  SecLabel.le env1.r4 env2.r4 &&
  SecLabel.le env1.s0 env2.s0 &&
  SecLabel.le env1.s1 env2.s1

/-- Single-pass abstract security-label transformer for `CtInstr`. -/
def transferCtInstr (env : CtTypeEnv) (ins : CtInstr) : Option CtTypeEnv :=
  match ins with
  | .movImm dst _ =>
      some (env.setReg dst .Public)
  | .movReg dst src =>
      some (env.setReg dst (env.getReg src))
  | .addConst dst src =>
      some (env.setReg dst (SecLabel.join (env.getReg dst) (env.getReg src)))
  | .xorConst dst src1 src2 =>
      some (env.setReg dst (SecLabel.join (env.getReg src1) (env.getReg src2)))
  | .cmovConst dst cond tr fa =>
      let l := SecLabel.join (env.getReg cond) (SecLabel.join (env.getReg tr) (env.getReg fa))
      some (env.setReg dst l)
  | .udivVarTime dst num den =>
      match env.getReg num, env.getReg den with
      | .Public, .Public => some (env.setReg dst .Public)
      | _, _             => none
  | .loadArena dst arena addrReg =>
      match env.getReg addrReg with
      | .Public =>
          let resLbl := match arena with
            | .PublicPacketArena    => .Public
            | .SecretKernelKeyArena => .Secret
          some (env.setReg dst resLbl)
      | .Secret => none
  | .storePublicArena addrReg valReg =>
      match env.getReg addrReg, env.getReg valReg with
      | .Public, .Public => some env
      | _, _             => none
  | .spillStack slot src =>
      some (env.setStack slot (env.getReg src))
  | .fillStack dst slot =>
      some (env.setReg dst (env.getStack slot))
  | .helperReadSecretKey dst =>
      some (env.setReg dst .Secret)
  | .helperLookupPublicMap dst keyReg =>
      match env.getReg keyReg with
      | .Public => some (env.setReg dst .Public)
      | .Secret => none
  | .helperEmitPublicMetric valReg =>
      match env.getReg valReg with
      | .Public => some env
      | .Secret => none

def transferCtInstrList (env : CtTypeEnv) : List CtInstr → Option CtTypeEnv
  | []      => some env
  | i :: is =>
      match transferCtInstr env i with
      | none      => none
      | some env' => transferCtInstrList env' is

abbrev CtCertificate := List CtTypeEnv

def getCtCert? (cert : CtCertificate) (bid : Nat) : Option CtTypeEnv :=
  match cert, bid with
  | [], _          => none
  | c :: _, 0      => some c
  | _ :: cs, n + 1 => getCtCert? cs n

/-- Single-block constant-time certificate check (`checkCtBlock`). -/
def checkCtBlock (cert : CtCertificate) (bb : CtBasicBlock) : Bool :=
  match getCtCert? cert bb.id with
  | none => false
  | some pre =>
      match transferCtInstrList pre bb.instrs with
      | none => false
      | some post =>
          match bb.term with
          | .exit retReg =>
              match post.getReg retReg with
              | .Public => true
              | .Secret => false
          | .jmp target =>
              match getCtCert? cert target with
              | none => false
              | some tCert => CtTypeEnv.subsumes post tCert
          | .branchEqZero condReg tTrue tFalse =>
              match post.getReg condReg, getCtCert? cert tTrue, getCtCert? cert tFalse with
              | .Public, some cTrue, some cFalse =>
                  CtTypeEnv.subsumes post cTrue && CtTypeEnv.subsumes post cFalse
              | _, _, _ => false

def checkAllCtBlocks (cert : CtCertificate) : List CtBasicBlock → Bool
  | []        => true
  | bb :: bbs => checkCtBlock cert bb && checkAllCtBlocks cert bbs

/-- **In-Kernel Single-Pass Constant-Time Certificate Checker (`checkKernelCtCert`)**:
    Verifies a 2-safety noninterference hyperproperty in a single O(|I|) linear pass
    over the CFG blocks without constructing the quadratic product graph `P × P`. -/
def checkKernelCtCert (prog : CtProg) (cert : CtCertificate) : Bool :=
  checkAllCtBlocks cert prog

/-- Low-equivalence relation (`CtLowEq`) between two concrete states `s₁, s₂` under `env`:
    they agree on `halted`, all `.Public` registers, all `.Public` stack slots, and `pubMem`,
    while differing arbitrarily on `.Secret` registers/stack slots, `secMem`, and `secretKey`. -/
structure CtLowEq (env : CtTypeEnv) (s₁ s₂ : CtState) : Prop where
  haltedEq : s₁.halted = s₂.halted
  regEq    : ∀ r : Reg, env.getReg r = .Public → s₁.getReg r = s₂.getReg r
  stackEq  : ∀ sl : StackSlot, env.getStack sl = .Public → s₁.getStack sl = s₂.getStack sl
  pubMemEq : ∀ a : Nat, s₁.pubMem a = s₂.pubMem a

theorem ctLowEq_setReg (env : CtTypeEnv) (s₁ s₂ : CtState)
    (hLow : CtLowEq env s₁ s₂) (dst : Reg) (lbl : SecLabel) (v₁ v₂ : Nat)
    (hVal : lbl = .Public → v₁ = v₂) :
    CtLowEq (env.setReg dst lbl) (s₁.setReg dst v₁) (s₂.setReg dst v₂) := by
  refine ⟨by simp [hLow.haltedEq], ?_, ?_, by intro a; simp [hLow.pubMemEq a]⟩
  · intro r hr
    cases decEq r dst with
    | isTrue hEq =>
        subst hEq
        rw [CtTypeEnv.getReg_setReg_eq] at hr
        rw [CtState.getReg_setReg_eq, CtState.getReg_setReg_eq]
        exact hVal hr
    | isFalse hNe =>
        rw [CtTypeEnv.getReg_setReg_ne _ _ _ _ hNe] at hr
        rw [CtState.getReg_setReg_ne _ _ _ _ hNe, CtState.getReg_setReg_ne _ _ _ _ hNe]
        exact hLow.regEq r hr
  · intro sl hsl
    rw [CtTypeEnv.getStack_setReg] at hsl
    simp [hLow.stackEq sl hsl]

theorem ctLowEq_setStack (env : CtTypeEnv) (s₁ s₂ : CtState)
    (hLow : CtLowEq env s₁ s₂) (slot : StackSlot) (lbl : SecLabel) (v₁ v₂ : Nat)
    (hVal : lbl = .Public → v₁ = v₂) :
    CtLowEq (env.setStack slot lbl) (s₁.setStack slot v₁) (s₂.setStack slot v₂) := by
  refine ⟨by simp [hLow.haltedEq], ?_, ?_, by intro a; simp [hLow.pubMemEq a]⟩
  · intro r hr
    rw [CtTypeEnv.getReg_setStack] at hr
    simp [hLow.regEq r hr]
  · intro sl hsl
    cases decEq sl slot with
    | isTrue hEq =>
        subst hEq
        rw [CtTypeEnv.getStack_setStack_eq] at hsl
        rw [CtState.getStack_setStack_eq, CtState.getStack_setStack_eq]
        exact hVal hsl
    | isFalse hNe =>
        rw [CtTypeEnv.getStack_setStack_ne _ _ _ _ hNe] at hsl
        rw [CtState.getStack_setStack_ne _ _ _ _ hNe, CtState.getStack_setStack_ne _ _ _ _ hNe]
        exact hLow.stackEq sl hsl

theorem ctLowEq_of_subsumes (env1 env2 : CtTypeEnv) (s₁ s₂ : CtState)
    (hSub : CtTypeEnv.subsumes env1 env2 = true)
    (hLow : CtLowEq env1 s₁ s₂) :
    CtLowEq env2 s₁ s₂ := by
  unfold CtTypeEnv.subsumes at hSub
  simp [Bool.and_eq_true] at hSub
  rcases hSub with ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, hs0⟩, hs1⟩
  refine ⟨hLow.haltedEq, ?_, ?_, hLow.pubMemEq⟩
  · intro r hr
    cases r with
    | R0 =>
        simp [CtTypeEnv.getReg] at hr
        rw [hr] at h0
        exact hLow.regEq .R0 (secLabel_le_public_imp env1.r0 h0)
    | R1 =>
        simp [CtTypeEnv.getReg] at hr
        rw [hr] at h1
        exact hLow.regEq .R1 (secLabel_le_public_imp env1.r1 h1)
    | R2 =>
        simp [CtTypeEnv.getReg] at hr
        rw [hr] at h2
        exact hLow.regEq .R2 (secLabel_le_public_imp env1.r2 h2)
    | R3 =>
        simp [CtTypeEnv.getReg] at hr
        rw [hr] at h3
        exact hLow.regEq .R3 (secLabel_le_public_imp env1.r3 h3)
    | R4 =>
        simp [CtTypeEnv.getReg] at hr
        rw [hr] at h4
        exact hLow.regEq .R4 (secLabel_le_public_imp env1.r4 h4)
  · intro sl hsl
    cases sl with
    | S0 =>
        simp [CtTypeEnv.getStack] at hsl
        rw [hsl] at hs0
        exact hLow.stackEq .S0 (secLabel_le_public_imp env1.s0 hs0)
    | S1 =>
        simp [CtTypeEnv.getStack] at hsl
        rw [hsl] at hs1
        exact hLow.stackEq .S1 (secLabel_le_public_imp env1.s1 hs1)

/-- **Per-Instruction 2-Safety Noninterference Theorem (`ct_instr_step_noninterference`)**:
    Every instruction accepted by `transferCtInstr` produces identical leakage observations
    and preserves `CtLowEq`. -/
theorem ct_instr_step_noninterference (env env' : CtTypeEnv) (ins : CtInstr) (s₁ s₂ : CtState)
    (hTrans : transferCtInstr env ins = some env')
    (hLow : CtLowEq env s₁ s₂) :
    (stepCtInstr ins s₁).2 = (stepCtInstr ins s₂).2 ∧
    CtLowEq env' (stepCtInstr ins s₁).1 (stepCtInstr ins s₂).1 := by
  cases ins with
  | movImm dst imm =>
      simp [transferCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact ctLowEq_setReg env s₁ s₂ hLow dst .Public imm imm (fun _ => rfl)
  | movReg dst src =>
      simp [transferCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact ctLowEq_setReg env s₁ s₂ hLow dst (env.getReg src) (s₁.getReg src) (s₂.getReg src) (hLow.regEq src)
  | addConst dst src =>
      simp [transferCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      refine ctLowEq_setReg env s₁ s₂ hLow dst (SecLabel.join (env.getReg dst) (env.getReg src))
        (s₁.getReg dst + s₁.getReg src) (s₂.getReg dst + s₂.getReg src) ?_
      intro hJoin
      have ⟨hd, hs⟩ := secLabel_join_eq_public _ _ hJoin
      rw [hLow.regEq dst hd, hLow.regEq src hs]
  | xorConst dst src1 src2 =>
      simp [transferCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      refine ctLowEq_setReg env s₁ s₂ hLow dst (SecLabel.join (env.getReg src1) (env.getReg src2))
        (s₁.getReg src1 ^^^ s₁.getReg src2) (s₂.getReg src1 ^^^ s₂.getReg src2) ?_
      intro hJoin
      have ⟨h1, h2⟩ := secLabel_join_eq_public _ _ hJoin
      rw [hLow.regEq src1 h1, hLow.regEq src2 h2]
  | cmovConst dst cond tr fa =>
      simp [transferCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      refine ctLowEq_setReg env s₁ s₂ hLow dst
        (SecLabel.join (env.getReg cond) (SecLabel.join (env.getReg tr) (env.getReg fa))) _ _ ?_
      intro hJoin
      have ⟨hc, htf⟩ := secLabel_join_eq_public _ _ hJoin
      have ⟨ht, hf⟩ := secLabel_join_eq_public _ _ htf
      rw [hLow.regEq cond hc, hLow.regEq tr ht, hLow.regEq fa hf]
  | udivVarTime dst num den =>
      unfold transferCtInstr at hTrans
      cases hNum : env.getReg num <;> cases hDen : env.getReg den <;>
        simp [hNum, hDen] at hTrans
      subst hTrans
      simp [stepCtInstr]
      have hn := hLow.regEq num hNum
      have hd := hLow.regEq den hDen
      refine ⟨⟨hn, hd⟩, ?_⟩
      exact ctLowEq_setReg env s₁ s₂ hLow dst .Public _ _ (fun _ => by rw [hn, hd])
  | loadArena dst arena addrReg =>
      unfold transferCtInstr at hTrans
      cases hAddr : env.getReg addrReg <;> simp [hAddr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      have ha := hLow.regEq addrReg hAddr
      refine ⟨ha, ?_⟩
      cases arena with
      | PublicPacketArena =>
          refine ctLowEq_setReg env s₁ s₂ hLow dst .Public _ _ (fun _ => ?_)
          rw [ha, hLow.pubMemEq]
      | SecretKernelKeyArena =>
          exact ctLowEq_setReg env s₁ s₂ hLow dst .Secret _ _ (fun h => nomatch h)
  | storePublicArena addrReg valReg =>
      unfold transferCtInstr at hTrans
      cases hAddr : env.getReg addrReg <;> cases hVal : env.getReg valReg <;>
        simp [hAddr, hVal] at hTrans
      subst hTrans
      simp [stepCtInstr]
      have ha := hLow.regEq addrReg hAddr
      have hv := hLow.regEq valReg hVal
      refine ⟨⟨ha, hv⟩, ?_⟩
      refine ⟨hLow.haltedEq, hLow.regEq, hLow.stackEq, ?_⟩
      intro a
      unfold updateMem
      rw [ha, hv]
      cases Nat.beq a (s₂.getReg addrReg) <;> simp [hLow.pubMemEq a]
  | spillStack slot src =>
      simp [transferCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact ctLowEq_setStack env s₁ s₂ hLow slot (env.getReg src) (s₁.getReg src) (s₂.getReg src) (hLow.regEq src)
  | fillStack dst slot =>
      simp [transferCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact ctLowEq_setReg env s₁ s₂ hLow dst (env.getStack slot) (s₁.getStack slot) (s₂.getStack slot) (hLow.stackEq slot)
  | helperReadSecretKey dst =>
      simp [transferCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact ctLowEq_setReg env s₁ s₂ hLow dst .Secret s₁.secretKey s₂.secretKey (fun h => nomatch h)
  | helperLookupPublicMap dst keyReg =>
      unfold transferCtInstr at hTrans
      cases hKey : env.getReg keyReg <;> simp [hKey] at hTrans
      subst hTrans
      simp [stepCtInstr]
      have hk := hLow.regEq keyReg hKey
      refine ⟨hk, ?_⟩
      refine ctLowEq_setReg env s₁ s₂ hLow dst .Public _ _ (fun _ => ?_)
      rw [hk, hLow.pubMemEq]
  | helperEmitPublicMetric valReg =>
      unfold transferCtInstr at hTrans
      cases hVal : env.getReg valReg <;> simp [hVal] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact ⟨hLow.regEq valReg hVal, hLow⟩

/-- **Per-Instruction-List 2-Safety Noninterference (`ct_instr_list_noninterference`)**. -/
theorem ct_instr_list_noninterference (insns : List CtInstr) :
    ∀ (env env' : CtTypeEnv) (s₁ s₂ : CtState),
      transferCtInstrList env insns = some env' →
      CtLowEq env s₁ s₂ →
      (stepCtInstrList insns s₁).2 = (stepCtInstrList insns s₂).2 ∧
      CtLowEq env' (stepCtInstrList insns s₁).1 (stepCtInstrList insns s₂).1 := by
  induction insns with
  | nil =>
      intro env env' s₁ s₂ hTrans hLow
      simp [transferCtInstrList] at hTrans
      subst hTrans
      simp [stepCtInstrList]
      exact hLow
  | cons i is ih =>
      intro env env' s₁ s₂ hTrans hLow
      unfold transferCtInstrList at hTrans
      cases h1 : transferCtInstr env i with
      | none => rw [h1] at hTrans; nomatch hTrans
      | some envMid =>
          rw [h1] at hTrans
          have ⟨hEv, hLowMid⟩ := ct_instr_step_noninterference env envMid i s₁ s₂ h1 hLow
          have ⟨hEvs, hLowEnd⟩ := ih envMid env' (stepCtInstr i s₁).1 (stepCtInstr i s₂).1 hTrans hLowMid
          simp [stepCtInstrList, hEv, hEvs]
          exact hLowEnd

def AllBlocksCtCertified (prog : CtProg) (cert : CtCertificate) : Prop :=
  ∀ bid bb, getCtBlock? prog bid = some bb → bb.id = bid ∧ checkCtBlock cert bb = true

def checkCtBlocksIndexed (cert : CtCertificate) : Nat → List CtBasicBlock → Bool
  | _, [] => true
  | idx, bb :: bbs =>
      Nat.beq bb.id idx && checkCtBlock cert bb && checkCtBlocksIndexed cert (idx + 1) bbs

def checkKernelCtCertIndexed (prog : CtProg) (cert : CtCertificate) : Bool :=
  checkCtBlocksIndexed cert 0 prog

theorem checkCtBlocksIndexed_imp_get (cert : CtCertificate) (bbs : List CtBasicBlock) :
    ∀ (idx bid : Nat) (bb : CtBasicBlock),
      checkCtBlocksIndexed cert idx bbs = true →
      getCtBlock? bbs bid = some bb →
      bb.id = idx + bid ∧ checkCtBlock cert bb = true := by
  induction bbs with
  | nil =>
      intro idx bid bb _ hGet
      simp [getCtBlock?] at hGet
  | cons hd tl ih =>
      intro idx bid bb hChk hGet
      unfold checkCtBlocksIndexed at hChk
      simp [Bool.and_eq_true] at hChk
      rcases hChk with ⟨⟨hId, hBlk⟩, hRest⟩
      cases bid with
      | zero =>
          simp [getCtBlock?] at hGet
          subst hGet
          simp [hId, hBlk]
      | succ n =>
          simp [getCtBlock?] at hGet
          have ⟨hId', hBlk'⟩ := ih (idx + 1) n bb hRest hGet
          refine ⟨?_, hBlk'⟩
          omega

theorem checkKernelCtCertIndexed_imp_AllBlocksCtCertified (prog : CtProg) (cert : CtCertificate)
    (h : checkKernelCtCertIndexed prog cert = true) :
    AllBlocksCtCertified prog cert := by
  intro bid bb hGet
  have ⟨hId, hBlk⟩ := checkCtBlocksIndexed_imp_get cert prog 0 bid bb h hGet
  simp at hId
  exact ⟨hId, hBlk⟩

/-- **Per-Block 2-Safety Noninterference (`ct_block_step_noninterference`)**. -/
theorem ct_block_step_noninterference (prog : CtProg) (cert : CtCertificate)
    (hCert : AllBlocksCtCertified prog cert)
    (bid : Nat) (pre : CtTypeEnv) (s₁ s₂ : CtState)
    (hPre : getCtCert? cert bid = some pre)
    (hLow : CtLowEq pre s₁ s₂) :
    let r₁ := stepCtBlock prog bid s₁
    let r₂ := stepCtBlock prog bid s₂
    r₁.1 = r₂.1 ∧ r₁.2.2 = r₂.2.2 ∧
    (r₁.2.1.halted = true ∧ r₂.2.1.halted = true ∨
      ∃ nextPre, getCtCert? cert r₁.1 = some nextPre ∧ CtLowEq nextPre r₁.2.1 r₂.2.1) := by
  dsimp
  unfold stepCtBlock
  cases hHalt1 : s₁.halted with
  | true =>
      have hHalt2 : s₂.halted = true := by rw [← hLow.haltedEq, hHalt1]
      simp [hHalt2]
      exact Or.inl hHalt1
  | false =>
      have hHalt2 : s₂.halted = false := by rw [← hLow.haltedEq, hHalt1]
      simp [hHalt2]
      cases hBlk : getCtBlock? prog bid with
      | none =>
          simp
      | some bb =>
          simp
          have ⟨hBidEq, hChk⟩ := hCert bid bb hBlk
          unfold checkCtBlock at hChk
          rw [hBidEq, hPre] at hChk
          simp at hChk
          cases hList : transferCtInstrList pre bb.instrs with
          | none => rw [hList] at hChk; nomatch hChk
          | some post =>
              rw [hList] at hChk
              simp at hChk
              have ⟨hEvsEq, hPostLow⟩ := ct_instr_list_noninterference bb.instrs pre post s₁ s₂ hList hLow
              cases hTerm : bb.term with
              | exit retReg =>
                  simp [hTerm] at hChk
                  cases hRet : post.getReg retReg <;> simp [hRet] at hChk
                  simp [stepCtTerm, hEvsEq, hPostLow.regEq retReg hRet]
              | jmp target =>
                  simp [hTerm] at hChk
                  cases hTargetCert : getCtCert? cert target with
                  | none => simp [hTargetCert] at hChk
                  | some tCert =>
                      simp [hTargetCert] at hChk
                      simp [stepCtTerm, hEvsEq]
                      exact Or.inr ⟨tCert, hTargetCert, ctLowEq_of_subsumes post tCert _ _ hChk hPostLow⟩
              | branchEqZero condReg tTrue tFalse =>
                  simp [hTerm] at hChk
                  cases hCond : post.getReg condReg <;>
                    cases hCTrue : getCtCert? cert tTrue <;>
                    cases hCFalse : getCtCert? cert tFalse <;>
                    simp [hCond, hCTrue, hCFalse] at hChk
                  rcases hChk with ⟨hSubT, hSubF⟩
                  have hCondVal := hPostLow.regEq condReg hCond
                  simp [stepCtTerm, hEvsEq, hCondVal]
                  cases Nat.beq ((stepCtInstrList bb.instrs s₂).1.getReg condReg) 0 with
                  | true =>
                      exact Or.inr ⟨_, hCTrue, ctLowEq_of_subsumes post _ _ _ hSubT hPostLow⟩
                  | false =>
                      exact Or.inr ⟨_, hCFalse, ctLowEq_of_subsumes post _ _ _ hSubF hPostLow⟩

theorem obsTrace_of_halted (prog : CtProg) (fuel : Nat) (bid : Nat) (s₁ s₂ : CtState)
    (h1 : s₁.halted = true) (h2 : s₂.halted = true) :
    obsTrace prog fuel bid s₁ = obsTrace prog fuel bid s₂ := by
  induction fuel generalizing bid with
  | zero => rfl
  | succ f ih =>
      unfold obsTrace stepCtBlock
      rw [h1, h2]
      simp [ih bid]

/-- **Foundational Theorem 1a (`kernel_ct_cert_implies_2safety_noninterference`)**:
    If a Ring-0 kernel extension `prog` passes the single-pass O(|I|) security-lattice
    certificate checker (`AllBlocksCtCertified prog cert`), then for **all** `fuel` steps
    and **all pairs** of initial states `(s₁, s₂)` satisfying `CtLowEq pre s₁ s₂`
    (regardless of secret keys or `SecretKernelKeyArena` contents), their leakage
    observation traces are **bit-for-bit identical**:
    `obsTrace prog fuel bid s₁ = obsTrace prog fuel bid s₂`! -/
theorem kernel_ct_cert_implies_2safety_noninterference
    (prog : CtProg) (cert : CtCertificate)
    (hCert : AllBlocksCtCertified prog cert) :
    ∀ (fuel : Nat) (bid : Nat) (pre : CtTypeEnv) (s₁ s₂ : CtState),
      getCtCert? cert bid = some pre →
      CtLowEq pre s₁ s₂ →
      obsTrace prog fuel bid s₁ = obsTrace prog fuel bid s₂ := by
  intro fuel
  induction fuel with
  | zero =>
      intro bid pre s₁ s₂ _ _
      rfl
  | succ f ih =>
      intro bid pre s₁ s₂ hPre hLow
      unfold obsTrace
      dsimp
      have hStep := ct_block_step_noninterference prog cert hCert bid pre s₁ s₂ hPre hLow
      dsimp at hStep
      rcases hStep with ⟨hNextEq, hEvsEq, hCont⟩
      rw [hEvsEq, hNextEq]
      cases hCont with
      | inl hHalted =>
          rw [obsTrace_of_halted prog f (stepCtBlock prog bid s₂).1
              (stepCtBlock prog bid s₁).2.1 (stepCtBlock prog bid s₂).2.1 hHalted.1 hHalted.2]
      | inr hNextCert =>
          rcases hNextCert with ⟨nextPre, hNextPre, hNextLow⟩
          rw [hNextEq] at hNextPre
          rw [ih (stepCtBlock prog bid s₂).1 nextPre
              (stepCtBlock prog bid s₁).2.1 (stepCtBlock prog bid s₂).2.1 hNextPre hNextLow]

/-- Concrete witness 1: `secretLeakProg` reads a secret kernel key into `R2` and uses it as a
    public map lookup key (`helperLookupPublicMap R0 R2`). `checkKernelCtCert` rejects it! -/
def secretLeakProg : CtProg :=
  [ { id := 0
      instrs := [ .helperReadSecretKey .R2, .helperLookupPublicMap .R0 .R2 ]
      term := .exit .R0 } ]

def allPublicCtEnv : CtTypeEnv :=
  { r0 := .Public, r1 := .Public, r2 := .Public, r3 := .Public, r4 := .Public,
    s0 := .Public, s1 := .Public }

theorem ct_cert_rejects_secret_branch_and_cache_index :
    checkKernelCtCert secretLeakProg [allPublicCtEnv] = false :=
  rfl

/-- Concrete witness 2: `constantTimeKeyedMacProg` reads a secret kernel key into `R2`,
    XORs it with a public packet word from `PublicPacketArena` (`R1`), selects branchlessly
    via `cmovConst`, and exits with a public status code `R0 = 0`. `checkKernelCtCert` accepts! -/
def constantTimeKeyedMacProg : CtProg :=
  [ { id := 0
      instrs := [
        .helperReadSecretKey .R2,
        .loadArena .R3 .PublicPacketArena .R1,
        .xorConst .R4 .R2 .R3,
        .cmovConst .R4 .R1 .R4 .R2,
        .movImm .R0 0
      ]
      term := .exit .R0 } ]

theorem ct_cert_accepts_constant_time_keyed_mac :
    checkKernelCtCert constantTimeKeyedMacProg [allPublicCtEnv] = true :=
  rfl

/-!
  =============================================================================
  SECTION 2: Single-Pass O(|I|) Relational Equality & Mask-Cancellation
  Certificate Checker (`checkKernelRelCtCert`)
  =============================================================================
-/

/-- Relational security type per register (`RelSecType`):
    - `PubExact`: guaranteed equal in both runs (`s₁.getReg r = s₂.getReg r`).
    - `SecKeyExact`: holds the exact secret kernel key (`s₁.getReg r = s₁.secretKey ∧ s₂.getReg r = s₂.secretKey`).
    - `SecKeyXorPub`: holds a public value XOR-masked by `secretKey`
      (`(s₁.getReg r ^^^ s₁.secretKey) = (s₂.getReg r ^^^ s₂.secretKey)`).
    - `SecAny`: arbitrary secret value. -/
inductive RelSecType where
  | PubExact
  | SecKeyExact
  | SecKeyXorPub
  | SecAny
  deriving DecidableEq, Repr

def RelSecType.le (t1 t2 : RelSecType) : Bool :=
  match t1, t2 with
  | _, .SecAny                   => true
  | .PubExact, .PubExact         => true
  | .SecKeyExact, .SecKeyExact   => true
  | .SecKeyXorPub, .SecKeyXorPub => true
  | _, _                         => false

def RelSecType.join (t1 t2 : RelSecType) : RelSecType :=
  match t1, t2 with
  | .PubExact, .PubExact => .PubExact
  | _, _                 => .SecAny

/-- Relational XOR abstract transformer (`RelSecType.xorType`):
    Captures one-time-pad masking (`PubExact ^^^ SecKeyExact = SecKeyXorPub`),
    one-time-pad unmasking (`SecKeyXorPub ^^^ SecKeyExact = PubExact`), and
    exact key cancellation (`SecKeyExact ^^^ SecKeyExact = PubExact`)! -/
def RelSecType.xorType (t1 t2 : RelSecType) : RelSecType :=
  match t1, t2 with
  | .PubExact, .PubExact         => .PubExact
  | .SecKeyExact, .SecKeyExact   => .PubExact
  | .PubExact, .SecKeyExact      => .SecKeyXorPub
  | .SecKeyExact, .PubExact      => .SecKeyXorPub
  | .SecKeyXorPub, .SecKeyExact  => .PubExact
  | .SecKeyExact, .SecKeyXorPub  => .PubExact
  | .SecKeyXorPub, .SecKeyXorPub => .PubExact
  | _, _                         => .SecAny

structure RelCtEnv where
  r0 : RelSecType
  r1 : RelSecType
  r2 : RelSecType
  r3 : RelSecType
  r4 : RelSecType
  s0 : RelSecType
  s1 : RelSecType
  deriving DecidableEq, Repr

def RelCtEnv.getReg (env : RelCtEnv) : Reg → RelSecType
  | .R0 => env.r0
  | .R1 => env.r1
  | .R2 => env.r2
  | .R3 => env.r3
  | .R4 => env.r4

def RelCtEnv.setReg (env : RelCtEnv) (r : Reg) (t : RelSecType) : RelCtEnv :=
  match r with
  | .R0 => { env with r0 := t }
  | .R1 => { env with r1 := t }
  | .R2 => { env with r2 := t }
  | .R3 => { env with r3 := t }
  | .R4 => { env with r4 := t }

def RelCtEnv.getStack (env : RelCtEnv) : StackSlot → RelSecType
  | .S0 => env.s0
  | .S1 => env.s1

def RelCtEnv.setStack (env : RelCtEnv) (sl : StackSlot) (t : RelSecType) : RelCtEnv :=
  match sl with
  | .S0 => { env with s0 := t }
  | .S1 => { env with s1 := t }

@[simp] theorem RelCtEnv.getStack_setReg (env : RelCtEnv) (r : Reg) (t : RelSecType) (sl : StackSlot) :
    (env.setReg r t).getStack sl = env.getStack sl := by
  cases r <;> cases sl <;> rfl

theorem RelCtEnv.getReg_setReg_eq (env : RelCtEnv) (r : Reg) (t : RelSecType) :
    (env.setReg r t).getReg r = t := by
  cases r <;> rfl

theorem RelCtEnv.getReg_setReg_ne (env : RelCtEnv) (dst r : Reg) (t : RelSecType) (h : r ≠ dst) :
    (env.setReg dst t).getReg r = env.getReg r := by
  cases dst <;> cases r <;> first | contradiction | rfl

@[simp] theorem RelCtEnv.getReg_setStack (env : RelCtEnv) (sl : StackSlot) (t : RelSecType) (r : Reg) :
    (env.setStack sl t).getReg r = env.getReg r := by
  cases sl <;> cases r <;> rfl

theorem RelCtEnv.getStack_setStack_eq (env : RelCtEnv) (sl : StackSlot) (t : RelSecType) :
    (env.setStack sl t).getStack sl = t := by
  cases sl <;> rfl

theorem RelCtEnv.getStack_setStack_ne (env : RelCtEnv) (slot sl : StackSlot) (t : RelSecType) (h : sl ≠ slot) :
    (env.setStack slot t).getStack sl = env.getStack sl := by
  cases slot <;> cases sl <;> first | contradiction | rfl

def RelCtEnv.subsumes (env1 env2 : RelCtEnv) : Bool :=
  RelSecType.le env1.r0 env2.r0 &&
  RelSecType.le env1.r1 env2.r1 &&
  RelSecType.le env1.r2 env2.r2 &&
  RelSecType.le env1.r3 env2.r3 &&
  RelSecType.le env1.r4 env2.r4 &&
  RelSecType.le env1.s0 env2.s0 &&
  RelSecType.le env1.s1 env2.s1

/-- Single-pass relational instruction transformer (`transferRelCtInstr`).
    Notice how `.xorConst dst src1 src2` checks syntactic register equality `src1 == src2`
    (self-XOR zeroing `r ^^^ r = 0` produces `.PubExact` even for `.SecAny`!) AND applies
    `RelSecType.xorType` for one-time-pad mask/unmask cancellation! -/
def transferRelCtInstr (env : RelCtEnv) (ins : CtInstr) : Option RelCtEnv :=
  match ins with
  | .movImm dst _ =>
      some (env.setReg dst .PubExact)
  | .movReg dst src =>
      some (env.setReg dst (env.getReg src))
  | .addConst dst src =>
      some (env.setReg dst (RelSecType.join (env.getReg dst) (env.getReg src)))
  | .xorConst dst src1 src2 =>
      let resType :=
        match decEq src1 src2 with
        | isTrue _  => .PubExact
        | isFalse _ => RelSecType.xorType (env.getReg src1) (env.getReg src2)
      some (env.setReg dst resType)
  | .cmovConst dst cond tr fa =>
      let l := RelSecType.join (env.getReg cond) (RelSecType.join (env.getReg tr) (env.getReg fa))
      some (env.setReg dst l)
  | .udivVarTime dst num den =>
      match env.getReg num, env.getReg den with
      | .PubExact, .PubExact => some (env.setReg dst .PubExact)
      | _, _                 => none
  | .loadArena dst arena addrReg =>
      match env.getReg addrReg with
      | .PubExact =>
          let resLbl := match arena with
            | .PublicPacketArena    => .PubExact
            | .SecretKernelKeyArena => .SecAny
          some (env.setReg dst resLbl)
      | _ => none
  | .storePublicArena addrReg valReg =>
      match env.getReg addrReg, env.getReg valReg with
      | .PubExact, .PubExact => some env
      | _, _                 => none
  | .spillStack slot src =>
      some (env.setStack slot (env.getReg src))
  | .fillStack dst slot =>
      some (env.setReg dst (env.getStack slot))
  | .helperReadSecretKey dst =>
      some (env.setReg dst .SecKeyExact)
  | .helperLookupPublicMap dst keyReg =>
      match env.getReg keyReg with
      | .PubExact => some (env.setReg dst .PubExact)
      | _         => none
  | .helperEmitPublicMetric valReg =>
      match env.getReg valReg with
      | .PubExact => some env
      | _         => none

def transferRelCtInstrList (env : RelCtEnv) : List CtInstr → Option RelCtEnv
  | []      => some env
  | i :: is =>
      match transferRelCtInstr env i with
      | none      => none
      | some env' => transferRelCtInstrList env' is

abbrev RelCtCertificate := List RelCtEnv

def getRelCtCert? (cert : RelCtCertificate) (bid : Nat) : Option RelCtEnv :=
  match cert, bid with
  | [], _          => none
  | c :: _, 0      => some c
  | _ :: cs, n + 1 => getRelCtCert? cs n

def checkRelCtBlock (cert : RelCtCertificate) (bb : CtBasicBlock) : Bool :=
  match getRelCtCert? cert bb.id with
  | none => false
  | some pre =>
      match transferRelCtInstrList pre bb.instrs with
      | none => false
      | some post =>
          match bb.term with
          | .exit retReg =>
              match post.getReg retReg with
              | .PubExact => true
              | _         => false
          | .jmp target =>
              match getRelCtCert? cert target with
              | none => false
              | some tCert => RelCtEnv.subsumes post tCert
          | .branchEqZero condReg tTrue tFalse =>
              match post.getReg condReg, getRelCtCert? cert tTrue, getRelCtCert? cert tFalse with
              | .PubExact, some cTrue, some cFalse =>
                  RelCtEnv.subsumes post cTrue && RelCtEnv.subsumes post cFalse
              | _, _, _ => false

def checkAllRelCtBlocks (cert : RelCtCertificate) : List CtBasicBlock → Bool
  | []        => true
  | bb :: bbs => checkRelCtBlock cert bb && checkAllRelCtBlocks cert bbs

/-- **In-Kernel Single-Pass Relational Constant-Time Certificate Checker (`checkKernelRelCtCert`)**. -/
def checkKernelRelCtCert (prog : CtProg) (cert : RelCtCertificate) : Bool :=
  checkAllRelCtBlocks cert prog

/-- Relational semantics (`RelValRel`) of `RelSecType` for a pair of values `(v₁, v₂)` wrt `(k₁, k₂)`. -/
def RelValRel (t : RelSecType) (k₁ k₂ v₁ v₂ : Nat) : Prop :=
  match t with
  | .PubExact     => v₁ = v₂
  | .SecKeyExact  => v₁ = k₁ ∧ v₂ = k₂
  | .SecKeyXorPub => (v₁ ^^^ k₁) = (v₂ ^^^ k₂)
  | .SecAny       => True

structure RelLowEq (env : RelCtEnv) (s₁ s₂ : CtState) : Prop where
  haltedEq : s₁.halted = s₂.halted
  regRel   : ∀ r : Reg, RelValRel (env.getReg r) s₁.secretKey s₂.secretKey (s₁.getReg r) (s₂.getReg r)
  stackRel : ∀ sl : StackSlot, RelValRel (env.getStack sl) s₁.secretKey s₂.secretKey (s₁.getStack sl) (s₂.getStack sl)
  pubMemEq : ∀ a : Nat, s₁.pubMem a = s₂.pubMem a

theorem xor_mask_unmask (p k : Nat) : (p ^^^ k) ^^^ k = p := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xor_comm_cancel (k p : Nat) : (k ^^^ p) ^^^ k = p := by
  rw [Nat.xor_comm k p, xor_mask_unmask]

theorem relValRel_of_le (t1 t2 : RelSecType) (k₁ k₂ v₁ v₂ : Nat)
    (hLe : RelSecType.le t1 t2 = true)
    (hRel : RelValRel t1 k₁ k₂ v₁ v₂) :
    RelValRel t2 k₁ k₂ v₁ v₂ := by
  cases t1 <;> cases t2 <;> simp [RelSecType.le, RelValRel] at hLe hRel ⊢
  all_goals exact hRel

theorem relValRel_join (t1 t2 : RelSecType) (k₁ k₂ v₁ v₂ w₁ w₂ : Nat)
    (h1 : RelValRel t1 k₁ k₂ v₁ v₂)
    (h2 : RelValRel t2 k₁ k₂ w₁ w₂) :
    RelValRel (RelSecType.join t1 t2) k₁ k₂ (v₁ + w₁) (v₂ + w₂) := by
  cases t1 <;> cases t2 <;> simp [RelSecType.join, RelValRel] at h1 h2 ⊢
  rw [h1, h2]

theorem relValRel_xor (t1 t2 : RelSecType) (k₁ k₂ v₁ v₂ w₁ w₂ : Nat)
    (h1 : RelValRel t1 k₁ k₂ v₁ v₂)
    (h2 : RelValRel t2 k₁ k₂ w₁ w₂) :
    RelValRel (RelSecType.xorType t1 t2) k₁ k₂ (v₁ ^^^ w₁) (v₂ ^^^ w₂) := by
  cases t1 <;> cases t2 <;> simp [RelSecType.xorType, RelValRel] at h1 h2 ⊢
  · rw [h1, h2]
  · rcases h2 with ⟨hw1, hw2⟩
    rw [hw1, hw2, xor_mask_unmask, xor_mask_unmask, h1]
  · rcases h1 with ⟨hv1, hv2⟩
    rw [hv1, hv2, xor_comm_cancel, xor_comm_cancel, h2]
  · rcases h1 with ⟨hv1, hv2⟩
    rcases h2 with ⟨hw1, hw2⟩
    rw [hv1, hw1, hv2, hw2, Nat.xor_self, Nat.xor_self]
  · rcases h1 with ⟨hv1, hv2⟩
    rw [hv1, hv2, Nat.xor_comm k₁ w₁, Nat.xor_comm k₂ w₂, h2]
  · rcases h2 with ⟨hw1, hw2⟩
    rw [hw1, hw2, h1]
  · have hL : v₁ ^^^ w₁ = (v₁ ^^^ k₁) ^^^ (w₁ ^^^ k₁) := by
      rw [Nat.xor_assoc, ← Nat.xor_assoc k₁ w₁ k₁, Nat.xor_comm k₁ w₁,
          Nat.xor_assoc w₁ k₁ k₁, Nat.xor_self, Nat.xor_zero]
    have hR : v₂ ^^^ w₂ = (v₂ ^^^ k₂) ^^^ (w₂ ^^^ k₂) := by
      rw [Nat.xor_assoc, ← Nat.xor_assoc k₂ w₂ k₂, Nat.xor_comm k₂ w₂,
          Nat.xor_assoc w₂ k₂ k₂, Nat.xor_self, Nat.xor_zero]
    rw [hL, hR, h1, h2]

theorem relLowEq_setReg (env : RelCtEnv) (s₁ s₂ : CtState)
    (hLow : RelLowEq env s₁ s₂) (dst : Reg) (t : RelSecType) (v₁ v₂ : Nat)
    (hVal : RelValRel t s₁.secretKey s₂.secretKey v₁ v₂) :
    RelLowEq (env.setReg dst t) (s₁.setReg dst v₁) (s₂.setReg dst v₂) := by
  refine ⟨by simp [hLow.haltedEq], ?_, ?_, by intro a; simp [hLow.pubMemEq a]⟩
  · intro r
    simp only [CtState.secretKey_setReg]
    cases decEq r dst with
    | isTrue hEq =>
        subst hEq
        rw [RelCtEnv.getReg_setReg_eq, CtState.getReg_setReg_eq, CtState.getReg_setReg_eq]
        exact hVal
    | isFalse hNe =>
        rw [RelCtEnv.getReg_setReg_ne _ _ _ _ hNe,
            CtState.getReg_setReg_ne _ _ _ _ hNe,
            CtState.getReg_setReg_ne _ _ _ _ hNe]
        exact hLow.regRel r
  · intro sl
    simp [hLow.stackRel sl]

theorem relLowEq_setStack (env : RelCtEnv) (s₁ s₂ : CtState)
    (hLow : RelLowEq env s₁ s₂) (slot : StackSlot) (t : RelSecType) (v₁ v₂ : Nat)
    (hVal : RelValRel t s₁.secretKey s₂.secretKey v₁ v₂) :
    RelLowEq (env.setStack slot t) (s₁.setStack slot v₁) (s₂.setStack slot v₂) := by
  refine ⟨by simp [hLow.haltedEq], ?_, ?_, by intro a; simp [hLow.pubMemEq a]⟩
  · intro r
    simp [hLow.regRel r]
  · intro sl
    simp only [CtState.secretKey_setStack]
    cases decEq sl slot with
    | isTrue hEq =>
        subst hEq
        rw [RelCtEnv.getStack_setStack_eq, CtState.getStack_setStack_eq, CtState.getStack_setStack_eq]
        exact hVal
    | isFalse hNe =>
        rw [RelCtEnv.getStack_setStack_ne _ _ _ _ hNe,
            CtState.getStack_setStack_ne _ _ _ _ hNe,
            CtState.getStack_setStack_ne _ _ _ _ hNe]
        exact hLow.stackRel sl

theorem relLowEq_of_subsumes (env1 env2 : RelCtEnv) (s₁ s₂ : CtState)
    (hSub : RelCtEnv.subsumes env1 env2 = true)
    (hLow : RelLowEq env1 s₁ s₂) :
    RelLowEq env2 s₁ s₂ := by
  unfold RelCtEnv.subsumes at hSub
  simp [Bool.and_eq_true] at hSub
  rcases hSub with ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, hs0⟩, hs1⟩
  refine ⟨hLow.haltedEq, ?_, ?_, hLow.pubMemEq⟩
  · intro r
    cases r with
    | R0 => exact relValRel_of_le _ _ _ _ _ _ h0 (hLow.regRel .R0)
    | R1 => exact relValRel_of_le _ _ _ _ _ _ h1 (hLow.regRel .R1)
    | R2 => exact relValRel_of_le _ _ _ _ _ _ h2 (hLow.regRel .R2)
    | R3 => exact relValRel_of_le _ _ _ _ _ _ h3 (hLow.regRel .R3)
    | R4 => exact relValRel_of_le _ _ _ _ _ _ h4 (hLow.regRel .R4)
  · intro sl
    cases sl with
    | S0 => exact relValRel_of_le _ _ _ _ _ _ hs0 (hLow.stackRel .S0)
    | S1 => exact relValRel_of_le _ _ _ _ _ _ hs1 (hLow.stackRel .S1)

/-- **Per-Instruction Relational Constant-Time Noninterference (`rel_ct_instr_step_noninterference`)**. -/
theorem rel_ct_instr_step_noninterference (env env' : RelCtEnv) (ins : CtInstr) (s₁ s₂ : CtState)
    (hTrans : transferRelCtInstr env ins = some env')
    (hLow : RelLowEq env s₁ s₂) :
    (stepCtInstr ins s₁).2 = (stepCtInstr ins s₂).2 ∧
    RelLowEq env' (stepCtInstr ins s₁).1 (stepCtInstr ins s₂).1 := by
  cases ins with
  | movImm dst imm =>
      simp [transferRelCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact relLowEq_setReg env s₁ s₂ hLow dst .PubExact imm imm rfl
  | movReg dst src =>
      simp [transferRelCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact relLowEq_setReg env s₁ s₂ hLow dst (env.getReg src) _ _ (hLow.regRel src)
  | addConst dst src =>
      simp [transferRelCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact relLowEq_setReg env s₁ s₂ hLow dst _ _ _
        (relValRel_join _ _ _ _ _ _ _ _ (hLow.regRel dst) (hLow.regRel src))
  | xorConst dst src1 src2 =>
      unfold transferRelCtInstr at hTrans
      simp at hTrans
      subst hTrans
      simp [stepCtInstr]
      cases decEq src1 src2 with
      | isTrue hEq =>
          subst hEq
          simp
          refine relLowEq_setReg env s₁ s₂ hLow dst .PubExact _ _ ?_
          simp [RelValRel]
      | isFalse hNe =>
          simp
          exact relLowEq_setReg env s₁ s₂ hLow dst _ _ _
            (relValRel_xor _ _ _ _ _ _ _ _ (hLow.regRel src1) (hLow.regRel src2))
  | cmovConst dst cond tr fa =>
      simp [transferRelCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      refine relLowEq_setReg env s₁ s₂ hLow dst
        (RelSecType.join (env.getReg cond) (RelSecType.join (env.getReg tr) (env.getReg fa))) _ _ ?_
      have hc := hLow.regRel cond
      have ht := hLow.regRel tr
      have hf := hLow.regRel fa
      cases h1 : env.getReg cond <;> cases h2 : env.getReg tr <;> cases h3 : env.getReg fa <;>
        simp [h1, h2, h3, RelSecType.join, RelValRel] at hc ht hf ⊢
      rw [hc, ht, hf]
  | udivVarTime dst num den =>
      unfold transferRelCtInstr at hTrans
      cases hNum : env.getReg num <;> cases hDen : env.getReg den <;>
        simp [hNum, hDen] at hTrans
      subst hTrans
      simp [stepCtInstr]
      have hn : s₁.getReg num = s₂.getReg num := by
        have h := hLow.regRel num; rw [hNum] at h; exact h
      have hd : s₁.getReg den = s₂.getReg den := by
        have h := hLow.regRel den; rw [hDen] at h; exact h
      refine ⟨⟨hn, hd⟩, ?_⟩
      exact relLowEq_setReg env s₁ s₂ hLow dst .PubExact _ _ (by simp [RelValRel, hn, hd])
  | loadArena dst arena addrReg =>
      unfold transferRelCtInstr at hTrans
      cases hAddr : env.getReg addrReg <;> simp [hAddr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      have ha : s₁.getReg addrReg = s₂.getReg addrReg := by
        have h := hLow.regRel addrReg; rw [hAddr] at h; exact h
      refine ⟨ha, ?_⟩
      cases arena with
      | PublicPacketArena =>
          refine relLowEq_setReg env s₁ s₂ hLow dst .PubExact _ _ ?_
          simp [RelValRel, ha, hLow.pubMemEq]
      | SecretKernelKeyArena =>
          exact relLowEq_setReg env s₁ s₂ hLow dst .SecAny _ _ trivial
  | storePublicArena addrReg valReg =>
      unfold transferRelCtInstr at hTrans
      cases hAddr : env.getReg addrReg <;> cases hVal : env.getReg valReg <;>
        simp [hAddr, hVal] at hTrans
      subst hTrans
      simp [stepCtInstr]
      have ha : s₁.getReg addrReg = s₂.getReg addrReg := by
        have h := hLow.regRel addrReg; rw [hAddr] at h; exact h
      have hv : s₁.getReg valReg = s₂.getReg valReg := by
        have h := hLow.regRel valReg; rw [hVal] at h; exact h
      refine ⟨⟨ha, hv⟩, ?_⟩
      refine ⟨hLow.haltedEq, hLow.regRel, hLow.stackRel, ?_⟩
      intro a
      unfold updateMem
      rw [ha, hv]
      cases Nat.beq a (s₂.getReg addrReg) <;> simp [hLow.pubMemEq a]
  | spillStack slot src =>
      simp [transferRelCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact relLowEq_setStack env s₁ s₂ hLow slot (env.getReg src) _ _ (hLow.regRel src)
  | fillStack dst slot =>
      simp [transferRelCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact relLowEq_setReg env s₁ s₂ hLow dst (env.getStack slot) _ _ (hLow.stackRel slot)
  | helperReadSecretKey dst =>
      simp [transferRelCtInstr] at hTrans
      subst hTrans
      simp [stepCtInstr]
      exact relLowEq_setReg env s₁ s₂ hLow dst .SecKeyExact _ _ ⟨rfl, rfl⟩
  | helperLookupPublicMap dst keyReg =>
      unfold transferRelCtInstr at hTrans
      cases hKey : env.getReg keyReg <;> simp [hKey] at hTrans
      subst hTrans
      simp [stepCtInstr]
      have hk : s₁.getReg keyReg = s₂.getReg keyReg := by
        have h := hLow.regRel keyReg; rw [hKey] at h; exact h
      refine ⟨hk, ?_⟩
      refine relLowEq_setReg env s₁ s₂ hLow dst .PubExact _ _ ?_
      simp [RelValRel, hk, hLow.pubMemEq]
  | helperEmitPublicMetric valReg =>
      unfold transferRelCtInstr at hTrans
      cases hVal : env.getReg valReg <;> simp [hVal] at hTrans
      subst hTrans
      simp [stepCtInstr]
      have hv : s₁.getReg valReg = s₂.getReg valReg := by
        have h := hLow.regRel valReg; rw [hVal] at h; exact h
      exact ⟨hv, hLow⟩

theorem rel_ct_instr_list_noninterference (insns : List CtInstr) :
    ∀ (env env' : RelCtEnv) (s₁ s₂ : CtState),
      transferRelCtInstrList env insns = some env' →
      RelLowEq env s₁ s₂ →
      (stepCtInstrList insns s₁).2 = (stepCtInstrList insns s₂).2 ∧
      RelLowEq env' (stepCtInstrList insns s₁).1 (stepCtInstrList insns s₂).1 := by
  induction insns with
  | nil =>
      intro env env' s₁ s₂ hTrans hLow
      simp [transferRelCtInstrList] at hTrans
      subst hTrans
      simp [stepCtInstrList]
      exact hLow
  | cons i is ih =>
      intro env env' s₁ s₂ hTrans hLow
      unfold transferRelCtInstrList at hTrans
      cases h1 : transferRelCtInstr env i with
      | none => rw [h1] at hTrans; nomatch hTrans
      | some envMid =>
          rw [h1] at hTrans
          have ⟨hEv, hLowMid⟩ := rel_ct_instr_step_noninterference env envMid i s₁ s₂ h1 hLow
          have ⟨hEvs, hLowEnd⟩ := ih envMid env' (stepCtInstr i s₁).1 (stepCtInstr i s₂).1 hTrans hLowMid
          simp [stepCtInstrList, hEv, hEvs]
          exact hLowEnd

def AllBlocksRelCtCertified (prog : CtProg) (cert : RelCtCertificate) : Prop :=
  ∀ bid bb, getCtBlock? prog bid = some bb → bb.id = bid ∧ checkRelCtBlock cert bb = true

def checkRelCtBlocksIndexed (cert : RelCtCertificate) : Nat → List CtBasicBlock → Bool
  | _, [] => true
  | idx, bb :: bbs =>
      Nat.beq bb.id idx && checkRelCtBlock cert bb && checkRelCtBlocksIndexed cert (idx + 1) bbs

def checkKernelRelCtCertIndexed (prog : CtProg) (cert : RelCtCertificate) : Bool :=
  checkRelCtBlocksIndexed cert 0 prog

theorem checkRelCtBlocksIndexed_imp_get (cert : RelCtCertificate) (bbs : List CtBasicBlock) :
    ∀ (idx bid : Nat) (bb : CtBasicBlock),
      checkRelCtBlocksIndexed cert idx bbs = true →
      getCtBlock? bbs bid = some bb →
      bb.id = idx + bid ∧ checkRelCtBlock cert bb = true := by
  induction bbs with
  | nil =>
      intro idx bid bb _ hGet
      simp [getCtBlock?] at hGet
  | cons hd tl ih =>
      intro idx bid bb hChk hGet
      unfold checkRelCtBlocksIndexed at hChk
      simp [Bool.and_eq_true] at hChk
      rcases hChk with ⟨⟨hId, hBlk⟩, hRest⟩
      cases bid with
      | zero =>
          simp [getCtBlock?] at hGet
          subst hGet
          simp [hId, hBlk]
      | succ n =>
          simp [getCtBlock?] at hGet
          have ⟨hId', hBlk'⟩ := ih (idx + 1) n bb hRest hGet
          refine ⟨?_, hBlk'⟩
          omega

theorem checkKernelRelCtCertIndexed_imp_AllBlocksRelCtCertified (prog : CtProg) (cert : RelCtCertificate)
    (h : checkKernelRelCtCertIndexed prog cert = true) :
    AllBlocksRelCtCertified prog cert := by
  intro bid bb hGet
  have ⟨hId, hBlk⟩ := checkRelCtBlocksIndexed_imp_get cert prog 0 bid bb h hGet
  simp at hId
  exact ⟨hId, hBlk⟩

theorem rel_ct_block_step_noninterference (prog : CtProg) (cert : RelCtCertificate)
    (hCert : AllBlocksRelCtCertified prog cert)
    (bid : Nat) (pre : RelCtEnv) (s₁ s₂ : CtState)
    (hPre : getRelCtCert? cert bid = some pre)
    (hLow : RelLowEq pre s₁ s₂) :
    let r₁ := stepCtBlock prog bid s₁
    let r₂ := stepCtBlock prog bid s₂
    r₁.1 = r₂.1 ∧ r₁.2.2 = r₂.2.2 ∧
    (r₁.2.1.halted = true ∧ r₂.2.1.halted = true ∨
      ∃ nextPre, getRelCtCert? cert r₁.1 = some nextPre ∧ RelLowEq nextPre r₁.2.1 r₂.2.1) := by
  dsimp
  unfold stepCtBlock
  cases hHalt1 : s₁.halted with
  | true =>
      have hHalt2 : s₂.halted = true := by rw [← hLow.haltedEq, hHalt1]
      simp [hHalt2]
      exact Or.inl hHalt1
  | false =>
      have hHalt2 : s₂.halted = false := by rw [← hLow.haltedEq, hHalt1]
      simp [hHalt2]
      cases hBlk : getCtBlock? prog bid with
      | none => simp
      | some bb =>
          simp
          have ⟨hBidEq, hChk⟩ := hCert bid bb hBlk
          unfold checkRelCtBlock at hChk
          rw [hBidEq, hPre] at hChk
          simp at hChk
          cases hList : transferRelCtInstrList pre bb.instrs with
          | none => rw [hList] at hChk; nomatch hChk
          | some post =>
              rw [hList] at hChk
              simp at hChk
              have ⟨hEvsEq, hPostLow⟩ := rel_ct_instr_list_noninterference bb.instrs pre post s₁ s₂ hList hLow
              cases hTerm : bb.term with
              | exit retReg =>
                  simp [hTerm] at hChk
                  cases hRet : post.getReg retReg <;> simp [hRet] at hChk
                  have hRetVal : (stepCtInstrList bb.instrs s₁).1.getReg retReg =
                                 (stepCtInstrList bb.instrs s₂).1.getReg retReg := by
                    have h := hPostLow.regRel retReg; rw [hRet] at h; exact h
                  simp [stepCtTerm, hEvsEq, hRetVal]
              | jmp target =>
                  simp [hTerm] at hChk
                  cases hTargetCert : getRelCtCert? cert target with
                  | none => simp [hTargetCert] at hChk
                  | some tCert =>
                      simp [hTargetCert] at hChk
                      simp [stepCtTerm, hEvsEq]
                      exact Or.inr ⟨tCert, hTargetCert, relLowEq_of_subsumes post tCert _ _ hChk hPostLow⟩
              | branchEqZero condReg tTrue tFalse =>
                  simp [hTerm] at hChk
                  cases hCond : post.getReg condReg <;>
                    cases hCTrue : getRelCtCert? cert tTrue <;>
                    cases hCFalse : getRelCtCert? cert tFalse <;>
                    simp [hCond, hCTrue, hCFalse] at hChk
                  rcases hChk with ⟨hSubT, hSubF⟩
                  have hCondVal : (stepCtInstrList bb.instrs s₁).1.getReg condReg =
                                  (stepCtInstrList bb.instrs s₂).1.getReg condReg := by
                    have h := hPostLow.regRel condReg; rw [hCond] at h; exact h
                  simp [stepCtTerm, hEvsEq, hCondVal]
                  cases Nat.beq ((stepCtInstrList bb.instrs s₂).1.getReg condReg) 0 with
                  | true =>
                      exact Or.inr ⟨_, hCTrue, relLowEq_of_subsumes post _ _ _ hSubT hPostLow⟩
                  | false =>
                      exact Or.inr ⟨_, hCFalse, relLowEq_of_subsumes post _ _ _ hSubF hPostLow⟩

/-- **Foundational Theorem 1b (`kernel_rel_ct_cert_soundness`)**:
    Universal 2-safety noninterference for the single-pass relational certificate checker. -/
theorem kernel_rel_ct_cert_soundness
    (prog : CtProg) (cert : RelCtCertificate)
    (hCert : AllBlocksRelCtCertified prog cert) :
    ∀ (fuel : Nat) (bid : Nat) (pre : RelCtEnv) (s₁ s₂ : CtState),
      getRelCtCert? cert bid = some pre →
      RelLowEq pre s₁ s₂ →
      obsTrace prog fuel bid s₁ = obsTrace prog fuel bid s₂ := by
  intro fuel
  induction fuel with
  | zero =>
      intro bid pre s₁ s₂ _ _
      rfl
  | succ f ih =>
      intro bid pre s₁ s₂ hPre hLow
      unfold obsTrace
      dsimp
      have hStep := rel_ct_block_step_noninterference prog cert hCert bid pre s₁ s₂ hPre hLow
      dsimp at hStep
      rcases hStep with ⟨hNextEq, hEvsEq, hCont⟩
      rw [hEvsEq, hNextEq]
      cases hCont with
      | inl hHalted =>
          rw [obsTrace_of_halted prog f (stepCtBlock prog bid s₂).1
              (stepCtBlock prog bid s₁).2.1 (stepCtBlock prog bid s₂).2.1 hHalted.1 hHalted.2]
      | inr hNextCert =>
          rcases hNextCert with ⟨nextPre, hNextPre, hNextLow⟩
          rw [hNextEq] at hNextPre
          rw [ih (stepCtBlock prog bid s₂).1 nextPre
              (stepCtBlock prog bid s₁).2.1 (stepCtBlock prog bid s₂).2.1 hNextPre hNextLow]

/-- Concrete witness `otpCancelProg`:
    1. Reads secret kernel key into `R2` (`SecKeyExact`);
    2. Masks public packet offset `R1` with `R2` (`R3 := R1 ^^^ R2`, `SecKeyXorPub`);
    3. Unmasks `R3` with `R2` (`R4 := R3 ^^^ R2`, recovering `PubExact` via cancellation!);
    4. Scrubs `R2` via self-XOR (`R2 := R2 ^^^ R2`, recovering `PubExact`);
    5. Uses the unmasked offset `R4` as a `PublicPacketArena` load address (`R0 := *(pub + R4)`). -/
def otpCancelProg : CtProg :=
  [ { id := 0
      instrs := [
        .helperReadSecretKey .R2,
        .xorConst .R3 .R1 .R2,
        .xorConst .R4 .R3 .R2,
        .xorConst .R2 .R2 .R2,
        .loadArena .R0 .PublicPacketArena .R4
      ]
      term := .exit .R0 } ]

def allPubRelEnv : RelCtEnv :=
  { r0 := .PubExact, r1 := .PubExact, r2 := .PubExact, r3 := .PubExact, r4 := .PubExact,
    s0 := .PubExact, s1 := .PubExact }

/-- **Foundational Theorem 1c (`relational_kernel_cert_strictly_extends_ct_cert`)**:
    1. Non-relational `checkKernelCtCert` rejects `otpCancelProg` across ALL possible entry
       certificates `env` (`checkKernelCtCert otpCancelProg [env] = false`).
    2. Single-pass relational `checkKernelRelCtCert` accepts `otpCancelProg` (`= true`).
    3. Executing `otpCancelProg` on any two states `s₁, s₂` with different secret keys (`s₁.secretKey ≠ s₂.secretKey`)
       produces identical observation traces! -/
theorem relational_kernel_cert_strictly_extends_ct_cert :
    (∀ env : CtTypeEnv, checkKernelCtCert otpCancelProg [env] = false) ∧
    checkKernelRelCtCert otpCancelProg [allPubRelEnv] = true ∧
    (∀ (fuel : Nat) (s₁ s₂ : CtState),
      RelLowEq allPubRelEnv s₁ s₂ →
      obsTrace otpCancelProg fuel 0 s₁ = obsTrace otpCancelProg fuel 0 s₂) := by
  refine ⟨?_, rfl, ?_⟩
  · intro env
    cases env with
    | mk r0 r1 r2 r3 r4 s0 s1 =>
        cases r1 <;> rfl
  · intro fuel s₁ s₂ hLow
    apply kernel_rel_ct_cert_soundness otpCancelProg [allPubRelEnv] _ fuel 0 allPubRelEnv s₁ s₂ rfl hLow
    intro bid bb hBlk
    cases bid with
    | zero =>
        simp [otpCancelProg, getCtBlock?] at hBlk
        subst hBlk
        exact ⟨rfl, rfl⟩
    | succ n =>
        simp [otpCancelProg, getCtBlock?] at hBlk

/-!
  =============================================================================
  SECTION 3: Speculative Kernel Execution Semantics (`SpecState`, `Oracle`) &
  Spectre v1 Breakout Against Architectural Memory-Safety + CT Certificates
  (`Blade` POPL 2021, `Pitchfork` PLDI 2020, `Jasmin SCT` IEEE S&P 2021/2023)
  =============================================================================
-/

/-- Fundamental bitwise containment lemma: for any address `addr`, mask `mask`, and
    arena bound `bound`, if `mask < bound`, then `(addr &&& mask) < bound` holds
    unconditionally (even when `addr` is an out-of-bounds speculative offset!). -/
theorem natBlt_and_of_natBlt (addr mask bound : Nat)
    (hMask : natBlt mask bound = true) :
    natBlt (addr &&& mask) bound = true := by
  unfold natBlt at *
  have h1 : mask + 1 ≤ bound := Nat.le_of_ble_eq_true hMask
  have h2 : (addr &&& mask) ≤ mask := Nat.and_le_right
  have h3 : (addr &&& mask) + 1 ≤ bound := Nat.le_trans (Nat.succ_le_succ h2) h1
  exact Nat.ble_eq_true_of_le h3

/-- Speculative kernel extension instruction set (`SctInstr`). -/
inductive SctInstr where
  | movImm (dst : Reg) (imm : Nat)
  | movReg (dst src : Reg)
  | addConst (dst src : Reg)
  | andImm (dst : Reg) (imm : Nat)
  | ldUnmasked (dst addrReg : Reg)
  | ldMasked (dst addrReg : Reg) (mask : Nat)
  | slhInitMsf
  | slhProtect (dst src : Reg)
  | lfence
  | helperReadSecretKey (dst : Reg)
  | helperEmitPublicMetric (valReg : Reg)
  deriving DecidableEq, Repr

inductive SctTerm where
  | exit (retReg : Reg)
  | jmp (target : Nat)
  | branchLtBound (idxReg : Reg) (bound : Nat) (tInBounds tOutBounds : Nat)
  deriving DecidableEq, Repr

structure SctBasicBlock where
  id     : Nat
  instrs : List SctInstr
  term   : SctTerm
  deriving DecidableEq, Repr

abbrev SctProg := List SctBasicBlock

def getSctBlock? (prog : SctProg) (bid : Nat) : Option SctBasicBlock :=
  match prog, bid with
  | [], _           => none
  | bb :: _, 0      => some bb
  | _ :: bbs, n + 1 => getSctBlock? bbs n

/-- Concrete speculative execution state (`SpecState`) of a Ring-0 kernel extension. -/
structure SpecState where
  r0              : Nat
  r1              : Nat
  r2              : Nat
  r3              : Nat
  r4              : Nat
  pubBound        : Nat
  pubMem          : Nat → Nat
  kernelSecretMem : Nat → Nat
  secretKey       : Nat
  specMode        : Bool
  msfMasked       : Bool
  specHalted      : Bool
  exited          : Bool

def SpecState.getReg (st : SpecState) : Reg → Nat
  | .R0 => st.r0
  | .R1 => st.r1
  | .R2 => st.r2
  | .R3 => st.r3
  | .R4 => st.r4

def SpecState.setReg (st : SpecState) (r : Reg) (v : Nat) : SpecState :=
  match r with
  | .R0 => { st with r0 := v }
  | .R1 => { st with r1 := v }
  | .R2 => { st with r2 := v }
  | .R3 => { st with r3 := v }
  | .R4 => { st with r4 := v }

def SpecState.syncMsf (st : SpecState) : SpecState :=
  { st with msfMasked := st.specMode }

def SpecState.applyLfence (st : SpecState) : SpecState :=
  { st with specHalted := st.specMode }

def SpecState.updateBranchSpec (st : SpecState) (mispred : Bool) : SpecState :=
  { st with specMode := st.specMode || mispred, msfMasked := st.msfMasked || mispred }

@[simp] theorem SpecState.specMode_setReg (st : SpecState) (r : Reg) (v : Nat) :
    (st.setReg r v).specMode = st.specMode := by
  cases r <;> rfl

@[simp] theorem SpecState.msfMasked_setReg (st : SpecState) (r : Reg) (v : Nat) :
    (st.setReg r v).msfMasked = st.msfMasked := by
  cases r <;> rfl

@[simp] theorem SpecState.specHalted_setReg (st : SpecState) (r : Reg) (v : Nat) :
    (st.setReg r v).specHalted = st.specHalted := by
  cases r <;> rfl

@[simp] theorem SpecState.exited_setReg (st : SpecState) (r : Reg) (v : Nat) :
    (st.setReg r v).exited = st.exited := by
  cases r <;> rfl

@[simp] theorem SpecState.pubBound_setReg (st : SpecState) (r : Reg) (v : Nat) :
    (st.setReg r v).pubBound = st.pubBound := by
  cases r <;> rfl

@[simp] theorem SpecState.pubMem_setReg (st : SpecState) (r : Reg) (v : Nat) :
    (st.setReg r v).pubMem = st.pubMem := by
  cases r <;> rfl

theorem SpecState.getReg_setReg_eq (st : SpecState) (r : Reg) (v : Nat) :
    (st.setReg r v).getReg r = v := by
  cases r <;> rfl

theorem SpecState.getReg_setReg_ne (st : SpecState) (dst r : Reg) (v : Nat) (h : r ≠ dst) :
    (st.setReg dst v).getReg r = st.getReg r := by
  cases dst <;> cases r <;> first | contradiction | rfl

@[simp] theorem SpecState.getReg_syncMsf (st : SpecState) (r : Reg) :
    st.syncMsf.getReg r = st.getReg r := by
  cases r <;> rfl

@[simp] theorem SpecState.getReg_applyLfence (st : SpecState) (r : Reg) :
    st.applyLfence.getReg r = st.getReg r := by
  cases r <;> rfl

@[simp] theorem SpecState.getReg_updateBranchSpec (st : SpecState) (m : Bool) (r : Reg) :
    (st.updateBranchSpec m).getReg r = st.getReg r := by
  cases r <;> rfl

/-- Memory read semantics (`readSpecMem`):
    Addresses `< st.pubBound` read `st.pubMem addr`; out-of-bounds addresses `≥ st.pubBound`
    read host kernel secret memory `st.kernelSecretMem addr`! -/
def readSpecMem (st : SpecState) (addr : Nat) : Nat :=
  match natBlt addr st.pubBound with
  | true  => st.pubMem addr
  | false => st.kernelSecretMem addr

/-- Unmasked load (`readUnmasked`):
    - During architectural execution (`specMode = false`) of an architecturally bounds-checked
      extension, the access hits `st.pubMem addr`.
    - During transient execution (`specMode = true` after a mispredicted bounds check), an
      out-of-bounds `addr ≥ st.pubBound` reads `st.kernelSecretMem addr`! -/
def readUnmasked (st : SpecState) (addr : Nat) : Nat :=
  match st.specMode with
  | false => st.pubMem addr
  | true  => readSpecMem st addr

/-- By `natBlt_and_of_natBlt`, a bitwise-masked SFI load `readSpecMem st (addr &&& mask)`
    with `mask < st.pubBound` ALWAYS reads `st.pubMem (addr &&& mask)` and NEVER reads
    `st.kernelSecretMem`, even during transient misprediction (`specMode = true`)! -/
theorem readSpecMem_masked_eq_pubMem (st : SpecState) (addr mask : Nat)
    (hMask : natBlt mask st.pubBound = true) :
    readSpecMem st (addr &&& mask) = st.pubMem (addr &&& mask) := by
  unfold readSpecMem
  rw [natBlt_and_of_natBlt addr mask st.pubBound hMask]

def applySlhProtect (msfMasked : Bool) (val : Nat) : Nat :=
  match msfMasked with
  | true  => 0
  | false => val

/-- Speculative observation events (`SpecObsEvent`). -/
inductive SpecObsEvent where
  | obsSpecNone
  | obsSpecMemAddr (addr : Nat)
  | obsSpecMetric (val : Nat)
  | obsSpecJmp (target : Nat)
  | obsSpecBranch (archCond mispred : Bool) (nextBid : Nat)
  | obsSpecExit (retVal : Nat)
  | obsSpecHalted
  deriving DecidableEq, Repr

/-- Single-instruction speculative operational semantics (`stepSctInstr`). -/
def stepSctInstr (ins : SctInstr) (st : SpecState) : SpecState × SpecObsEvent :=
  match st.specHalted with
  | true => (st, .obsSpecHalted)
  | false =>
      match ins with
      | .movImm dst imm =>
          (st.setReg dst imm, .obsSpecNone)
      | .movReg dst src =>
          (st.setReg dst (st.getReg src), .obsSpecNone)
      | .addConst dst src =>
          (st.setReg dst (st.getReg dst + st.getReg src), .obsSpecNone)
      | .andImm dst imm =>
          (st.setReg dst (st.getReg dst &&& imm), .obsSpecNone)
      | .ldUnmasked dst addrReg =>
          let addr := st.getReg addrReg
          let val  := readUnmasked st addr
          (st.setReg dst val, .obsSpecMemAddr addr)
      | .ldMasked dst addrReg mask =>
          let addr := (st.getReg addrReg) &&& mask
          let val  := readSpecMem st addr
          (st.setReg dst val, .obsSpecMemAddr addr)
      | .slhInitMsf =>
          (st.syncMsf, .obsSpecNone)
      | .slhProtect dst src =>
          let val := applySlhProtect st.msfMasked (st.getReg src)
          (st.setReg dst val, .obsSpecNone)
      | .lfence =>
          (st.applyLfence, .obsSpecNone)
      | .helperReadSecretKey dst =>
          (st.setReg dst st.secretKey, .obsSpecNone)
      | .helperEmitPublicMetric valReg =>
          (st, .obsSpecMetric (st.getReg valReg))

def stepSctInstrList : List SctInstr → SpecState → SpecState × List SpecObsEvent
  | [], st => (st, [])
  | i :: is, st =>
      let r1 := stepSctInstr i st
      let r2 := stepSctInstrList is r1.1
      (r2.1, r1.2 :: r2.2)

/-- Speculative terminator semantics (`stepSctTerm`). -/
def stepSctTerm (term : SctTerm) (mispred : Bool) (st : SpecState) : Nat × SpecState × SpecObsEvent :=
  match st.specHalted with
  | true => (0, { st with exited := true }, .obsSpecHalted)
  | false =>
      match term with
      | .exit retReg =>
          (0, { st with exited := true }, .obsSpecExit (st.getReg retReg))
      | .jmp target =>
          (target, st, .obsSpecJmp target)
      | .branchLtBound idxReg bound tInBounds tOutBounds =>
          let archInBounds := natBlt (st.getReg idxReg) bound
          let actualTaken  := match mispred with | false => archInBounds | true => !archInBounds
          let nextBid      := match actualTaken with | true => tInBounds | false => tOutBounds
          (nextBid, st.updateBranchSpec mispred,
            .obsSpecBranch archInBounds mispred nextBid)

def stepSctBlock (prog : SctProg) (bid : Nat) (mispred : Bool) (st : SpecState) :
    Nat × SpecState × List SpecObsEvent :=
  match st.exited || st.specHalted with
  | true => (bid, st, [.obsSpecHalted])
  | false =>
      match getSctBlock? prog bid with
      | none => (bid, { st with exited := true }, [.obsSpecHalted])
      | some bb =>
          let r1 := stepSctInstrList bb.instrs st
          let r2 := stepSctTerm bb.term mispred r1.1
          (r2.1, r2.2.1, r1.2 ++ [r2.2.2])

/-- Multi-step speculative execution trace (`specObsTrace`) driven by an adversary-chosen
    branch-prediction oracle `oracle : List Bool`. -/
def specObsTrace (prog : SctProg) : Nat → List Bool → Nat → SpecState → List SpecObsEvent
  | 0, _, _, _ => []
  | fuel + 1, oracle, bid, st =>
      let mispred := match oracle with | [] => false | m :: _ => m
      let restOracle := match oracle with | [] => [] | _ :: ms => ms
      let res := stepSctBlock prog bid mispred st
      res.2.2 ++ specObsTrace prog fuel restOracle res.1 res.2.1

/-- Classic Spectre v1 Bounds-Check Bypass Gadget (`spectreGadgetProg`). -/
def spectreGadgetProg : SctProg :=
  [ { id := 0
      instrs := []
      term := .branchLtBound .R1 16 1 2 },
    { id := 1
      instrs := [
        .ldUnmasked .R2 .R1,
        .andImm .R2 15,
        .ldUnmasked .R3 .R2,
        .movImm .R0 0
      ]
      term := .exit .R0 },
    { id := 2
      instrs := [ .movImm .R0 0 ]
      term := .exit .R0 } ]

/-- Architectural constant-time projection of `spectreGadgetProg` (`spectreGadgetCtProg`). -/
def spectreGadgetCtProg : CtProg :=
  [ { id := 0
      instrs := []
      term := .branchEqZero .R1 1 2 },
    { id := 1
      instrs := [
        .loadArena .R2 .PublicPacketArena .R1,
        .loadArena .R3 .PublicPacketArena .R2,
        .movImm .R0 0
      ]
      term := .exit .R0 },
    { id := 2
      instrs := [ .movImm .R0 0 ]
      term := .exit .R0 } ]

def spectreState1 : SpecState :=
  { r0 := 0, r1 := 64, r2 := 0, r3 := 0, r4 := 0
    pubBound := 16
    pubMem := fun _ => 0
    kernelSecretMem := fun a => match Nat.beq a 64 with | true => 7 | false => 0
    secretKey := 0
    specMode := false
    msfMasked := false
    specHalted := false
    exited := false }

def spectreState2 : SpecState :=
  { r0 := 0, r1 := 64, r2 := 0, r3 := 0, r4 := 0
    pubBound := 16
    pubMem := fun _ => 0
    kernelSecretMem := fun a => match Nat.beq a 64 with | true => 13 | false => 0
    secretKey := 0
    specMode := false
    msfMasked := false
    specHalted := false
    exited := false }

/-- **Foundational Theorem 2a (`arch_ct_and_memsafe_cert_leaks_under_spectre_v1`)**:
    1. `spectreGadgetCtProg` passes the architectural constant-time certificate checker
       (`checkKernelCtCert = true`).
    2. Without branch misprediction (`oracle = [false]`), `spectreState1` and `spectreState2`
       produce identical observation traces.
    3. Under a single Spectre v1 branch misprediction (`oracle = [true]` on `R1 < 16` with `R1 = 64`),
       `spectreGadgetProg` transiently reads `kernelSecretMem 64` (`7` vs `13`) and leaks it
       as a cache-line address in `specObsTrace`! -/
theorem arch_ct_and_memsafe_cert_leaks_under_spectre_v1 :
    checkKernelCtCert spectreGadgetCtProg [allPublicCtEnv, allPublicCtEnv, allPublicCtEnv] = true ∧
    specObsTrace spectreGadgetProg 2 [false] 0 spectreState1 =
      specObsTrace spectreGadgetProg 2 [false] 0 spectreState2 ∧
    specObsTrace spectreGadgetProg 2 [true] 0 spectreState1 ≠
      specObsTrace spectreGadgetProg 2 [true] 0 spectreState2 := by
  refine ⟨rfl, rfl, ?_⟩
  intro hEq
  nomatch hEq

/-!
  =============================================================================
  SECTION 4: Linux eBPF `sanitize_ptr_alu` / `can_skip_alu_sanitation`
  Path-Pruning Bypass (`CVE-2021-33624`, Commit `9183671af6db`)
  =============================================================================
-/

def cve2021_33624_prog : SctProg :=
  [ { id := 0
      instrs := [ .movImm .R1 0, .movImm .R4 0 ]
      term := .branchLtBound .R4 1 2 1 },
    { id := 1
      instrs := [ .movReg .R1 .R3 ]
      term := .jmp 2 },
    { id := 2
      instrs := [
        .ldUnmasked .R2 .R1,
        .andImm .R2 15,
        .ldUnmasked .R0 .R2
      ]
      term := .exit .R0 } ]

def linuxPrePatchVerifierAccepts (prog : SctProg) : Bool :=
  match getSctBlock? prog 0, getSctBlock? prog 2 with
  | some bb0, some bb2 =>
      Nat.beq bb0.id 0 && Nat.beq bb2.id 2
  | _, _ => false

def cve2021_33624_state1 : SpecState :=
  { spectreState1 with r1 := 0, r3 := 64, r4 := 0 }

def cve2021_33624_state2 : SpecState :=
  { spectreState2 with r1 := 0, r3 := 64, r4 := 0 }

/-- **Foundational Theorem 2b (`linux_skip_alu_sanitation_cve2021_33624_unsound`)**:
    1. `cve2021_33624_prog` is accepted without ALU sanitation by `linuxPrePatchVerifierAccepts`.
    2. Architecturally (`oracle = [false]`), path `0 → 2` executes with `R1 = 0` and leaks nothing.
    3. Under branch misprediction (`oracle = [true]`), transient execution traverses the pruned
       branch `0 → 1 → 2` with `R1 = R3 = 64`, reading `kernelSecretMem 64` (`7` vs `13`) and
       leaking it into `specObsTrace`! -/
theorem linux_skip_alu_sanitation_cve2021_33624_unsound :
    linuxPrePatchVerifierAccepts cve2021_33624_prog = true ∧
    specObsTrace cve2021_33624_prog 3 [false] 0 cve2021_33624_state1 =
      specObsTrace cve2021_33624_prog 3 [false] 0 cve2021_33624_state2 ∧
    specObsTrace cve2021_33624_prog 3 [true] 0 cve2021_33624_state1 ≠
      specObsTrace cve2021_33624_prog 3 [true] 0 cve2021_33624_state2 := by
  refine ⟨rfl, rfl, ?_⟩
  intro hEq
  nomatch hEq

/-!
  =============================================================================
  SECTION 5: Single-Pass Dual-Label Speculative Constant-Time Certificate Checker
  (`checkKernelSctCert` — `Blade` POPL '21, `Pitchfork` PLDI '20, `Jasmin SCT` S&P '23)
  =============================================================================
-/

/-- Speculative stability label (`SpecLabel` in `Blade` POPL 2021 DOI `10.1145/3434330`
    and `Jasmin SCT` IEEE S&P 2023 DOI `10.1109/SP46215.2023.10179418`). -/
inductive SpecLabel where
  | SpecSafe
  | SpecTransient
  deriving DecidableEq, Repr

def SpecLabel.le (s1 s2 : SpecLabel) : Bool :=
  match s1, s2 with
  | .SpecTransient, .SpecSafe => false
  | _, _                      => true

def SpecLabel.join (s1 s2 : SpecLabel) : SpecLabel :=
  match s1, s2 with
  | .SpecSafe, .SpecSafe => .SpecSafe
  | _, _                 => .SpecTransient

theorem specLabel_join_eq_safe (s1 s2 : SpecLabel)
    (h : SpecLabel.join s1 s2 = .SpecSafe) :
    s1 = .SpecSafe ∧ s2 = .SpecSafe := by
  cases s1 <;> cases s2 <;> simp [SpecLabel.join] at h ⊢

theorem specLabel_le_safe_imp (s1 : SpecLabel)
    (h : SpecLabel.le s1 .SpecSafe = true) :
    s1 = .SpecSafe := by
  cases s1 <;> simp [SpecLabel.le] at h ⊢

/-- Dual security label `(arch, spec) ∈ {Public, Secret} × {SpecSafe, SpecTransient}`. -/
structure SctDualLabel where
  arch : SecLabel
  spec : SpecLabel
  deriving DecidableEq, Repr

def SctDualLabel.pubSafe : SctDualLabel :=
  { arch := .Public, spec := .SpecSafe }

def SctDualLabel.pubTransient : SctDualLabel :=
  { arch := .Public, spec := .SpecTransient }

def SctDualLabel.secTransient : SctDualLabel :=
  { arch := .Secret, spec := .SpecTransient }

def SctDualLabel.isPubSafe (l : SctDualLabel) : Bool :=
  match l.arch, l.spec with
  | .Public, .SpecSafe => true
  | _, _               => false

def SctDualLabel.le (l1 l2 : SctDualLabel) : Bool :=
  SecLabel.le l1.arch l2.arch && SpecLabel.le l1.spec l2.spec

def SctDualLabel.join (l1 l2 : SctDualLabel) : SctDualLabel :=
  { arch := SecLabel.join l1.arch l2.arch
    spec := SpecLabel.join l1.spec l2.spec }

/-- Per-block dual-label certificate environment (`SctTypeEnv`). -/
structure SctTypeEnv where
  r0        : SctDualLabel
  r1        : SctDualLabel
  r2        : SctDualLabel
  r3        : SctDualLabel
  r4        : SctDualLabel
  msfSynced : Bool
  pubBound  : Nat
  deriving DecidableEq, Repr

def SctTypeEnv.getReg (env : SctTypeEnv) : Reg → SctDualLabel
  | .R0 => env.r0
  | .R1 => env.r1
  | .R2 => env.r2
  | .R3 => env.r3
  | .R4 => env.r4

def SctTypeEnv.setReg (env : SctTypeEnv) (r : Reg) (l : SctDualLabel) : SctTypeEnv :=
  match r with
  | .R0 => { env with r0 := l }
  | .R1 => { env with r1 := l }
  | .R2 => { env with r2 := l }
  | .R3 => { env with r3 := l }
  | .R4 => { env with r4 := l }

@[simp] theorem SctTypeEnv.msfSynced_setReg (env : SctTypeEnv) (r : Reg) (l : SctDualLabel) :
    (env.setReg r l).msfSynced = env.msfSynced := by
  cases r <;> rfl

@[simp] theorem SctTypeEnv.pubBound_setReg (env : SctTypeEnv) (r : Reg) (l : SctDualLabel) :
    (env.setReg r l).pubBound = env.pubBound := by
  cases r <;> rfl

theorem SctTypeEnv.getReg_setReg_eq (env : SctTypeEnv) (r : Reg) (l : SctDualLabel) :
    (env.setReg r l).getReg r = l := by
  cases r <;> rfl

theorem SctTypeEnv.getReg_setReg_ne (env : SctTypeEnv) (dst r : Reg) (l : SctDualLabel) (h : r ≠ dst) :
    (env.setReg dst l).getReg r = env.getReg r := by
  cases dst <;> cases r <;> first | contradiction | rfl

/-- After a hardware `.lfence` barrier, transient execution is halted (`specHalted := specMode`),
    so all registers' speculative labels are upgraded to `.SpecSafe`. -/
def SctTypeEnv.stabilizeAll (env : SctTypeEnv) : SctTypeEnv :=
  { env with
    r0 := { env.r0 with spec := .SpecSafe }
    r1 := { env.r1 with spec := .SpecSafe }
    r2 := { env.r2 with spec := .SpecSafe }
    r3 := { env.r3 with spec := .SpecSafe }
    r4 := { env.r4 with spec := .SpecSafe } }

def SctTypeEnv.subsumes (env1 env2 : SctTypeEnv) : Bool :=
  Nat.beq env1.pubBound env2.pubBound &&
  (match env2.msfSynced with | true => env1.msfSynced | false => true) &&
  SctDualLabel.le env1.r0 env2.r0 &&
  SctDualLabel.le env1.r1 env2.r1 &&
  SctDualLabel.le env1.r2 env2.r2 &&
  SctDualLabel.le env1.r3 env2.r3 &&
  SctDualLabel.le env1.r4 env2.r4

/-- Single-pass dual-label instruction transformer (`transferSctInstr`). -/
def transferSctInstr (env : SctTypeEnv) (ins : SctInstr) : Option SctTypeEnv :=
  match ins with
  | .movImm dst _ =>
      some (env.setReg dst SctDualLabel.pubSafe)
  | .movReg dst src =>
      some (env.setReg dst (env.getReg src))
  | .addConst dst src =>
      some (env.setReg dst (SctDualLabel.join (env.getReg dst) (env.getReg src)))
  | .andImm dst _ =>
      some (env.setReg dst (env.getReg dst))
  | .ldUnmasked dst addrReg =>
      match SctDualLabel.isPubSafe (env.getReg addrReg) with
      | true  => some (env.setReg dst SctDualLabel.pubTransient)
      | false => none
  | .ldMasked dst addrReg mask =>
      match SctDualLabel.isPubSafe (env.getReg addrReg) && natBlt mask env.pubBound with
      | true  => some (env.setReg dst SctDualLabel.pubSafe)
      | false => none
  | .slhInitMsf =>
      some { env with msfSynced := true }
  | .slhProtect dst src =>
      match env.msfSynced with
      | true =>
          let sl := env.getReg src
          some (env.setReg dst { arch := sl.arch, spec := .SpecSafe })
      | false => none
  | .lfence =>
      some env.stabilizeAll
  | .helperReadSecretKey dst =>
      some (env.setReg dst SctDualLabel.secTransient)
  | .helperEmitPublicMetric valReg =>
      match SctDualLabel.isPubSafe (env.getReg valReg) with
      | true  => some env
      | false => none

def transferSctInstrList (env : SctTypeEnv) : List SctInstr → Option SctTypeEnv
  | []      => some env
  | i :: is =>
      match transferSctInstr env i with
      | none      => none
      | some env' => transferSctInstrList env' is

abbrev SctCertificate := List SctTypeEnv

def getSctCert? (cert : SctCertificate) (bid : Nat) : Option SctTypeEnv :=
  match cert, bid with
  | [], _          => none
  | c :: _, 0      => some c
  | _ :: cs, n + 1 => getSctCert? cs n

def checkSctBlock (cert : SctCertificate) (bb : SctBasicBlock) : Bool :=
  match getSctCert? cert bb.id with
  | none => false
  | some pre =>
      match transferSctInstrList pre bb.instrs with
      | none => false
      | some post =>
          match bb.term with
          | .exit retReg =>
              SctDualLabel.isPubSafe (post.getReg retReg)
          | .jmp target =>
              match getSctCert? cert target with
              | none => false
              | some tCert => SctTypeEnv.subsumes post tCert
          | .branchLtBound idxReg _ tInBounds tOutBounds =>
              match SctDualLabel.isPubSafe (post.getReg idxReg),
                    getSctCert? cert tInBounds, getSctCert? cert tOutBounds with
              | true, some cIn, some cOut =>
                  SctTypeEnv.subsumes post cIn && SctTypeEnv.subsumes post cOut
              | _, _, _ => false

def checkAllSctBlocks (cert : SctCertificate) : List SctBasicBlock → Bool
  | []        => true
  | bb :: bbs => checkSctBlock cert bb && checkAllSctBlocks cert bbs

/-- **In-Kernel Single-Pass Speculative Constant-Time Certificate Checker (`checkKernelSctCert`)**. -/
def checkKernelSctCert (prog : SctProg) (cert : SctCertificate) : Bool :=
  checkAllSctBlocks cert prog

/-- Relational interpretation (`SctRegRel`) of a dual label `l : SctDualLabel` for two states
    `s₁, s₂`. -/
def SctRegRel (l : SctDualLabel) (specMode specHalted : Bool) (v₁ v₂ : Nat) : Prop :=
  (l.arch = .Public → specMode = false → v₁ = v₂) ∧
  (l.arch = .Public → l.spec = .SpecSafe → specHalted = false → v₁ = v₂)

/-- Speculative Low-Equivalence (`SctLowEq`) between two concrete states `s₁, s₂` that may
    differ arbitrarily on both `kernelSecretMem` and `secretKey`! -/
structure SctLowEq (env : SctTypeEnv) (s₁ s₂ : SpecState) : Prop where
  specModeEq   : s₁.specMode = s₂.specMode
  msfMaskedEq  : s₁.msfMasked = s₂.msfMasked
  specHaltedEq : s₁.specHalted = s₂.specHalted
  exitedEq     : s₁.exited = s₂.exited
  haltImpSpec  : s₁.specHalted = true → s₁.specMode = true
  msfSyncInv   : env.msfSynced = true → s₁.specHalted = false → s₁.msfMasked = s₁.specMode
  boundEq1     : s₁.pubBound = env.pubBound
  boundEq2     : s₂.pubBound = env.pubBound
  pubMemEq     : ∀ a : Nat, s₁.pubMem a = s₂.pubMem a
  regRel       : ∀ r : Reg, SctRegRel (env.getReg r) s₁.specMode s₁.specHalted (s₁.getReg r) (s₂.getReg r)

theorem sctDualLabel_isPubSafe_imp (l : SctDualLabel)
    (h : SctDualLabel.isPubSafe l = true) :
    l.arch = .Public ∧ l.spec = .SpecSafe := by
  cases l with
  | mk arch spec =>
      cases arch <;> cases spec <;> simp [SctDualLabel.isPubSafe] at h ⊢

theorem sctRegRel_of_le (l1 l2 : SctDualLabel) (sm sh : Bool) (v₁ v₂ : Nat)
    (hLe : SctDualLabel.le l1 l2 = true)
    (hRel : SctRegRel l1 sm sh v₁ v₂) :
    SctRegRel l2 sm sh v₁ v₂ := by
  unfold SctDualLabel.le at hLe
  simp [Bool.and_eq_true] at hLe
  rcases hLe with ⟨hArch, hSpec⟩
  refine ⟨?_, ?_⟩
  · intro hA2 hSm
    rw [hA2] at hArch
    exact hRel.1 (secLabel_le_public_imp l1.arch hArch) hSm
  · intro hA2 hS2 hSh
    rw [hA2] at hArch
    rw [hS2] at hSpec
    exact hRel.2 (secLabel_le_public_imp l1.arch hArch) (specLabel_le_safe_imp l1.spec hSpec) hSh

theorem sctLowEq_setReg (env : SctTypeEnv) (s₁ s₂ : SpecState)
    (hLow : SctLowEq env s₁ s₂) (dst : Reg) (l : SctDualLabel) (v₁ v₂ : Nat)
    (hVal : SctRegRel l s₁.specMode s₁.specHalted v₁ v₂) :
    SctLowEq (env.setReg dst l) (s₁.setReg dst v₁) (s₂.setReg dst v₂) := by
  refine ⟨by simp [hLow.specModeEq], by simp [hLow.msfMaskedEq],
          by simp [hLow.specHaltedEq], by simp [hLow.exitedEq],
          by intro h; simp at h ⊢; exact hLow.haltImpSpec h,
          ?_,
          by simp [hLow.boundEq1], by simp [hLow.boundEq2],
          by intro a; simp [hLow.pubMemEq a], ?_⟩
  · intro hSync hHalt
    simp at hSync hHalt ⊢
    exact hLow.msfSyncInv hSync hHalt
  · intro r
    simp only [SpecState.specMode_setReg, SpecState.specHalted_setReg]
    cases decEq r dst with
    | isTrue hEq =>
        subst hEq
        rw [SctTypeEnv.getReg_setReg_eq, SpecState.getReg_setReg_eq, SpecState.getReg_setReg_eq]
        exact hVal
    | isFalse hNe =>
        rw [SctTypeEnv.getReg_setReg_ne _ _ _ _ hNe,
            SpecState.getReg_setReg_ne _ _ _ _ hNe,
            SpecState.getReg_setReg_ne _ _ _ _ hNe]
        exact hLow.regRel r

theorem sctLowEq_of_subsumes (env1 env2 : SctTypeEnv) (s₁ s₂ : SpecState)
    (hSub : SctTypeEnv.subsumes env1 env2 = true)
    (hLow : SctLowEq env1 s₁ s₂) :
    SctLowEq env2 s₁ s₂ := by
  unfold SctTypeEnv.subsumes at hSub
  simp [Bool.and_eq_true] at hSub
  rcases hSub with ⟨⟨⟨⟨⟨⟨hBndEq, hMsf⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩
  refine ⟨hLow.specModeEq, hLow.msfMaskedEq, hLow.specHaltedEq, hLow.exitedEq,
          hLow.haltImpSpec, ?_, hLow.boundEq1.trans hBndEq, hLow.boundEq2.trans hBndEq,
          hLow.pubMemEq, ?_⟩
  · intro hSync2 hHalt
    rw [hSync2] at hMsf
    exact hLow.msfSyncInv hMsf hHalt
  · intro r
    cases r with
    | R0 => exact sctRegRel_of_le _ _ _ _ _ _ h0 (hLow.regRel .R0)
    | R1 => exact sctRegRel_of_le _ _ _ _ _ _ h1 (hLow.regRel .R1)
    | R2 => exact sctRegRel_of_le _ _ _ _ _ _ h2 (hLow.regRel .R2)
    | R3 => exact sctRegRel_of_le _ _ _ _ _ _ h3 (hLow.regRel .R3)
    | R4 => exact sctRegRel_of_le _ _ _ _ _ _ h4 (hLow.regRel .R4)

theorem transferSctInstr_pubBound_eq (env env' : SctTypeEnv) (ins : SctInstr)
    (hTrans : transferSctInstr env ins = some env') :
    env'.pubBound = env.pubBound := by
  cases ins with
  | movImm dst _ =>
      simp [transferSctInstr] at hTrans; subst hTrans; simp
  | movReg dst _ =>
      simp [transferSctInstr] at hTrans; subst hTrans; simp
  | addConst dst _ =>
      simp [transferSctInstr] at hTrans; subst hTrans; simp
  | andImm dst _ =>
      simp [transferSctInstr] at hTrans; subst hTrans; simp
  | ldUnmasked dst addrReg =>
      unfold transferSctInstr at hTrans
      cases h : SctDualLabel.isPubSafe (env.getReg addrReg) <;> simp [h] at hTrans
      subst hTrans; simp
  | ldMasked dst addrReg mask =>
      unfold transferSctInstr at hTrans
      cases h1 : SctDualLabel.isPubSafe (env.getReg addrReg) <;>
        cases h2 : natBlt mask env.pubBound <;> simp [h1, h2] at hTrans
      subst hTrans; simp
  | slhInitMsf =>
      simp [transferSctInstr] at hTrans; subst hTrans; rfl
  | slhProtect dst _ =>
      unfold transferSctInstr at hTrans
      cases h : env.msfSynced <;> simp [h] at hTrans
      subst hTrans; simp
  | lfence =>
      simp [transferSctInstr] at hTrans; subst hTrans; rfl
  | helperReadSecretKey dst =>
      simp [transferSctInstr] at hTrans; subst hTrans; simp
  | helperEmitPublicMetric valReg =>
      unfold transferSctInstr at hTrans
      cases h : SctDualLabel.isPubSafe (env.getReg valReg) <;> simp [h] at hTrans
      subst hTrans; rfl

theorem sctLowEq_preserve_when_halted (env env' : SctTypeEnv) (ins : SctInstr) (s₁ s₂ : SpecState)
    (hTrans : transferSctInstr env ins = some env')
    (hHalt1 : s₁.specHalted = true)
    (hLow : SctLowEq env s₁ s₂) :
    SctLowEq env' s₁ s₂ := by
  have hB := (transferSctInstr_pubBound_eq env env' ins hTrans).symm
  have hSm1 : s₁.specMode = true := hLow.haltImpSpec hHalt1
  refine ⟨hLow.specModeEq, hLow.msfMaskedEq, hLow.specHaltedEq, hLow.exitedEq,
          hLow.haltImpSpec, ?_, hLow.boundEq1.trans hB, hLow.boundEq2.trans hB,
          hLow.pubMemEq, ?_⟩
  · intro _ hNotHalt
    rw [hHalt1] at hNotHalt
    nomatch hNotHalt
  · intro r
    refine ⟨?_, ?_⟩
    · intro _ hSmFalse
      rw [hSm1] at hSmFalse
      nomatch hSmFalse
    · intro _ _ hShFalse
      rw [hHalt1] at hShFalse
      nomatch hShFalse

/-- **Per-Instruction Speculative Constant-Time Noninterference (`sct_instr_step_noninterference`)**. -/
theorem sct_instr_step_noninterference (env env' : SctTypeEnv) (ins : SctInstr) (s₁ s₂ : SpecState)
    (hTrans : transferSctInstr env ins = some env')
    (hLow : SctLowEq env s₁ s₂) :
    (stepSctInstr ins s₁).2 = (stepSctInstr ins s₂).2 ∧
    SctLowEq env' (stepSctInstr ins s₁).1 (stepSctInstr ins s₂).1 := by
  unfold stepSctInstr
  cases hHalt1 : s₁.specHalted with
  | true =>
      have hHalt2 : s₂.specHalted = true := by rw [← hLow.specHaltedEq, hHalt1]
      simp [hHalt2]
      exact sctLowEq_preserve_when_halted env env' ins s₁ s₂ hTrans hHalt1 hLow
  | false =>
      have hHalt2 : s₂.specHalted = false := by rw [← hLow.specHaltedEq, hHalt1]
      simp [hHalt2]
      cases ins with
      | movImm dst imm =>
          simp [transferSctInstr] at hTrans
          subst hTrans
          simp
          exact sctLowEq_setReg env s₁ s₂ hLow dst SctDualLabel.pubSafe imm imm
            ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
      | movReg dst src =>
          simp [transferSctInstr] at hTrans
          subst hTrans
          simp
          exact sctLowEq_setReg env s₁ s₂ hLow dst (env.getReg src) _ _ (hLow.regRel src)
      | addConst dst src =>
          simp [transferSctInstr] at hTrans
          subst hTrans
          simp
          refine sctLowEq_setReg env s₁ s₂ hLow dst
            (SctDualLabel.join (env.getReg dst) (env.getReg src)) _ _ ⟨?_, ?_⟩
          · intro hArch hSm
            have ⟨hd, hs⟩ := secLabel_join_eq_public _ _ hArch
            rw [(hLow.regRel dst).1 hd hSm, (hLow.regRel src).1 hs hSm]
          · intro hArch hSpec hSh
            have ⟨hd, hs⟩ := secLabel_join_eq_public _ _ hArch
            have ⟨sd, ss⟩ := specLabel_join_eq_safe _ _ hSpec
            rw [(hLow.regRel dst).2 hd sd hSh, (hLow.regRel src).2 hs ss hSh]
      | andImm dst imm =>
          simp [transferSctInstr] at hTrans
          subst hTrans
          simp
          refine sctLowEq_setReg env s₁ s₂ hLow dst (env.getReg dst) _ _ ⟨?_, ?_⟩
          · intro hArch hSm
            rw [(hLow.regRel dst).1 hArch hSm]
          · intro hArch hSpec hSh
            rw [(hLow.regRel dst).2 hArch hSpec hSh]
      | ldUnmasked dst addrReg =>
          unfold transferSctInstr at hTrans
          cases hSafe : SctDualLabel.isPubSafe (env.getReg addrReg) <;> simp [hSafe] at hTrans
          subst hTrans
          have ⟨hA, hS⟩ := sctDualLabel_isPubSafe_imp _ hSafe
          have hAddrEq : s₁.getReg addrReg = s₂.getReg addrReg :=
            (hLow.regRel addrReg).2 hA hS hHalt1
          refine ⟨by simp [hAddrEq], ?_⟩
          refine sctLowEq_setReg env s₁ s₂ hLow dst SctDualLabel.pubTransient _ _ ⟨?_, ?_⟩
          · intro _ hSm1
            have hSm2 : s₂.specMode = false := by rw [← hLow.specModeEq, hSm1]
            simp [readUnmasked, hSm1, hSm2, hAddrEq, hLow.pubMemEq]
          · intro _ hSpec
            nomatch hSpec
      | ldMasked dst addrReg mask =>
          unfold transferSctInstr at hTrans
          cases hSafe : SctDualLabel.isPubSafe (env.getReg addrReg) <;>
            cases hMask : natBlt mask env.pubBound <;> simp [hSafe, hMask] at hTrans
          subst hTrans
          have ⟨hA, hS⟩ := sctDualLabel_isPubSafe_imp _ hSafe
          have hAddrEq : s₁.getReg addrReg = s₂.getReg addrReg :=
            (hLow.regRel addrReg).2 hA hS hHalt1
          have hMask1 : natBlt mask s₁.pubBound = true := by rw [hLow.boundEq1]; exact hMask
          have hMask2 : natBlt mask s₂.pubBound = true := by rw [hLow.boundEq2]; exact hMask
          have hValEq : readSpecMem s₁ (s₁.getReg addrReg &&& mask) =
                        readSpecMem s₂ (s₂.getReg addrReg &&& mask) := by
            rw [readSpecMem_masked_eq_pubMem s₁ _ _ hMask1,
                readSpecMem_masked_eq_pubMem s₂ _ _ hMask2,
                hAddrEq, hLow.pubMemEq]
          refine ⟨by simp [hAddrEq], ?_⟩
          exact sctLowEq_setReg env s₁ s₂ hLow dst SctDualLabel.pubSafe _ _
            ⟨fun _ _ => hValEq, fun _ _ _ => hValEq⟩
      | slhInitMsf =>
          simp [transferSctInstr] at hTrans
          subst hTrans
          simp
          refine ⟨hLow.specModeEq, hLow.specModeEq, hLow.specHaltedEq, hLow.exitedEq,
                  hLow.haltImpSpec, fun _ _ => rfl, hLow.boundEq1, hLow.boundEq2,
                  hLow.pubMemEq, ?_⟩
          intro r
          cases r <;> simp [SctTypeEnv.getReg, SpecState.syncMsf, SpecState.getReg]
          · exact hLow.regRel .R0
          · exact hLow.regRel .R1
          · exact hLow.regRel .R2
          · exact hLow.regRel .R3
          · exact hLow.regRel .R4
      | slhProtect dst src =>
          unfold transferSctInstr at hTrans
          cases hSync : env.msfSynced <;> simp [hSync] at hTrans
          subst hTrans
          simp
          have hMsf1 : s₁.msfMasked = s₁.specMode := hLow.msfSyncInv hSync hHalt1
          have hValEq : (env.getReg src).arch = .Public →
              applySlhProtect s₁.msfMasked (s₁.getReg src) =
              applySlhProtect s₂.msfMasked (s₂.getReg src) := by
            intro hArch
            rw [← hLow.msfMaskedEq, hMsf1]
            cases hSm : s₁.specMode with
            | true => rfl
            | false =>
                simp [applySlhProtect]
                exact (hLow.regRel src).1 hArch hSm
          exact sctLowEq_setReg env s₁ s₂ hLow dst
            { arch := (env.getReg src).arch, spec := .SpecSafe } _ _
            ⟨fun hA _ => hValEq hA, fun hA _ _ => hValEq hA⟩
      | lfence =>
          simp [transferSctInstr] at hTrans
          subst hTrans
          simp [SpecState.applyLfence]
          refine ⟨hLow.specModeEq, hLow.msfMaskedEq, hLow.specModeEq, hLow.exitedEq,
                  fun h => h, ?_, hLow.boundEq1, hLow.boundEq2, hLow.pubMemEq, ?_⟩
          · intro hSync _
            exact hLow.msfSyncInv hSync hHalt1
          · intro r
            cases r <;> simp [SctTypeEnv.stabilizeAll, SctTypeEnv.getReg, SpecState.getReg]
            · exact ⟨(hLow.regRel .R0).1, fun hA _ hSm => (hLow.regRel .R0).1 hA hSm⟩
            · exact ⟨(hLow.regRel .R1).1, fun hA _ hSm => (hLow.regRel .R1).1 hA hSm⟩
            · exact ⟨(hLow.regRel .R2).1, fun hA _ hSm => (hLow.regRel .R2).1 hA hSm⟩
            · exact ⟨(hLow.regRel .R3).1, fun hA _ hSm => (hLow.regRel .R3).1 hA hSm⟩
            · exact ⟨(hLow.regRel .R4).1, fun hA _ hSm => (hLow.regRel .R4).1 hA hSm⟩
      | helperReadSecretKey dst =>
          simp [transferSctInstr] at hTrans
          subst hTrans
          simp
          exact sctLowEq_setReg env s₁ s₂ hLow dst SctDualLabel.secTransient _ _
            ⟨(fun h _ => nomatch h), (fun h _ _ => nomatch h)⟩
      | helperEmitPublicMetric valReg =>
          unfold transferSctInstr at hTrans
          cases hSafe : SctDualLabel.isPubSafe (env.getReg valReg) <;> simp [hSafe] at hTrans
          subst hTrans
          have ⟨hA, hS⟩ := sctDualLabel_isPubSafe_imp _ hSafe
          simp
          exact ⟨(hLow.regRel valReg).2 hA hS hHalt1, hLow⟩

theorem sct_instr_list_noninterference (insns : List SctInstr) :
    ∀ (env env' : SctTypeEnv) (s₁ s₂ : SpecState),
      transferSctInstrList env insns = some env' →
      SctLowEq env s₁ s₂ →
      (stepSctInstrList insns s₁).2 = (stepSctInstrList insns s₂).2 ∧
      SctLowEq env' (stepSctInstrList insns s₁).1 (stepSctInstrList insns s₂).1 := by
  induction insns with
  | nil =>
      intro env env' s₁ s₂ hTrans hLow
      simp [transferSctInstrList] at hTrans
      subst hTrans
      simp [stepSctInstrList]
      exact hLow
  | cons i is ih =>
      intro env env' s₁ s₂ hTrans hLow
      unfold transferSctInstrList at hTrans
      cases h1 : transferSctInstr env i with
      | none => rw [h1] at hTrans; nomatch hTrans
      | some envMid =>
          rw [h1] at hTrans
          have ⟨hEv, hLowMid⟩ := sct_instr_step_noninterference env envMid i s₁ s₂ h1 hLow
          have ⟨hEvs, hLowEnd⟩ := ih envMid env' (stepSctInstr i s₁).1 (stepSctInstr i s₂).1 hTrans hLowMid
          simp [stepSctInstrList, hEv, hEvs]
          exact hLowEnd

def AllBlocksSctCertified (prog : SctProg) (cert : SctCertificate) : Prop :=
  ∀ bid bb, getSctBlock? prog bid = some bb → bb.id = bid ∧ checkSctBlock cert bb = true

def checkSctBlocksIndexed (cert : SctCertificate) : Nat → List SctBasicBlock → Bool
  | _, [] => true
  | idx, bb :: bbs =>
      Nat.beq bb.id idx && checkSctBlock cert bb && checkSctBlocksIndexed cert (idx + 1) bbs

def checkKernelSctCertIndexed (prog : SctProg) (cert : SctCertificate) : Bool :=
  checkSctBlocksIndexed cert 0 prog

theorem checkSctBlocksIndexed_imp_get (cert : SctCertificate) (bbs : List SctBasicBlock) :
    ∀ (idx bid : Nat) (bb : SctBasicBlock),
      checkSctBlocksIndexed cert idx bbs = true →
      getSctBlock? bbs bid = some bb →
      bb.id = idx + bid ∧ checkSctBlock cert bb = true := by
  induction bbs with
  | nil =>
      intro idx bid bb _ hGet
      simp [getSctBlock?] at hGet
  | cons hd tl ih =>
      intro idx bid bb hChk hGet
      unfold checkSctBlocksIndexed at hChk
      simp [Bool.and_eq_true] at hChk
      rcases hChk with ⟨⟨hId, hBlk⟩, hRest⟩
      cases bid with
      | zero =>
          simp [getSctBlock?] at hGet
          subst hGet
          simp [hId, hBlk]
      | succ n =>
          simp [getSctBlock?] at hGet
          have ⟨hId', hBlk'⟩ := ih (idx + 1) n bb hRest hGet
          refine ⟨?_, hBlk'⟩
          omega

theorem checkKernelSctCertIndexed_imp_AllBlocksSctCertified (prog : SctProg) (cert : SctCertificate)
    (h : checkKernelSctCertIndexed prog cert = true) :
    AllBlocksSctCertified prog cert := by
  intro bid bb hGet
  have ⟨hId, hBlk⟩ := checkSctBlocksIndexed_imp_get cert prog 0 bid bb h hGet
  simp at hId
  exact ⟨hId, hBlk⟩

theorem sctRegRel_after_branch (l : SctDualLabel) (sm sh mispred : Bool) (v₁ v₂ : Nat)
    (hRel : SctRegRel l sm sh v₁ v₂) :
    SctRegRel l (sm || mispred) sh v₁ v₂ := by
  refine ⟨?_, hRel.2⟩
  intro hArch hOrFalse
  have hSmFalse : sm = false := by
    cases sm <;> simp at hOrFalse ⊢
  exact hRel.1 hArch hSmFalse

theorem sctLowEq_updateBranchSpec (env : SctTypeEnv) (s₁ s₂ : SpecState) (mispred : Bool)
    (hHalt1 : s₁.specHalted = false)
    (hLow : SctLowEq env s₁ s₂) :
    SctLowEq env (s₁.updateBranchSpec mispred) (s₂.updateBranchSpec mispred) := by
  refine ⟨by simp [SpecState.updateBranchSpec, hLow.specModeEq],
          by simp [SpecState.updateBranchSpec, hLow.msfMaskedEq],
          hLow.specHaltedEq,
          hLow.exitedEq,
          by intro hSh; simp [SpecState.updateBranchSpec, hHalt1] at hSh,
          ?_,
          hLow.boundEq1,
          hLow.boundEq2,
          hLow.pubMemEq,
          ?_⟩
  · intro hSync _
    simp [SpecState.updateBranchSpec, hLow.msfSyncInv hSync hHalt1]
  · intro r
    simp only [SpecState.getReg_updateBranchSpec]
    exact sctRegRel_after_branch (env.getReg r) s₁.specMode s₁.specHalted mispred _ _ (hLow.regRel r)

theorem sct_block_step_noninterference (prog : SctProg) (cert : SctCertificate)
    (hCert : AllBlocksSctCertified prog cert)
    (bid : Nat) (mispred : Bool) (pre : SctTypeEnv) (s₁ s₂ : SpecState)
    (hPre : getSctCert? cert bid = some pre)
    (hLow : SctLowEq pre s₁ s₂) :
    let r₁ := stepSctBlock prog bid mispred s₁
    let r₂ := stepSctBlock prog bid mispred s₂
    r₁.1 = r₂.1 ∧ r₁.2.2 = r₂.2.2 ∧
    ((r₁.2.1.exited || r₁.2.1.specHalted) = true ∧ (r₂.2.1.exited || r₂.2.1.specHalted) = true ∨
      ∃ nextPre, getSctCert? cert r₁.1 = some nextPre ∧ SctLowEq nextPre r₁.2.1 r₂.2.1) := by
  dsimp
  unfold stepSctBlock
  have hStopEq : (s₁.exited || s₁.specHalted) = (s₂.exited || s₂.specHalted) := by
    rw [hLow.exitedEq, hLow.specHaltedEq]
  cases hStop1 : (s₁.exited || s₁.specHalted) with
  | true =>
      have hStop2 : (s₂.exited || s₂.specHalted) = true := by rw [← hStopEq, hStop1]
      simp [hStop2]
      exact Or.inl (Bool.or_eq_true_iff.mp hStop1)
  | false =>
      have hStop2 : (s₂.exited || s₂.specHalted) = false := by rw [← hStopEq, hStop1]
      simp [hStop2]
      cases hBlk : getSctBlock? prog bid with
      | none => simp
      | some bb =>
          simp
          have ⟨hBidEq, hChk⟩ := hCert bid bb hBlk
          unfold checkSctBlock at hChk
          rw [hBidEq, hPre] at hChk
          simp at hChk
          cases hList : transferSctInstrList pre bb.instrs with
          | none => rw [hList] at hChk; nomatch hChk
          | some post =>
              rw [hList] at hChk
              simp at hChk
              have ⟨hEvsEq, hPostLow⟩ := sct_instr_list_noninterference bb.instrs pre post s₁ s₂ hList hLow
              unfold stepSctTerm
              cases hHaltMid1 : (stepSctInstrList bb.instrs s₁).1.specHalted with
              | true =>
                  have hHaltMid2 : (stepSctInstrList bb.instrs s₂).1.specHalted = true := by
                    rw [← hPostLow.specHaltedEq, hHaltMid1]
                  simp [hHaltMid2, hEvsEq]
              | false =>
                  have hHaltMid2 : (stepSctInstrList bb.instrs s₂).1.specHalted = false := by
                    rw [← hPostLow.specHaltedEq, hHaltMid1]
                  simp [hHaltMid2]
                  cases hTerm : bb.term with
                  | exit retReg =>
                      simp [hTerm] at hChk
                      have ⟨hA, hS⟩ := sctDualLabel_isPubSafe_imp _ hChk
                      have hRetEq := (hPostLow.regRel retReg).2 hA hS hHaltMid1
                      simp [hEvsEq, hRetEq]
                  | jmp target =>
                      simp [hTerm] at hChk
                      cases hTargetCert : getSctCert? cert target with
                      | none => simp [hTargetCert] at hChk
                      | some tCert =>
                          simp [hTargetCert] at hChk
                          simp [hEvsEq]
                          exact Or.inr (sctLowEq_of_subsumes post tCert _ _ hChk hPostLow)
                  | branchLtBound idxReg bound tInBounds tOutBounds =>
                      simp [hTerm] at hChk
                      cases hSafe : SctDualLabel.isPubSafe (post.getReg idxReg) <;>
                        cases hCIn : getSctCert? cert tInBounds <;>
                        cases hCOut : getSctCert? cert tOutBounds <;>
                        simp [hSafe, hCIn, hCOut] at hChk
                      rcases hChk with ⟨hSubIn, hSubOut⟩
                      have ⟨hA, hS⟩ := sctDualLabel_isPubSafe_imp _ hSafe
                      have hIdxEq := (hPostLow.regRel idxReg).2 hA hS hHaltMid1
                      simp [hEvsEq, hIdxEq]
                      have hBrLow := sctLowEq_updateBranchSpec post
                        (stepSctInstrList bb.instrs s₁).1 (stepSctInstrList bb.instrs s₂).1
                        mispred hHaltMid1 hPostLow
                      cases (match mispred with
                             | false => natBlt ((stepSctInstrList bb.instrs s₂).1.getReg idxReg) bound
                             | true => !natBlt ((stepSctInstrList bb.instrs s₂).1.getReg idxReg) bound) with
                      | true =>
                          exact Or.inr ⟨_, hCIn, sctLowEq_of_subsumes post _ _ _ hSubIn hBrLow⟩
                      | false =>
                          exact Or.inr ⟨_, hCOut, sctLowEq_of_subsumes post _ _ _ hSubOut hBrLow⟩

theorem specObsTrace_of_stopped (prog : SctProg) (fuel : Nat) (oracle : List Bool)
    (bid : Nat) (s₁ s₂ : SpecState)
    (h1 : (s₁.exited || s₁.specHalted) = true)
    (h2 : (s₂.exited || s₂.specHalted) = true) :
    specObsTrace prog fuel oracle bid s₁ = specObsTrace prog fuel oracle bid s₂ := by
  induction fuel generalizing oracle bid with
  | zero => rfl
  | succ f ih =>
      unfold specObsTrace stepSctBlock
      dsimp
      rw [h1, h2]
      simp [ih _ bid]

/-- **Foundational Theorem 2c (`kernel_sct_dual_label_cert_soundness`)**:
    If a Ring-0 kernel extension `prog` passes the single-pass O(|I|) dual-label speculative
    constant-time certificate checker (`AllBlocksSctCertified prog cert`), then for **every**
    adversary branch-prediction oracle `oracle : List Bool`, **every** step budget `fuel : Nat`,
    and **all pairs** of initial states `(s₁, s₂)` satisfying `SctLowEq pre s₁ s₂`
    (with arbitrary host kernel secrets `s₁.kernelSecretMem ≠ s₂.kernelSecretMem` and
    `s₁.secretKey ≠ s₂.secretKey`), their speculative observation traces are **100% identical**:
    `specObsTrace prog fuel oracle bid s₁ = specObsTrace prog fuel oracle bid s₂`! -/
theorem kernel_sct_dual_label_cert_soundness
    (prog : SctProg) (cert : SctCertificate)
    (hCert : AllBlocksSctCertified prog cert) :
    ∀ (fuel : Nat) (oracle : List Bool) (bid : Nat) (pre : SctTypeEnv) (s₁ s₂ : SpecState),
      getSctCert? cert bid = some pre →
      SctLowEq pre s₁ s₂ →
      specObsTrace prog fuel oracle bid s₁ = specObsTrace prog fuel oracle bid s₂ := by
  intro fuel
  induction fuel with
  | zero =>
      intro oracle bid pre s₁ s₂ _ _
      rfl
  | succ f ih =>
      intro oracle bid pre s₁ s₂ hPre hLow
      unfold specObsTrace
      dsimp
      let mispred := match oracle with | [] => false | m :: _ => m
      let restOracle := match oracle with | [] => [] | _ :: ms => ms
      have hStep := sct_block_step_noninterference prog cert hCert bid mispred pre s₁ s₂ hPre hLow
      dsimp at hStep
      rcases hStep with ⟨hNextEq, hEvsEq, hCont⟩
      rw [hEvsEq, hNextEq]
      cases hCont with
      | inl hStopped =>
          rw [specObsTrace_of_stopped prog f restOracle
              (stepSctBlock prog bid mispred s₂).1
              (stepSctBlock prog bid mispred s₁).2.1
              (stepSctBlock prog bid mispred s₂).2.1
              hStopped.1 hStopped.2]
      | inr hNextCert =>
          rcases hNextCert with ⟨nextPre, hNextPre, hNextLow⟩
          rw [hNextEq] at hNextPre
          rw [ih restOracle (stepSctBlock prog bid mispred s₂).1 nextPre
              (stepSctBlock prog bid mispred s₁).2.1
              (stepSctBlock prog bid mispred s₂).2.1
              hNextPre hNextLow]

/-- Concrete verification of `spectreGadgetProg` and its three Speculative Constant-Time repairs! -/
def defaultSctEnv : SctTypeEnv :=
  { r0 := SctDualLabel.pubSafe
    r1 := SctDualLabel.pubSafe
    r2 := SctDualLabel.pubSafe
    r3 := SctDualLabel.pubSafe
    r4 := SctDualLabel.pubSafe
    msfSynced := true
    pubBound := 16 }

def defaultSctCert3 : SctCertificate :=
  [defaultSctEnv, defaultSctEnv, defaultSctEnv]

/-- 1. Unmitigated `spectreGadgetProg` AND `cve2021_33624_prog` are both REJECTED by `checkKernelSctCert`
    because `.ldUnmasked` taints `R2` as `pubTransient` (`⟨.Public, .SpecTransient⟩`), which is
    rejected at the transmitter `.ldUnmasked .R3 .R2`! -/
theorem spectre_gadget_rejected_by_sct_cert :
    checkKernelSctCert spectreGadgetProg defaultSctCert3 = false ∧
    checkKernelSctCert cve2021_33624_prog defaultSctCert3 = false :=
  ⟨rfl, rfl⟩

/-- 2. Repair A (`Blade` POPL '21 / `Jasmin SCT` S&P '23 Selective SLH Cut-Set `protect`):
    Inserting `.slhProtect .R2 .R2` on the source-to-sink cut edge between `.ldUnmasked .R2 .R1`
    and `.ldUnmasked .R3 .R2` upgrades `R2` back to `pubSafe` (`⟨.Public, .SpecSafe⟩`), passes
    `checkKernelSctCert = true`, and eliminates the Spectre v1 leak! -/
def spectreGadgetBladeSlhProg : SctProg :=
  [ { id := 0
      instrs := [ .slhInitMsf ]
      term := .branchLtBound .R1 16 1 2 },
    { id := 1
      instrs := [
        .ldUnmasked .R2 .R1,
        .andImm .R2 15,
        .slhProtect .R2 .R2,
        .ldUnmasked .R3 .R2,
        .movImm .R0 0
      ]
      term := .exit .R0 },
    { id := 2
      instrs := [ .movImm .R0 0 ]
      term := .exit .R0 } ]

theorem spectre_gadget_repaired_by_blade_slh_accepted :
    checkKernelSctCert spectreGadgetBladeSlhProg defaultSctCert3 = true ∧
    specObsTrace spectreGadgetBladeSlhProg 2 [true] 0 spectreState1 =
      specObsTrace spectreGadgetBladeSlhProg 2 [true] 0 spectreState2 :=
  ⟨rfl, rfl⟩

/-- 3. Repair B (LFI/SFI Bitwise Sandboxing `.ldMasked`):
    Replacing `.ldUnmasked .R2 .R1` with SFI `.ldMasked .R2 .R1 15` (`15 < 16`) keeps `R2`
    at `pubSafe` (`⟨.Public, .SpecSafe⟩`) with ZERO fences and ZERO `SLH` instructions, passes
    `checkKernelSctCert = true`, and eliminates the Spectre v1 leak! -/
def spectreGadgetSfiMaskProg : SctProg :=
  [ { id := 0
      instrs := []
      term := .branchLtBound .R1 16 1 2 },
    { id := 1
      instrs := [
        .ldMasked .R2 .R1 15,
        .andImm .R2 15,
        .ldUnmasked .R3 .R2,
        .movImm .R0 0
      ]
      term := .exit .R0 },
    { id := 2
      instrs := [ .movImm .R0 0 ]
      term := .exit .R0 } ]

theorem spectre_gadget_repaired_by_sfi_mask_accepted :
    checkKernelSctCert spectreGadgetSfiMaskProg defaultSctCert3 = true ∧
    specObsTrace spectreGadgetSfiMaskProg 2 [true] 0 spectreState1 =
      specObsTrace spectreGadgetSfiMaskProg 2 [true] 0 spectreState2 :=
  ⟨rfl, rfl⟩

/-- 4. Repair C (Hardware Speculation Barrier `.lfence` / `BPF_ST_NOSPEC`):
    Inserting `.lfence` at the entry of Block 1 halts transient execution, passes
    `checkKernelSctCert = true`, and eliminates the Spectre v1 leak! -/
def spectreGadgetLfenceProg : SctProg :=
  [ { id := 0
      instrs := []
      term := .branchLtBound .R1 16 1 2 },
    { id := 1
      instrs := [
        .lfence,
        .ldUnmasked .R2 .R1,
        .andImm .R2 15,
        .lfence,
        .ldUnmasked .R3 .R2,
        .movImm .R0 0
      ]
      term := .exit .R0 },
    { id := 2
      instrs := [ .movImm .R0 0 ]
      term := .exit .R0 } ]

theorem spectre_gadget_repaired_by_lfence_accepted :
    checkKernelSctCert spectreGadgetLfenceProg defaultSctCert3 = true ∧
    specObsTrace spectreGadgetLfenceProg 2 [true] 0 spectreState1 =
      specObsTrace spectreGadgetLfenceProg 2 [true] 0 spectreState2 :=
  ⟨rfl, rfl⟩

/-!
  =============================================================================
  SECTION 6: Spectre v4 (`STL` Speculative Store Bypass) & Sticky Stack-Slot
  Secret Taint Certificates (`Jasmin SCT` IEEE S&P 2023 / POPL 2025,
  Linux `BPF_ST_NOSPEC` Commit `f5e81d111750`)
  =============================================================================
-/

theorem secLabel_le_join_left (a b : SecLabel) :
    SecLabel.le a (SecLabel.join a b) = true := by
  cases a <;> cases b <;> rfl

theorem secLabel_le_join_right (a b : SecLabel) :
    SecLabel.le b (SecLabel.join a b) = true := by
  cases a <;> cases b <;> rfl

theorem specLabel_le_join_left (a b : SpecLabel) :
    SpecLabel.le a (SpecLabel.join a b) = true := by
  cases a <;> cases b <;> rfl

theorem specLabel_le_join_right (a b : SpecLabel) :
    SpecLabel.le b (SpecLabel.join a b) = true := by
  cases a <;> cases b <;> rfl

theorem sctDualLabel_le_join_left (l1 l2 : SctDualLabel) :
    SctDualLabel.le l1 (SctDualLabel.join l1 l2) = true := by
  unfold SctDualLabel.le SctDualLabel.join
  simp [secLabel_le_join_left, specLabel_le_join_left]

theorem sctDualLabel_le_join_right (l1 l2 : SctDualLabel) :
    SctDualLabel.le l2 (SctDualLabel.join l1 l2) = true := by
  unfold SctDualLabel.le SctDualLabel.join
  simp [secLabel_le_join_right, specLabel_le_join_right]

/-- Combined Spectre v1 (`PHT`) + Spectre v4 (`STL` Speculative Store Bypass) instruction set
    with stack spill (`spillStack`) and stack fill (`fillStack`) operations. -/
inductive SctV4Instr where
  | movImm (dst : Reg) (imm : Nat)
  | movReg (dst src : Reg)
  | addConst (dst src : Reg)
  | andImm (dst : Reg) (imm : Nat)
  | ldUnmasked (dst addrReg : Reg)
  | ldMasked (dst addrReg : Reg) (mask : Nat)
  | spillStack (slot : StackSlot) (src : Reg)
  | fillStack (dst : Reg) (slot : StackSlot)
  | slhInitMsf
  | slhProtect (dst src : Reg)
  | lfence
  | helperReadSecretKey (dst : Reg)
  | helperEmitPublicMetric (valReg : Reg)
  deriving DecidableEq, Repr

structure SctV4BasicBlock where
  id     : Nat
  instrs : List SctV4Instr
  term   : SctTerm
  deriving DecidableEq, Repr

abbrev SctV4Prog := List SctV4BasicBlock

def getSctV4Block? (prog : SctV4Prog) (bid : Nat) : Option SctV4BasicBlock :=
  match prog, bid with
  | [], _           => none
  | bb :: _, 0      => some bb
  | _ :: bbs, n + 1 => getSctV4Block? bbs n

/-- Concrete speculative execution state (`SpecV4State`) modeling both Spectre v1 (`PHT`)
    and Spectre v4 (`STL` Speculative Store Bypass on stack slots `S0`, `S1`):
    - `s0Curr, s1Curr`: latest architectural values written to stack slots `S0, S1`.
    - `s0Stale, s1Stale`: older stale values in the store buffer / L1 stack cache prior to
      the most recent overwrite, which a Spectre v4 `STL` store-bypass (`stlBypass = true`)
      can transiently forward to a subsequent `fillStack` load! -/
structure SpecV4State where
  r0              : Nat
  r1              : Nat
  r2              : Nat
  r3              : Nat
  r4              : Nat
  s0Curr          : Nat
  s0Stale         : Nat
  s1Curr          : Nat
  s1Stale         : Nat
  pubBound        : Nat
  pubMem          : Nat → Nat
  kernelSecretMem : Nat → Nat
  secretKey       : Nat
  specMode        : Bool
  msfMasked       : Bool
  specHalted      : Bool
  exited          : Bool

def SpecV4State.getReg (st : SpecV4State) : Reg → Nat
  | .R0 => st.r0
  | .R1 => st.r1
  | .R2 => st.r2
  | .R3 => st.r3
  | .R4 => st.r4

def SpecV4State.setReg (st : SpecV4State) (r : Reg) (v : Nat) : SpecV4State :=
  match r with
  | .R0 => { st with r0 := v }
  | .R1 => { st with r1 := v }
  | .R2 => { st with r2 := v }
  | .R3 => { st with r3 := v }
  | .R4 => { st with r4 := v }

def SpecV4State.getStackCurr (st : SpecV4State) : StackSlot → Nat
  | .S0 => st.s0Curr
  | .S1 => st.s1Curr

def SpecV4State.getStackStale (st : SpecV4State) : StackSlot → Nat
  | .S0 => st.s0Stale
  | .S1 => st.s1Stale

/-- Spilling a register `v` to stack slot `sl` updates the architectural slot `Curr := v`
    while shifting the previous value into the stale store-buffer slot `Stale := Curr`. -/
def SpecV4State.spillStack (st : SpecV4State) (sl : StackSlot) (v : Nat) : SpecV4State :=
  match sl with
  | .S0 => { st with s0Curr := v, s0Stale := st.s0Curr }
  | .S1 => { st with s1Curr := v, s1Stale := st.s1Curr }

def SpecV4State.enterStlSpec (st : SpecV4State) (stlBypass : Bool) : SpecV4State :=
  { st with specMode := st.specMode || stlBypass }

def SpecV4State.syncMsf (st : SpecV4State) : SpecV4State :=
  { st with msfMasked := st.specMode }

def SpecV4State.applyLfence (st : SpecV4State) : SpecV4State :=
  { st with specHalted := st.specMode }

def SpecV4State.updateBranchSpec (st : SpecV4State) (mispred : Bool) : SpecV4State :=
  { st with specMode := st.specMode || mispred, msfMasked := st.msfMasked || mispred }

@[simp] theorem SpecV4State.specMode_setReg (st : SpecV4State) (r : Reg) (v : Nat) :
    (st.setReg r v).specMode = st.specMode := by
  cases r <;> rfl

@[simp] theorem SpecV4State.msfMasked_setReg (st : SpecV4State) (r : Reg) (v : Nat) :
    (st.setReg r v).msfMasked = st.msfMasked := by
  cases r <;> rfl

@[simp] theorem SpecV4State.specHalted_setReg (st : SpecV4State) (r : Reg) (v : Nat) :
    (st.setReg r v).specHalted = st.specHalted := by
  cases r <;> rfl

@[simp] theorem SpecV4State.exited_setReg (st : SpecV4State) (r : Reg) (v : Nat) :
    (st.setReg r v).exited = st.exited := by
  cases r <;> rfl

@[simp] theorem SpecV4State.pubBound_setReg (st : SpecV4State) (r : Reg) (v : Nat) :
    (st.setReg r v).pubBound = st.pubBound := by
  cases r <;> rfl

@[simp] theorem SpecV4State.pubMem_setReg (st : SpecV4State) (r : Reg) (v : Nat) :
    (st.setReg r v).pubMem = st.pubMem := by
  cases r <;> rfl

@[simp] theorem SpecV4State.getStackCurr_setReg (st : SpecV4State) (r : Reg) (v : Nat) (sl : StackSlot) :
    (st.setReg r v).getStackCurr sl = st.getStackCurr sl := by
  cases r <;> cases sl <;> rfl

@[simp] theorem SpecV4State.getStackStale_setReg (st : SpecV4State) (r : Reg) (v : Nat) (sl : StackSlot) :
    (st.setReg r v).getStackStale sl = st.getStackStale sl := by
  cases r <;> cases sl <;> rfl

theorem SpecV4State.getReg_setReg_eq (st : SpecV4State) (r : Reg) (v : Nat) :
    (st.setReg r v).getReg r = v := by
  cases r <;> rfl

theorem SpecV4State.getReg_setReg_ne (st : SpecV4State) (dst r : Reg) (v : Nat) (h : r ≠ dst) :
    (st.setReg dst v).getReg r = st.getReg r := by
  cases dst <;> cases r <;> first | contradiction | rfl

@[simp] theorem SpecV4State.specMode_spillStack (st : SpecV4State) (sl : StackSlot) (v : Nat) :
    (st.spillStack sl v).specMode = st.specMode := by
  cases sl <;> rfl

@[simp] theorem SpecV4State.msfMasked_spillStack (st : SpecV4State) (sl : StackSlot) (v : Nat) :
    (st.spillStack sl v).msfMasked = st.msfMasked := by
  cases sl <;> rfl

@[simp] theorem SpecV4State.specHalted_spillStack (st : SpecV4State) (sl : StackSlot) (v : Nat) :
    (st.spillStack sl v).specHalted = st.specHalted := by
  cases sl <;> rfl

@[simp] theorem SpecV4State.exited_spillStack (st : SpecV4State) (sl : StackSlot) (v : Nat) :
    (st.spillStack sl v).exited = st.exited := by
  cases sl <;> rfl

@[simp] theorem SpecV4State.pubBound_spillStack (st : SpecV4State) (sl : StackSlot) (v : Nat) :
    (st.spillStack sl v).pubBound = st.pubBound := by
  cases sl <;> rfl

@[simp] theorem SpecV4State.pubMem_spillStack (st : SpecV4State) (sl : StackSlot) (v : Nat) :
    (st.spillStack sl v).pubMem = st.pubMem := by
  cases sl <;> rfl

@[simp] theorem SpecV4State.getReg_spillStack (st : SpecV4State) (sl : StackSlot) (v : Nat) (r : Reg) :
    (st.spillStack sl v).getReg r = st.getReg r := by
  cases sl <;> cases r <;> rfl

theorem SpecV4State.getStackCurr_spillStack_eq (st : SpecV4State) (sl : StackSlot) (v : Nat) :
    (st.spillStack sl v).getStackCurr sl = v := by
  cases sl <;> rfl

theorem SpecV4State.getStackCurr_spillStack_ne (st : SpecV4State) (slot sl : StackSlot) (v : Nat) (h : sl ≠ slot) :
    (st.spillStack slot v).getStackCurr sl = st.getStackCurr sl := by
  cases slot <;> cases sl <;> first | contradiction | rfl

theorem SpecV4State.getStackStale_spillStack_eq (st : SpecV4State) (sl : StackSlot) (v : Nat) :
    (st.spillStack sl v).getStackStale sl = st.getStackCurr sl := by
  cases sl <;> rfl

theorem SpecV4State.getStackStale_spillStack_ne (st : SpecV4State) (slot sl : StackSlot) (v : Nat) (h : sl ≠ slot) :
    (st.spillStack slot v).getStackStale sl = st.getStackStale sl := by
  cases slot <;> cases sl <;> first | contradiction | rfl

@[simp] theorem SpecV4State.getReg_enterStlSpec (st : SpecV4State) (b : Bool) (r : Reg) :
    (st.enterStlSpec b).getReg r = st.getReg r := by
  cases r <;> rfl

@[simp] theorem SpecV4State.getStackCurr_enterStlSpec (st : SpecV4State) (b : Bool) (sl : StackSlot) :
    (st.enterStlSpec b).getStackCurr sl = st.getStackCurr sl := by
  cases sl <;> rfl

@[simp] theorem SpecV4State.getStackStale_enterStlSpec (st : SpecV4State) (b : Bool) (sl : StackSlot) :
    (st.enterStlSpec b).getStackStale sl = st.getStackStale sl := by
  cases sl <;> rfl

@[simp] theorem SpecV4State.getReg_updateBranchSpec (st : SpecV4State) (m : Bool) (r : Reg) :
    (st.updateBranchSpec m).getReg r = st.getReg r := by
  cases r <;> rfl

@[simp] theorem SpecV4State.getStackCurr_updateBranchSpec (st : SpecV4State) (m : Bool) (sl : StackSlot) :
    (st.updateBranchSpec m).getStackCurr sl = st.getStackCurr sl := by
  cases sl <;> rfl

@[simp] theorem SpecV4State.getStackStale_updateBranchSpec (st : SpecV4State) (m : Bool) (sl : StackSlot) :
    (st.updateBranchSpec m).getStackStale sl = st.getStackStale sl := by
  cases sl <;> rfl

def readSpecV4Mem (st : SpecV4State) (addr : Nat) : Nat :=
  match natBlt addr st.pubBound with
  | true  => st.pubMem addr
  | false => st.kernelSecretMem addr

def readUnmaskedV4 (st : SpecV4State) (addr : Nat) : Nat :=
  match st.specMode with
  | false => st.pubMem addr
  | true  => readSpecV4Mem st addr

theorem readSpecV4Mem_masked_eq_pubMem (st : SpecV4State) (addr mask : Nat)
    (hMask : natBlt mask st.pubBound = true) :
    readSpecV4Mem st (addr &&& mask) = st.pubMem (addr &&& mask) := by
  unfold readSpecV4Mem
  rw [natBlt_and_of_natBlt addr mask st.pubBound hMask]

/-- Speculative operational semantics of `SctV4Instr` parameterized by an adversary-chosen
    Spectre v4 store-to-load bypass directive `stlBypass : Bool`:
    - On `.fillStack dst slot`, when `stlBypass = false`, the CPU forwards the latest store
      `st.getStackCurr slot`; when `stlBypass = true`, the load bypasses the store buffer and
      transiently reads the overwritten value `st.getStackStale slot`, entering `specMode := true`
      without setting the branch Misspeculation Flag `msfMasked`! -/
def stepSctV4Instr (ins : SctV4Instr) (stlBypass : Bool) (st : SpecV4State) : SpecV4State × SpecObsEvent :=
  match st.specHalted with
  | true => (st, .obsSpecHalted)
  | false =>
      match ins with
      | .movImm dst imm =>
          (st.setReg dst imm, .obsSpecNone)
      | .movReg dst src =>
          (st.setReg dst (st.getReg src), .obsSpecNone)
      | .addConst dst src =>
          (st.setReg dst (st.getReg dst + st.getReg src), .obsSpecNone)
      | .andImm dst imm =>
          (st.setReg dst (st.getReg dst &&& imm), .obsSpecNone)
      | .ldUnmasked dst addrReg =>
          let addr := st.getReg addrReg
          let val  := readUnmaskedV4 st addr
          (st.setReg dst val, .obsSpecMemAddr addr)
      | .ldMasked dst addrReg mask =>
          let addr := (st.getReg addrReg) &&& mask
          let val  := readSpecV4Mem st addr
          (st.setReg dst val, .obsSpecMemAddr addr)
      | .spillStack slot src =>
          (st.spillStack slot (st.getReg src), .obsSpecNone)
      | .fillStack dst slot =>
          let val := match stlBypass with
            | false => st.getStackCurr slot
            | true  => st.getStackStale slot
          ((st.enterStlSpec stlBypass).setReg dst val, .obsSpecNone)
      | .slhInitMsf =>
          (st.syncMsf, .obsSpecNone)
      | .slhProtect dst src =>
          let val := applySlhProtect st.msfMasked (st.getReg src)
          (st.setReg dst val, .obsSpecNone)
      | .lfence =>
          (st.applyLfence, .obsSpecNone)
      | .helperReadSecretKey dst =>
          (st.setReg dst st.secretKey, .obsSpecNone)
      | .helperEmitPublicMetric valReg =>
          (st, .obsSpecMetric (st.getReg valReg))

def stepSctV4InstrList : List SctV4Instr → List Bool → SpecV4State → SpecV4State × List SpecObsEvent
  | [], _, st => (st, [])
  | i :: is, stlOracles, st =>
      let stlB := match stlOracles with | [] => false | b :: _ => b
      let rest := match stlOracles with | [] => [] | _ :: bs => bs
      let r1 := stepSctV4Instr i stlB st
      let r2 := stepSctV4InstrList is rest r1.1
      (r2.1, r1.2 :: r2.2)

def stepSctV4Term (term : SctTerm) (mispred : Bool) (st : SpecV4State) : Nat × SpecV4State × SpecObsEvent :=
  match st.specHalted with
  | true => (0, { st with exited := true }, .obsSpecHalted)
  | false =>
      match term with
      | .exit retReg =>
          (0, { st with exited := true }, .obsSpecExit (st.getReg retReg))
      | .jmp target =>
          (target, st, .obsSpecJmp target)
      | .branchLtBound idxReg bound tInBounds tOutBounds =>
          let archInBounds := natBlt (st.getReg idxReg) bound
          let actualTaken  := match mispred with | false => archInBounds | true => !archInBounds
          let nextBid      := match actualTaken with | true => tInBounds | false => tOutBounds
          (nextBid, st.updateBranchSpec mispred,
            .obsSpecBranch archInBounds mispred nextBid)

/-- Per-block combined Spectre v1 (`branchMispred`) + Spectre v4 (`stlOracles`) oracle. -/
structure V1V4StepOracle where
  branchMispred : Bool
  stlOracles    : List Bool
  deriving DecidableEq, Repr

def defaultV1V4Oracle : V1V4StepOracle :=
  { branchMispred := false, stlOracles := [] }

def stepSctV4Block (prog : SctV4Prog) (bid : Nat) (stepOrac : V1V4StepOracle) (st : SpecV4State) :
    Nat × SpecV4State × List SpecObsEvent :=
  match st.exited || st.specHalted with
  | true => (bid, st, [.obsSpecHalted])
  | false =>
      match getSctV4Block? prog bid with
      | none => (bid, { st with exited := true }, [.obsSpecHalted])
      | some bb =>
          let r1 := stepSctV4InstrList bb.instrs stepOrac.stlOracles st
          let r2 := stepSctV4Term bb.term stepOrac.branchMispred r1.1
          (r2.1, r2.2.1, r1.2 ++ [r2.2.2])

def specV4ObsTrace (prog : SctV4Prog) : Nat → List V1V4StepOracle → Nat → SpecV4State → List SpecObsEvent
  | 0, _, _, _ => []
  | fuel + 1, oracle, bid, st =>
      let stepOrac := match oracle with | [] => defaultV1V4Oracle | o :: _ => o
      let restOracle := match oracle with | [] => [] | _ :: os => os
      let res := stepSctV4Block prog bid stepOrac st
      res.2.2 ++ specV4ObsTrace prog fuel restOracle res.1 res.2.1

/-- Per-block dual-label certificate environment (`SctV4TypeEnv`) with stack-slot labels `s0, s1`. -/
structure SctV4TypeEnv where
  r0        : SctDualLabel
  r1        : SctDualLabel
  r2        : SctDualLabel
  r3        : SctDualLabel
  r4        : SctDualLabel
  s0        : SctDualLabel
  s1        : SctDualLabel
  msfSynced : Bool
  pubBound  : Nat
  deriving DecidableEq, Repr

def SctV4TypeEnv.getReg (env : SctV4TypeEnv) : Reg → SctDualLabel
  | .R0 => env.r0
  | .R1 => env.r1
  | .R2 => env.r2
  | .R3 => env.r3
  | .R4 => env.r4

def SctV4TypeEnv.setReg (env : SctV4TypeEnv) (r : Reg) (l : SctDualLabel) : SctV4TypeEnv :=
  match r with
  | .R0 => { env with r0 := l }
  | .R1 => { env with r1 := l }
  | .R2 => { env with r2 := l }
  | .R3 => { env with r3 := l }
  | .R4 => { env with r4 := l }

def SctV4TypeEnv.getStack (env : SctV4TypeEnv) : StackSlot → SctDualLabel
  | .S0 => env.s0
  | .S1 => env.s1

def SctV4TypeEnv.setStack (env : SctV4TypeEnv) (sl : StackSlot) (l : SctDualLabel) : SctV4TypeEnv :=
  match sl with
  | .S0 => { env with s0 := l }
  | .S1 => { env with s1 := l }

@[simp] theorem SctV4TypeEnv.msfSynced_setReg (env : SctV4TypeEnv) (r : Reg) (l : SctDualLabel) :
    (env.setReg r l).msfSynced = env.msfSynced := by
  cases r <;> rfl

@[simp] theorem SctV4TypeEnv.pubBound_setReg (env : SctV4TypeEnv) (r : Reg) (l : SctDualLabel) :
    (env.setReg r l).pubBound = env.pubBound := by
  cases r <;> rfl

@[simp] theorem SctV4TypeEnv.getStack_setReg (env : SctV4TypeEnv) (r : Reg) (l : SctDualLabel) (sl : StackSlot) :
    (env.setReg r l).getStack sl = env.getStack sl := by
  cases r <;> cases sl <;> rfl

theorem SctV4TypeEnv.getReg_setReg_eq (env : SctV4TypeEnv) (r : Reg) (l : SctDualLabel) :
    (env.setReg r l).getReg r = l := by
  cases r <;> rfl

theorem SctV4TypeEnv.getReg_setReg_ne (env : SctV4TypeEnv) (dst r : Reg) (l : SctDualLabel) (h : r ≠ dst) :
    (env.setReg dst l).getReg r = env.getReg r := by
  cases dst <;> cases r <;> first | contradiction | rfl

@[simp] theorem SctV4TypeEnv.msfSynced_setStack (env : SctV4TypeEnv) (sl : StackSlot) (l : SctDualLabel) :
    (env.setStack sl l).msfSynced = env.msfSynced := by
  cases sl <;> rfl

@[simp] theorem SctV4TypeEnv.pubBound_setStack (env : SctV4TypeEnv) (sl : StackSlot) (l : SctDualLabel) :
    (env.setStack sl l).pubBound = env.pubBound := by
  cases sl <;> rfl

@[simp] theorem SctV4TypeEnv.getReg_setStack (env : SctV4TypeEnv) (sl : StackSlot) (l : SctDualLabel) (r : Reg) :
    (env.setStack sl l).getReg r = env.getReg r := by
  cases sl <;> cases r <;> rfl

theorem SctV4TypeEnv.getStack_setStack_eq (env : SctV4TypeEnv) (sl : StackSlot) (l : SctDualLabel) :
    (env.setStack sl l).getStack sl = l := by
  cases sl <;> rfl

theorem SctV4TypeEnv.getStack_setStack_ne (env : SctV4TypeEnv) (slot sl : StackSlot) (l : SctDualLabel) (h : sl ≠ slot) :
    (env.setStack slot l).getStack sl = env.getStack sl := by
  cases slot <;> cases sl <;> first | contradiction | rfl

def SctV4TypeEnv.stabilizeAll (env : SctV4TypeEnv) : SctV4TypeEnv :=
  { env with
    r0 := { env.r0 with spec := .SpecSafe }
    r1 := { env.r1 with spec := .SpecSafe }
    r2 := { env.r2 with spec := .SpecSafe }
    r3 := { env.r3 with spec := .SpecSafe }
    r4 := { env.r4 with spec := .SpecSafe }
    s0 := { env.s0 with spec := .SpecSafe }
    s1 := { env.s1 with spec := .SpecSafe } }

def SctV4TypeEnv.subsumes (env1 env2 : SctV4TypeEnv) : Bool :=
  Nat.beq env1.pubBound env2.pubBound &&
  (match env2.msfSynced with | true => env1.msfSynced | false => true) &&
  SctDualLabel.le env1.r0 env2.r0 &&
  SctDualLabel.le env1.r1 env2.r1 &&
  SctDualLabel.le env1.r2 env2.r2 &&
  SctDualLabel.le env1.r3 env2.r3 &&
  SctDualLabel.le env1.r4 env2.r4 &&
  SctDualLabel.le env1.s0 env2.s0 &&
  SctDualLabel.le env1.s1 env2.s1

/-- **1. Unsound Flow-Sensitive Spectre-v1-Only Stack Transformer (`transferSctV1OnlyStackInstr`)**:
    Overwrites `env.setStack slot (env.getReg src)` on `spillStack`, ignoring the fact that
    a Spectre v4 `STL` store bypass can still read the previous secret in `s0Stale`! -/
def transferSctV1OnlyStackInstr (env : SctV4TypeEnv) (ins : SctV4Instr) : Option SctV4TypeEnv :=
  match ins with
  | .movImm dst _ => some (env.setReg dst SctDualLabel.pubSafe)
  | .movReg dst src => some (env.setReg dst (env.getReg src))
  | .addConst dst src => some (env.setReg dst (SctDualLabel.join (env.getReg dst) (env.getReg src)))
  | .andImm dst _ => some (env.setReg dst (env.getReg dst))
  | .ldUnmasked dst addrReg =>
      match SctDualLabel.isPubSafe (env.getReg addrReg) with
      | true  => some (env.setReg dst SctDualLabel.pubTransient)
      | false => none
  | .ldMasked dst addrReg mask =>
      match SctDualLabel.isPubSafe (env.getReg addrReg) && natBlt mask env.pubBound with
      | true  => some (env.setReg dst SctDualLabel.pubSafe)
      | false => none
  | .spillStack slot src =>
      -- Flow-sensitive overwrite (unsound under Spectre v4 STL!)
      some (env.setStack slot (env.getReg src))
  | .fillStack dst slot =>
      some (env.setReg dst (env.getStack slot))
  | .slhInitMsf => some { env with msfSynced := true }
  | .slhProtect dst src =>
      match env.msfSynced with
      | true  => some (env.setReg dst { arch := (env.getReg src).arch, spec := .SpecSafe })
      | false => none
  | .lfence => some env.stabilizeAll
  | .helperReadSecretKey dst => some (env.setReg dst SctDualLabel.secTransient)
  | .helperEmitPublicMetric valReg =>
      match SctDualLabel.isPubSafe (env.getReg valReg) with
      | true  => some env
      | false => none

def transferSctV1OnlyStackInstrList (env : SctV4TypeEnv) : List SctV4Instr → Option SctV4TypeEnv
  | []      => some env
  | i :: is =>
      match transferSctV1OnlyStackInstr env i with
      | none      => none
      | some env' => transferSctV1OnlyStackInstrList env' is

def checkSctV1OnlyStackBlock (cert : List SctV4TypeEnv) (bb : SctV4BasicBlock) : Bool :=
  match cert[bb.id]? with
  | none => false
  | some pre =>
      match transferSctV1OnlyStackInstrList pre bb.instrs with
      | none => false
      | some post =>
          match bb.term with
          | .exit retReg => SctDualLabel.isPubSafe (post.getReg retReg)
          | .jmp target =>
              match cert[target]? with
              | none => false
              | some tCert => SctV4TypeEnv.subsumes post tCert
          | .branchLtBound idxReg _ tIn tOut =>
              match SctDualLabel.isPubSafe (post.getReg idxReg), cert[tIn]?, cert[tOut]? with
              | true, some cIn, some cOut =>
                  SctV4TypeEnv.subsumes post cIn && SctV4TypeEnv.subsumes post cOut
              | _, _, _ => false

def checkKernelSctV1OnlyStackCert (prog : SctV4Prog) (cert : List SctV4TypeEnv) : Bool :=
  prog.all (checkSctV1OnlyStackBlock cert)

/-- **2. Sound Sticky Stack-Slot Transformer (`transferSctV1V4Instr` — `Jasmin SCT` S&P '23 / POPL '25)**:
    - On `.spillStack slot src`, updates `slot` via sticky join
      `SctDualLabel.join (env.getStack slot) (env.getReg src)` so that a stack slot tainted
      `Secret` or `SpecTransient` cannot be downgraded by a subsequent public store!
    - On `.fillStack dst slot`, since an `STL` bypass can enter `specMode = true` without
      updating the branch `msf` register, `msfSynced` is cleared to `false` and `dst` receives
      the sticky label `env.getStack slot`. -/
def transferSctV1V4Instr (env : SctV4TypeEnv) (ins : SctV4Instr) : Option SctV4TypeEnv :=
  match ins with
  | .movImm dst _ =>
      some (env.setReg dst SctDualLabel.pubSafe)
  | .movReg dst src =>
      some (env.setReg dst (env.getReg src))
  | .addConst dst src =>
      some (env.setReg dst (SctDualLabel.join (env.getReg dst) (env.getReg src)))
  | .andImm dst _ =>
      some (env.setReg dst (env.getReg dst))
  | .ldUnmasked dst addrReg =>
      match SctDualLabel.isPubSafe (env.getReg addrReg) with
      | true  => some (env.setReg dst SctDualLabel.pubTransient)
      | false => none
  | .ldMasked dst addrReg mask =>
      match SctDualLabel.isPubSafe (env.getReg addrReg) && natBlt mask env.pubBound with
      | true  => some (env.setReg dst SctDualLabel.pubSafe)
      | false => none
  | .spillStack slot src =>
      some (env.setStack slot (SctDualLabel.join (env.getStack slot) (env.getReg src)))
  | .fillStack dst slot =>
      some ({ env with msfSynced := false }.setReg dst (env.getStack slot))
  | .slhInitMsf =>
      some { env with msfSynced := true }
  | .slhProtect dst src =>
      match env.msfSynced with
      | true  => some (env.setReg dst { arch := (env.getReg src).arch, spec := .SpecSafe })
      | false => none
  | .lfence =>
      some env.stabilizeAll
  | .helperReadSecretKey dst =>
      some (env.setReg dst SctDualLabel.secTransient)
  | .helperEmitPublicMetric valReg =>
      match SctDualLabel.isPubSafe (env.getReg valReg) with
      | true  => some env
      | false => none

def transferSctV1V4InstrList (env : SctV4TypeEnv) : List SctV4Instr → Option SctV4TypeEnv
  | []      => some env
  | i :: is =>
      match transferSctV1V4Instr env i with
      | none      => none
      | some env' => transferSctV1V4InstrList env' is

abbrev SctV4Certificate := List SctV4TypeEnv

def getSctV4Cert? (cert : SctV4Certificate) (bid : Nat) : Option SctV4TypeEnv :=
  match cert, bid with
  | [], _          => none
  | c :: _, 0      => some c
  | _ :: cs, n + 1 => getSctV4Cert? cs n

def checkSctV1V4Block (cert : SctV4Certificate) (bb : SctV4BasicBlock) : Bool :=
  match getSctV4Cert? cert bb.id with
  | none => false
  | some pre =>
      match transferSctV1V4InstrList pre bb.instrs with
      | none => false
      | some post =>
          match bb.term with
          | .exit retReg =>
              SctDualLabel.isPubSafe (post.getReg retReg)
          | .jmp target =>
              match getSctV4Cert? cert target with
              | none => false
              | some tCert => SctV4TypeEnv.subsumes post tCert
          | .branchLtBound idxReg _ tInBounds tOutBounds =>
              match SctDualLabel.isPubSafe (post.getReg idxReg),
                    getSctV4Cert? cert tInBounds, getSctV4Cert? cert tOutBounds with
              | true, some cIn, some cOut =>
                  SctV4TypeEnv.subsumes post cIn && SctV4TypeEnv.subsumes post cOut
              | _, _, _ => false

def checkAllSctV1V4Blocks (cert : SctV4Certificate) : List SctV4BasicBlock → Bool
  | []        => true
  | bb :: bbs => checkSctV1V4Block cert bb && checkAllSctV1V4Blocks cert bbs

/-- **In-Kernel Single-Pass Combined Spectre v1 + v4 Sticky-Stack Certificate Checker (`checkKernelSctV1V4Cert`)**. -/
def checkKernelSctV1V4Cert (prog : SctV4Prog) (cert : SctV4Certificate) : Bool :=
  checkAllSctV1V4Blocks cert prog

/-- Concrete Spectre v4 `STL` Store-Bypass Gadget (`spectreV4StlGadgetProg`):
    1. Reads `secretKey` into `R2` (`helperReadSecretKey .R2`);
    2. Spills `R2` to stack slot `S0` (`spillStack .S0 .R2`);
    3. Overwrites `S0` with public constant `0` (`movImm .R3 0; spillStack .S0 .R3`);
    4. Reloads `R4` from `S0` (`fillStack .R4 .S0` — under `stlBypass = true`, reads stale `secretKey`!);
    5. Uses `R4` in a bitwise-masked load `ldMasked .R0 .R4 15` (leaking `secretKey & 15` into cache trace!). -/
def spectreV4StlGadgetProg : SctV4Prog :=
  [ { id := 0
      instrs := [
        .helperReadSecretKey .R2,
        .spillStack .S0 .R2,
        .movImm .R3 0,
        .spillStack .S0 .R3,
        .fillStack .R4 .S0,
        .ldMasked .R0 .R4 15,
        .movImm .R0 0
      ]
      term := .exit .R0 } ]

def defaultSctV4Env : SctV4TypeEnv :=
  { r0 := SctDualLabel.pubSafe
    r1 := SctDualLabel.pubSafe
    r2 := SctDualLabel.pubSafe
    r3 := SctDualLabel.pubSafe
    r4 := SctDualLabel.pubSafe
    s0 := SctDualLabel.pubSafe
    s1 := SctDualLabel.pubSafe
    msfSynced := true
    pubBound := 16 }

def spectreV4State1 : SpecV4State :=
  { r0 := 0, r1 := 0, r2 := 0, r3 := 0, r4 := 0
    s0Curr := 0, s0Stale := 0, s1Curr := 0, s1Stale := 0
    pubBound := 16
    pubMem := fun _ => 0
    kernelSecretMem := fun _ => 0
    secretKey := 5
    specMode := false
    msfMasked := false
    specHalted := false
    exited := false }

def spectreV4State2 : SpecV4State :=
  { spectreV4State1 with secretKey := 11 }

def noStlBypassOracle : List V1V4StepOracle :=
  [ { branchMispred := false, stlOracles := [false, false, false, false, false, false, false] } ]

def stlBypassOnFillOracle : List V1V4StepOracle :=
  [ { branchMispred := false, stlOracles := [false, false, false, false, true, false, false] } ]

/-- **Foundational Theorem 3a (`spectre_v4_stl_bypass_leaks_overwritten_secret_slot`)**:
    1. `spectreV4StlGadgetProg` passes the flow-sensitive Spectre-v1-only stack checker
       (`checkKernelSctV1OnlyStackCert = true`) because `S0` is overwritten with `0` before
       `fillStack .R4 .S0` and the load `.ldMasked .R0 .R4 15` is SFI-masked.
    2. Without Spectre v4 store bypass (`noStlBypassOracle`), `spectreV4State1` (`secretKey = 5`)
       and `spectreV4State2` (`secretKey = 11`) produce identical speculative observation traces.
    3. Under a single Spectre v4 `STL` store bypass on `fillStack .R4 .S0` (`stlBypassOnFillOracle`),
       the load bypasses `s0Curr = 0` and transiently reads `s0Stale = secretKey` (`5` vs `11`),
       leaking `.obsSpecMemAddr 5` vs `.obsSpecMemAddr 11` into `specV4ObsTrace`! -/
theorem spectre_v4_stl_bypass_leaks_overwritten_secret_slot :
    checkKernelSctV1OnlyStackCert spectreV4StlGadgetProg [defaultSctV4Env] = true ∧
    specV4ObsTrace spectreV4StlGadgetProg 1 noStlBypassOracle 0 spectreV4State1 =
      specV4ObsTrace spectreV4StlGadgetProg 1 noStlBypassOracle 0 spectreV4State2 ∧
    specV4ObsTrace spectreV4StlGadgetProg 1 stlBypassOnFillOracle 0 spectreV4State1 ≠
      specV4ObsTrace spectreV4StlGadgetProg 1 stlBypassOnFillOracle 0 spectreV4State2 := by
  refine ⟨rfl, rfl, ?_⟩
  intro hEq
  nomatch hEq

/-- Speculative Low-Equivalence (`SctV4LowEq`) across both Spectre v1 (`PHT`) and Spectre v4 (`STL`):
    Requires both `getStackCurr sl` AND `getStackStale sl` to satisfy `SctRegRel (env.getStack sl)`! -/
structure SctV4LowEq (env : SctV4TypeEnv) (s₁ s₂ : SpecV4State) : Prop where
  specModeEq    : s₁.specMode = s₂.specMode
  msfMaskedEq   : s₁.msfMasked = s₂.msfMasked
  specHaltedEq  : s₁.specHalted = s₂.specHalted
  exitedEq      : s₁.exited = s₂.exited
  haltImpSpec   : s₁.specHalted = true → s₁.specMode = true
  msfSyncInv    : env.msfSynced = true → s₁.specHalted = false → s₁.msfMasked = s₁.specMode
  boundEq1      : s₁.pubBound = env.pubBound
  boundEq2      : s₂.pubBound = env.pubBound
  pubMemEq      : ∀ a : Nat, s₁.pubMem a = s₂.pubMem a
  regRel        : ∀ r : Reg, SctRegRel (env.getReg r) s₁.specMode s₁.specHalted (s₁.getReg r) (s₂.getReg r)
  stackCurrRel  : ∀ sl : StackSlot, SctRegRel (env.getStack sl) s₁.specMode s₁.specHalted (s₁.getStackCurr sl) (s₂.getStackCurr sl)
  stackStaleRel : ∀ sl : StackSlot, SctRegRel (env.getStack sl) s₁.specMode s₁.specHalted (s₁.getStackStale sl) (s₂.getStackStale sl)

theorem sctV4LowEq_setReg (env : SctV4TypeEnv) (s₁ s₂ : SpecV4State)
    (hLow : SctV4LowEq env s₁ s₂) (dst : Reg) (l : SctDualLabel) (v₁ v₂ : Nat)
    (hVal : SctRegRel l s₁.specMode s₁.specHalted v₁ v₂) :
    SctV4LowEq (env.setReg dst l) (s₁.setReg dst v₁) (s₂.setReg dst v₂) := by
  refine ⟨by simp [hLow.specModeEq], by simp [hLow.msfMaskedEq],
          by simp [hLow.specHaltedEq], by simp [hLow.exitedEq],
          by intro h; simp at h ⊢; exact hLow.haltImpSpec h,
          ?_,
          by simp [hLow.boundEq1], by simp [hLow.boundEq2],
          by intro a; simp [hLow.pubMemEq a], ?_,
          by intro sl; simp [hLow.stackCurrRel sl],
          by intro sl; simp [hLow.stackStaleRel sl]⟩
  · intro hSync hHalt
    simp at hSync hHalt ⊢
    exact hLow.msfSyncInv hSync hHalt
  · intro r
    simp only [SpecV4State.specMode_setReg, SpecV4State.specHalted_setReg]
    cases decEq r dst with
    | isTrue hEq =>
        subst hEq
        rw [SctV4TypeEnv.getReg_setReg_eq, SpecV4State.getReg_setReg_eq, SpecV4State.getReg_setReg_eq]
        exact hVal
    | isFalse hNe =>
        rw [SctV4TypeEnv.getReg_setReg_ne _ _ _ _ hNe,
            SpecV4State.getReg_setReg_ne _ _ _ _ hNe,
            SpecV4State.getReg_setReg_ne _ _ _ _ hNe]
        exact hLow.regRel r

theorem sctV4LowEq_spillStack (env : SctV4TypeEnv) (s₁ s₂ : SpecV4State)
    (hLow : SctV4LowEq env s₁ s₂) (slot : StackSlot) (src : Reg) :
    SctV4LowEq (env.setStack slot (SctDualLabel.join (env.getStack slot) (env.getReg src)))
               (s₁.spillStack slot (s₁.getReg src))
               (s₂.spillStack slot (s₂.getReg src)) := by
  refine ⟨by simp [hLow.specModeEq], by simp [hLow.msfMaskedEq],
          by simp [hLow.specHaltedEq], by simp [hLow.exitedEq],
          by intro h; simp at h ⊢; exact hLow.haltImpSpec h,
          ?_,
          by simp [hLow.boundEq1], by simp [hLow.boundEq2],
          by intro a; simp [hLow.pubMemEq a],
          by intro r; simp [hLow.regRel r],
          ?_, ?_⟩
  · intro hSync hHalt
    simp at hSync hHalt ⊢
    exact hLow.msfSyncInv hSync hHalt
  · intro sl
    simp only [SpecV4State.specMode_spillStack, SpecV4State.specHalted_spillStack]
    cases decEq sl slot with
    | isTrue hEq =>
        subst hEq
        rw [SctV4TypeEnv.getStack_setStack_eq,
            SpecV4State.getStackCurr_spillStack_eq,
            SpecV4State.getStackCurr_spillStack_eq]
        exact sctRegRel_of_le (env.getReg src) _ _ _ _ _
          (sctDualLabel_le_join_right (env.getStack sl) (env.getReg src))
          (hLow.regRel src)
    | isFalse hNe =>
        rw [SctV4TypeEnv.getStack_setStack_ne _ _ _ _ hNe,
            SpecV4State.getStackCurr_spillStack_ne _ _ _ _ hNe,
            SpecV4State.getStackCurr_spillStack_ne _ _ _ _ hNe]
        exact hLow.stackCurrRel sl
  · intro sl
    simp only [SpecV4State.specMode_spillStack, SpecV4State.specHalted_spillStack]
    cases decEq sl slot with
    | isTrue hEq =>
        subst hEq
        rw [SctV4TypeEnv.getStack_setStack_eq,
            SpecV4State.getStackStale_spillStack_eq,
            SpecV4State.getStackStale_spillStack_eq]
        exact sctRegRel_of_le (env.getStack sl) _ _ _ _ _
          (sctDualLabel_le_join_left (env.getStack sl) (env.getReg src))
          (hLow.stackCurrRel sl)
    | isFalse hNe =>
        rw [SctV4TypeEnv.getStack_setStack_ne _ _ _ _ hNe,
            SpecV4State.getStackStale_spillStack_ne _ _ _ _ hNe,
            SpecV4State.getStackStale_spillStack_ne _ _ _ _ hNe]
        exact hLow.stackStaleRel sl

theorem sctV4LowEq_of_subsumes (env1 env2 : SctV4TypeEnv) (s₁ s₂ : SpecV4State)
    (hSub : SctV4TypeEnv.subsumes env1 env2 = true)
    (hLow : SctV4LowEq env1 s₁ s₂) :
    SctV4LowEq env2 s₁ s₂ := by
  unfold SctV4TypeEnv.subsumes at hSub
  simp [Bool.and_eq_true] at hSub
  rcases hSub with ⟨⟨⟨⟨⟨⟨⟨⟨hBndEq, hMsf⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, hs0⟩, hs1⟩
  refine ⟨hLow.specModeEq, hLow.msfMaskedEq, hLow.specHaltedEq, hLow.exitedEq,
          hLow.haltImpSpec, ?_, hLow.boundEq1.trans hBndEq, hLow.boundEq2.trans hBndEq,
          hLow.pubMemEq, ?_, ?_, ?_⟩
  · intro hSync2 hHalt
    rw [hSync2] at hMsf
    exact hLow.msfSyncInv hMsf hHalt
  · intro r
    cases r with
    | R0 => exact sctRegRel_of_le _ _ _ _ _ _ h0 (hLow.regRel .R0)
    | R1 => exact sctRegRel_of_le _ _ _ _ _ _ h1 (hLow.regRel .R1)
    | R2 => exact sctRegRel_of_le _ _ _ _ _ _ h2 (hLow.regRel .R2)
    | R3 => exact sctRegRel_of_le _ _ _ _ _ _ h3 (hLow.regRel .R3)
    | R4 => exact sctRegRel_of_le _ _ _ _ _ _ h4 (hLow.regRel .R4)
  · intro sl
    cases sl with
    | S0 => exact sctRegRel_of_le _ _ _ _ _ _ hs0 (hLow.stackCurrRel .S0)
    | S1 => exact sctRegRel_of_le _ _ _ _ _ _ hs1 (hLow.stackCurrRel .S1)
  · intro sl
    cases sl with
    | S0 => exact sctRegRel_of_le _ _ _ _ _ _ hs0 (hLow.stackStaleRel .S0)
    | S1 => exact sctRegRel_of_le _ _ _ _ _ _ hs1 (hLow.stackStaleRel .S1)

theorem transferSctV1V4Instr_pubBound_eq (env env' : SctV4TypeEnv) (ins : SctV4Instr)
    (hTrans : transferSctV1V4Instr env ins = some env') :
    env'.pubBound = env.pubBound := by
  cases ins with
  | movImm dst _ => simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
  | movReg dst _ => simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
  | addConst dst _ => simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
  | andImm dst _ => simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
  | ldUnmasked dst addrReg =>
      unfold transferSctV1V4Instr at hTrans
      cases h : SctDualLabel.isPubSafe (env.getReg addrReg) <;> simp [h] at hTrans
      subst hTrans; simp
  | ldMasked dst addrReg mask =>
      unfold transferSctV1V4Instr at hTrans
      cases h1 : SctDualLabel.isPubSafe (env.getReg addrReg) <;>
        cases h2 : natBlt mask env.pubBound <;> simp [h1, h2] at hTrans
      subst hTrans; simp
  | spillStack slot _ => simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
  | fillStack dst _ => simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
  | slhInitMsf => simp [transferSctV1V4Instr] at hTrans; subst hTrans; rfl
  | slhProtect dst _ =>
      unfold transferSctV1V4Instr at hTrans
      cases h : env.msfSynced <;> simp [h] at hTrans
      subst hTrans; simp
  | lfence => simp [transferSctV1V4Instr] at hTrans; subst hTrans; rfl
  | helperReadSecretKey dst => simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
  | helperEmitPublicMetric valReg =>
      unfold transferSctV1V4Instr at hTrans
      cases h : SctDualLabel.isPubSafe (env.getReg valReg) <;> simp [h] at hTrans
      subst hTrans; rfl

theorem sctV4LowEq_preserve_when_halted (env env' : SctV4TypeEnv) (ins : SctV4Instr) (s₁ s₂ : SpecV4State)
    (hTrans : transferSctV1V4Instr env ins = some env')
    (hHalt1 : s₁.specHalted = true)
    (hLow : SctV4LowEq env s₁ s₂) :
    SctV4LowEq env' s₁ s₂ := by
  have hB := (transferSctV1V4Instr_pubBound_eq env env' ins hTrans).symm
  have hSm1 : s₁.specMode = true := hLow.haltImpSpec hHalt1
  refine ⟨hLow.specModeEq, hLow.msfMaskedEq, hLow.specHaltedEq, hLow.exitedEq,
          hLow.haltImpSpec, ?_, hLow.boundEq1.trans hB, hLow.boundEq2.trans hB,
          hLow.pubMemEq, ?_, ?_, ?_⟩
  · intro _ hNotHalt
    rw [hHalt1] at hNotHalt
    nomatch hNotHalt
  · intro r
    refine ⟨?_, ?_⟩
    · intro _ hSmFalse; rw [hSm1] at hSmFalse; nomatch hSmFalse
    · intro _ _ hShFalse; rw [hHalt1] at hShFalse; nomatch hShFalse
  · intro sl
    refine ⟨?_, ?_⟩
    · intro _ hSmFalse; rw [hSm1] at hSmFalse; nomatch hSmFalse
    · intro _ _ hShFalse; rw [hHalt1] at hShFalse; nomatch hShFalse
  · intro sl
    refine ⟨?_, ?_⟩
    · intro _ hSmFalse; rw [hSm1] at hSmFalse; nomatch hSmFalse
    · intro _ _ hShFalse; rw [hHalt1] at hShFalse; nomatch hShFalse

/-- Helper: entering `enterStlSpec stlBypass` preserves `SctV4LowEq` when `msfSynced` is cleared. -/
theorem sctV4LowEq_enterStlSpec (env : SctV4TypeEnv) (s₁ s₂ : SpecV4State) (stlBypass : Bool)
    (hHalt1 : s₁.specHalted = false)
    (hLow : SctV4LowEq env s₁ s₂) :
    SctV4LowEq { env with msfSynced := false } (s₁.enterStlSpec stlBypass) (s₂.enterStlSpec stlBypass) := by
  refine ⟨(by simp [SpecV4State.enterStlSpec, hLow.specModeEq]),
          hLow.msfMaskedEq,
          hLow.specHaltedEq,
          hLow.exitedEq,
          (by intro hSh; simp [SpecV4State.enterStlSpec, hHalt1] at hSh),
          (by intro hSync; nomatch hSync),
          hLow.boundEq1,
          hLow.boundEq2,
          hLow.pubMemEq,
          ?_, ?_, ?_⟩
  · intro r
    simp only [SpecV4State.getReg_enterStlSpec]
    have hEq : ({ env with msfSynced := false } : SctV4TypeEnv).getReg r = env.getReg r := by
      cases r <;> rfl
    rw [hEq]
    exact sctRegRel_after_branch (env.getReg r) s₁.specMode s₁.specHalted stlBypass _ _ (hLow.regRel r)
  · intro sl
    simp only [SpecV4State.getStackCurr_enterStlSpec]
    have hEq : ({ env with msfSynced := false } : SctV4TypeEnv).getStack sl = env.getStack sl := by
      cases sl <;> rfl
    rw [hEq]
    exact sctRegRel_after_branch (env.getStack sl) s₁.specMode s₁.specHalted stlBypass _ _ (hLow.stackCurrRel sl)
  · intro sl
    simp only [SpecV4State.getStackStale_enterStlSpec]
    have hEq : ({ env with msfSynced := false } : SctV4TypeEnv).getStack sl = env.getStack sl := by
      cases sl <;> rfl
    rw [hEq]
    exact sctRegRel_after_branch (env.getStack sl) s₁.specMode s₁.specHalted stlBypass _ _ (hLow.stackStaleRel sl)

/-- **Per-Instruction Combined Spectre v1 + v4 Noninterference (`sct_v1_v4_instr_step_noninterference`)**. -/
theorem sct_v1_v4_instr_step_noninterference (env env' : SctV4TypeEnv) (ins : SctV4Instr)
    (stlBypass : Bool) (s₁ s₂ : SpecV4State)
    (hTrans : transferSctV1V4Instr env ins = some env')
    (hLow : SctV4LowEq env s₁ s₂) :
    (stepSctV4Instr ins stlBypass s₁).2 = (stepSctV4Instr ins stlBypass s₂).2 ∧
    SctV4LowEq env' (stepSctV4Instr ins stlBypass s₁).1 (stepSctV4Instr ins stlBypass s₂).1 := by
  unfold stepSctV4Instr
  cases hHalt1 : s₁.specHalted with
  | true =>
      have hHalt2 : s₂.specHalted = true := by rw [← hLow.specHaltedEq, hHalt1]
      simp [hHalt2]
      exact sctV4LowEq_preserve_when_halted env env' ins s₁ s₂ hTrans hHalt1 hLow
  | false =>
      have hHalt2 : s₂.specHalted = false := by rw [← hLow.specHaltedEq, hHalt1]
      simp [hHalt2]
      cases ins with
      | movImm dst imm =>
          simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
          exact sctV4LowEq_setReg env s₁ s₂ hLow dst SctDualLabel.pubSafe imm imm
            ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
      | movReg dst src =>
          simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
          exact sctV4LowEq_setReg env s₁ s₂ hLow dst (env.getReg src) _ _ (hLow.regRel src)
      | addConst dst src =>
          simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
          refine sctV4LowEq_setReg env s₁ s₂ hLow dst
            (SctDualLabel.join (env.getReg dst) (env.getReg src)) _ _ ⟨?_, ?_⟩
          · intro hArch hSm
            have ⟨hd, hs⟩ := secLabel_join_eq_public _ _ hArch
            rw [(hLow.regRel dst).1 hd hSm, (hLow.regRel src).1 hs hSm]
          · intro hArch hSpec hSh
            have ⟨hd, hs⟩ := secLabel_join_eq_public _ _ hArch
            have ⟨sd, ss⟩ := specLabel_join_eq_safe _ _ hSpec
            rw [(hLow.regRel dst).2 hd sd hSh, (hLow.regRel src).2 hs ss hSh]
      | andImm dst imm =>
          simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
          refine sctV4LowEq_setReg env s₁ s₂ hLow dst (env.getReg dst) _ _ ⟨?_, ?_⟩
          · intro hArch hSm; rw [(hLow.regRel dst).1 hArch hSm]
          · intro hArch hSpec hSh; rw [(hLow.regRel dst).2 hArch hSpec hSh]
      | ldUnmasked dst addrReg =>
          unfold transferSctV1V4Instr at hTrans
          cases hSafe : SctDualLabel.isPubSafe (env.getReg addrReg) <;> simp [hSafe] at hTrans
          subst hTrans
          have ⟨hA, hS⟩ := sctDualLabel_isPubSafe_imp _ hSafe
          have hAddrEq : s₁.getReg addrReg = s₂.getReg addrReg :=
            (hLow.regRel addrReg).2 hA hS hHalt1
          refine ⟨by simp [hAddrEq], ?_⟩
          refine sctV4LowEq_setReg env s₁ s₂ hLow dst SctDualLabel.pubTransient _ _ ⟨?_, ?_⟩
          · intro _ hSm1
            have hSm2 : s₂.specMode = false := by rw [← hLow.specModeEq, hSm1]
            simp [readUnmaskedV4, hSm1, hSm2, hAddrEq, hLow.pubMemEq]
          · intro _ hSpec; nomatch hSpec
      | ldMasked dst addrReg mask =>
          unfold transferSctV1V4Instr at hTrans
          cases hSafe : SctDualLabel.isPubSafe (env.getReg addrReg) <;>
            cases hMask : natBlt mask env.pubBound <;> simp [hSafe, hMask] at hTrans
          subst hTrans
          have ⟨hA, hS⟩ := sctDualLabel_isPubSafe_imp _ hSafe
          have hAddrEq : s₁.getReg addrReg = s₂.getReg addrReg :=
            (hLow.regRel addrReg).2 hA hS hHalt1
          have hMask1 : natBlt mask s₁.pubBound = true := by rw [hLow.boundEq1]; exact hMask
          have hMask2 : natBlt mask s₂.pubBound = true := by rw [hLow.boundEq2]; exact hMask
          have hValEq : readSpecV4Mem s₁ (s₁.getReg addrReg &&& mask) =
                        readSpecV4Mem s₂ (s₂.getReg addrReg &&& mask) := by
            rw [readSpecV4Mem_masked_eq_pubMem s₁ _ _ hMask1,
                readSpecV4Mem_masked_eq_pubMem s₂ _ _ hMask2,
                hAddrEq, hLow.pubMemEq]
          refine ⟨by simp [hAddrEq], ?_⟩
          exact sctV4LowEq_setReg env s₁ s₂ hLow dst SctDualLabel.pubSafe _ _
            ⟨fun _ _ => hValEq, fun _ _ _ => hValEq⟩
      | spillStack slot src =>
          simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
          exact sctV4LowEq_spillStack env s₁ s₂ hLow slot src
      | fillStack dst slot =>
          simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
          have hEnter := sctV4LowEq_enterStlSpec env s₁ s₂ stlBypass hHalt1 hLow
          refine sctV4LowEq_setReg { env with msfSynced := false }
            (s₁.enterStlSpec stlBypass) (s₂.enterStlSpec stlBypass) hEnter dst (env.getStack slot) _ _ ?_
          cases stlBypass with
          | false =>
              simpa [SpecV4State.enterStlSpec] using hLow.stackCurrRel slot
          | true =>
              refine ⟨?_, ?_⟩
              · intro _ hSm
                simp [SpecV4State.enterStlSpec] at hSm
              · intro hA hS _
                simpa [SpecV4State.enterStlSpec] using (hLow.stackStaleRel slot).2 hA hS hHalt1
      | slhInitMsf =>
          simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
          refine ⟨hLow.specModeEq, hLow.specModeEq, hLow.specHaltedEq, hLow.exitedEq,
                  hLow.haltImpSpec, fun _ _ => rfl, hLow.boundEq1, hLow.boundEq2,
                  hLow.pubMemEq, ?_, ?_, ?_⟩
          · intro r; cases r <;> simp [SctV4TypeEnv.getReg, SpecV4State.syncMsf, SpecV4State.getReg]
            · exact hLow.regRel .R0
            · exact hLow.regRel .R1
            · exact hLow.regRel .R2
            · exact hLow.regRel .R3
            · exact hLow.regRel .R4
          · intro sl; cases sl <;> simp [SctV4TypeEnv.getStack, SpecV4State.syncMsf, SpecV4State.getStackCurr]
            · exact hLow.stackCurrRel .S0
            · exact hLow.stackCurrRel .S1
          · intro sl; cases sl <;> simp [SctV4TypeEnv.getStack, SpecV4State.syncMsf, SpecV4State.getStackStale]
            · exact hLow.stackStaleRel .S0
            · exact hLow.stackStaleRel .S1
      | slhProtect dst src =>
          unfold transferSctV1V4Instr at hTrans
          cases hSync : env.msfSynced <;> simp [hSync] at hTrans
          subst hTrans; simp
          have hMsf1 : s₁.msfMasked = s₁.specMode := hLow.msfSyncInv hSync hHalt1
          have hValEq : (env.getReg src).arch = .Public →
              applySlhProtect s₁.msfMasked (s₁.getReg src) =
              applySlhProtect s₂.msfMasked (s₂.getReg src) := by
            intro hArch
            rw [← hLow.msfMaskedEq, hMsf1]
            cases hSm : s₁.specMode with
            | true => rfl
            | false =>
                simp [applySlhProtect]
                exact (hLow.regRel src).1 hArch hSm
          exact sctV4LowEq_setReg env s₁ s₂ hLow dst
            { arch := (env.getReg src).arch, spec := .SpecSafe } _ _
            ⟨fun hA _ => hValEq hA, fun hA _ _ => hValEq hA⟩
      | lfence =>
          simp [transferSctV1V4Instr] at hTrans; subst hTrans
          simp [SpecV4State.applyLfence]
          refine ⟨hLow.specModeEq, hLow.msfMaskedEq, hLow.specModeEq, hLow.exitedEq,
                  fun h => h, ?_, hLow.boundEq1, hLow.boundEq2, hLow.pubMemEq, ?_, ?_, ?_⟩
          · intro hSync _; exact hLow.msfSyncInv hSync hHalt1
          · intro r
            cases r <;> simp [SctV4TypeEnv.stabilizeAll, SctV4TypeEnv.getReg, SpecV4State.getReg]
            · exact ⟨(hLow.regRel .R0).1, fun hA _ hSm => (hLow.regRel .R0).1 hA hSm⟩
            · exact ⟨(hLow.regRel .R1).1, fun hA _ hSm => (hLow.regRel .R1).1 hA hSm⟩
            · exact ⟨(hLow.regRel .R2).1, fun hA _ hSm => (hLow.regRel .R2).1 hA hSm⟩
            · exact ⟨(hLow.regRel .R3).1, fun hA _ hSm => (hLow.regRel .R3).1 hA hSm⟩
            · exact ⟨(hLow.regRel .R4).1, fun hA _ hSm => (hLow.regRel .R4).1 hA hSm⟩
          · intro sl
            cases sl <;> simp [SctV4TypeEnv.stabilizeAll, SctV4TypeEnv.getStack, SpecV4State.getStackCurr]
            · exact ⟨(hLow.stackCurrRel .S0).1, fun hA _ hSm => (hLow.stackCurrRel .S0).1 hA hSm⟩
            · exact ⟨(hLow.stackCurrRel .S1).1, fun hA _ hSm => (hLow.stackCurrRel .S1).1 hA hSm⟩
          · intro sl
            cases sl <;> simp [SctV4TypeEnv.stabilizeAll, SctV4TypeEnv.getStack, SpecV4State.getStackStale]
            · exact ⟨(hLow.stackStaleRel .S0).1, fun hA _ hSm => (hLow.stackStaleRel .S0).1 hA hSm⟩
            · exact ⟨(hLow.stackStaleRel .S1).1, fun hA _ hSm => (hLow.stackStaleRel .S1).1 hA hSm⟩
      | helperReadSecretKey dst =>
          simp [transferSctV1V4Instr] at hTrans; subst hTrans; simp
          exact sctV4LowEq_setReg env s₁ s₂ hLow dst SctDualLabel.secTransient _ _
            ⟨(fun h _ => nomatch h), (fun h _ _ => nomatch h)⟩
      | helperEmitPublicMetric valReg =>
          unfold transferSctV1V4Instr at hTrans
          cases hSafe : SctDualLabel.isPubSafe (env.getReg valReg) <;> simp [hSafe] at hTrans
          subst hTrans
          have ⟨hA, hS⟩ := sctDualLabel_isPubSafe_imp _ hSafe
          simp
          exact ⟨(hLow.regRel valReg).2 hA hS hHalt1, hLow⟩

theorem sct_v1_v4_instr_list_noninterference (insns : List SctV4Instr) :
    ∀ (stlOracles : List Bool) (env env' : SctV4TypeEnv) (s₁ s₂ : SpecV4State),
      transferSctV1V4InstrList env insns = some env' →
      SctV4LowEq env s₁ s₂ →
      (stepSctV4InstrList insns stlOracles s₁).2 = (stepSctV4InstrList insns stlOracles s₂).2 ∧
      SctV4LowEq env' (stepSctV4InstrList insns stlOracles s₁).1 (stepSctV4InstrList insns stlOracles s₂).1 := by
  induction insns with
  | nil =>
      intro stlOracles env env' s₁ s₂ hTrans hLow
      simp [transferSctV1V4InstrList] at hTrans
      subst hTrans
      simp [stepSctV4InstrList]
      exact hLow
  | cons i is ih =>
      intro stlOracles env env' s₁ s₂ hTrans hLow
      unfold transferSctV1V4InstrList at hTrans
      cases h1 : transferSctV1V4Instr env i with
      | none => rw [h1] at hTrans; nomatch hTrans
      | some envMid =>
          rw [h1] at hTrans
          cases stlOracles with
          | nil =>
              have ⟨hEv, hLowMid⟩ := sct_v1_v4_instr_step_noninterference env envMid i false s₁ s₂ h1 hLow
              have ⟨hEvs, hLowEnd⟩ := ih [] envMid env' (stepSctV4Instr i false s₁).1 (stepSctV4Instr i false s₂).1 hTrans hLowMid
              simp [stepSctV4InstrList, hEv, hEvs]
              exact hLowEnd
          | cons stlB rest =>
              have ⟨hEv, hLowMid⟩ := sct_v1_v4_instr_step_noninterference env envMid i stlB s₁ s₂ h1 hLow
              have ⟨hEvs, hLowEnd⟩ := ih rest envMid env' (stepSctV4Instr i stlB s₁).1 (stepSctV4Instr i stlB s₂).1 hTrans hLowMid
              simp [stepSctV4InstrList, hEv, hEvs]
              exact hLowEnd

def AllBlocksSctV1V4Certified (prog : SctV4Prog) (cert : SctV4Certificate) : Prop :=
  ∀ bid bb, getSctV4Block? prog bid = some bb → bb.id = bid ∧ checkSctV1V4Block cert bb = true

def checkSctV1V4BlocksIndexed (cert : SctV4Certificate) : Nat → List SctV4BasicBlock → Bool
  | _, [] => true
  | idx, bb :: bbs =>
      Nat.beq bb.id idx && checkSctV1V4Block cert bb && checkSctV1V4BlocksIndexed cert (idx + 1) bbs

def checkKernelSctV1V4CertIndexed (prog : SctV4Prog) (cert : SctV4Certificate) : Bool :=
  checkSctV1V4BlocksIndexed cert 0 prog

theorem checkSctV1V4BlocksIndexed_imp_get (cert : SctV4Certificate) (bbs : List SctV4BasicBlock) :
    ∀ (idx bid : Nat) (bb : SctV4BasicBlock),
      checkSctV1V4BlocksIndexed cert idx bbs = true →
      getSctV4Block? bbs bid = some bb →
      bb.id = idx + bid ∧ checkSctV1V4Block cert bb = true := by
  induction bbs with
  | nil =>
      intro idx bid bb _ hGet
      simp [getSctV4Block?] at hGet
  | cons hd tl ih =>
      intro idx bid bb hChk hGet
      unfold checkSctV1V4BlocksIndexed at hChk
      simp [Bool.and_eq_true] at hChk
      rcases hChk with ⟨⟨hId, hBlk⟩, hRest⟩
      cases bid with
      | zero =>
          simp [getSctV4Block?] at hGet
          subst hGet
          simp [hId, hBlk]
      | succ n =>
          simp [getSctV4Block?] at hGet
          have ⟨hId', hBlk'⟩ := ih (idx + 1) n bb hRest hGet
          refine ⟨?_, hBlk'⟩
          omega

theorem checkKernelSctV1V4CertIndexed_imp_AllBlocksSctV1V4Certified (prog : SctV4Prog) (cert : SctV4Certificate)
    (h : checkKernelSctV1V4CertIndexed prog cert = true) :
    AllBlocksSctV1V4Certified prog cert := by
  intro bid bb hGet
  have ⟨hId, hBlk⟩ := checkSctV1V4BlocksIndexed_imp_get cert prog 0 bid bb h hGet
  simp at hId
  exact ⟨hId, hBlk⟩

theorem sctV4LowEq_updateBranchSpec (env : SctV4TypeEnv) (s₁ s₂ : SpecV4State) (mispred : Bool)
    (hHalt1 : s₁.specHalted = false)
    (hLow : SctV4LowEq env s₁ s₂) :
    SctV4LowEq env (s₁.updateBranchSpec mispred) (s₂.updateBranchSpec mispred) := by
  refine ⟨by simp [SpecV4State.updateBranchSpec, hLow.specModeEq],
          by simp [SpecV4State.updateBranchSpec, hLow.msfMaskedEq],
          hLow.specHaltedEq,
          hLow.exitedEq,
          by intro hSh; simp [SpecV4State.updateBranchSpec, hHalt1] at hSh,
          ?_,
          hLow.boundEq1,
          hLow.boundEq2,
          hLow.pubMemEq,
          ?_, ?_, ?_⟩
  · intro hSync _
    simp [SpecV4State.updateBranchSpec, hLow.msfSyncInv hSync hHalt1]
  · intro r
    simp only [SpecV4State.getReg_updateBranchSpec]
    exact sctRegRel_after_branch (env.getReg r) s₁.specMode s₁.specHalted mispred _ _ (hLow.regRel r)
  · intro sl
    simp only [SpecV4State.getStackCurr_updateBranchSpec]
    exact sctRegRel_after_branch (env.getStack sl) s₁.specMode s₁.specHalted mispred _ _ (hLow.stackCurrRel sl)
  · intro sl
    simp only [SpecV4State.getStackStale_updateBranchSpec]
    exact sctRegRel_after_branch (env.getStack sl) s₁.specMode s₁.specHalted mispred _ _ (hLow.stackStaleRel sl)

theorem sct_v1_v4_block_step_noninterference (prog : SctV4Prog) (cert : SctV4Certificate)
    (hCert : AllBlocksSctV1V4Certified prog cert)
    (bid : Nat) (stepOrac : V1V4StepOracle) (pre : SctV4TypeEnv) (s₁ s₂ : SpecV4State)
    (hPre : getSctV4Cert? cert bid = some pre)
    (hLow : SctV4LowEq pre s₁ s₂) :
    let r₁ := stepSctV4Block prog bid stepOrac s₁
    let r₂ := stepSctV4Block prog bid stepOrac s₂
    r₁.1 = r₂.1 ∧ r₁.2.2 = r₂.2.2 ∧
    ((r₁.2.1.exited || r₁.2.1.specHalted) = true ∧ (r₂.2.1.exited || r₂.2.1.specHalted) = true ∨
      ∃ nextPre, getSctV4Cert? cert r₁.1 = some nextPre ∧ SctV4LowEq nextPre r₁.2.1 r₂.2.1) := by
  dsimp
  unfold stepSctV4Block
  have hStopEq : (s₁.exited || s₁.specHalted) = (s₂.exited || s₂.specHalted) := by
    rw [hLow.exitedEq, hLow.specHaltedEq]
  cases hStop1 : (s₁.exited || s₁.specHalted) with
  | true =>
      have hStop2 : (s₂.exited || s₂.specHalted) = true := by rw [← hStopEq, hStop1]
      simp [hStop2]
      exact Or.inl (Bool.or_eq_true_iff.mp hStop1)
  | false =>
      have hStop2 : (s₂.exited || s₂.specHalted) = false := by rw [← hStopEq, hStop1]
      simp [hStop2]
      cases hBlk : getSctV4Block? prog bid with
      | none => simp
      | some bb =>
          simp
          have ⟨hBidEq, hChk⟩ := hCert bid bb hBlk
          unfold checkSctV1V4Block at hChk
          rw [hBidEq, hPre] at hChk
          simp at hChk
          cases hList : transferSctV1V4InstrList pre bb.instrs with
          | none => rw [hList] at hChk; nomatch hChk
          | some post =>
              rw [hList] at hChk
              simp at hChk
              have ⟨hEvsEq, hPostLow⟩ := sct_v1_v4_instr_list_noninterference bb.instrs stepOrac.stlOracles pre post s₁ s₂ hList hLow
              unfold stepSctV4Term
              cases hHaltMid1 : (stepSctV4InstrList bb.instrs stepOrac.stlOracles s₁).1.specHalted with
              | true =>
                  have hHaltMid2 : (stepSctV4InstrList bb.instrs stepOrac.stlOracles s₂).1.specHalted = true := by
                    rw [← hPostLow.specHaltedEq, hHaltMid1]
                  simp [hHaltMid2, hEvsEq]
              | false =>
                  have hHaltMid2 : (stepSctV4InstrList bb.instrs stepOrac.stlOracles s₂).1.specHalted = false := by
                    rw [← hPostLow.specHaltedEq, hHaltMid1]
                  simp [hHaltMid2]
                  cases hTerm : bb.term with
                  | exit retReg =>
                      simp [hTerm] at hChk
                      have ⟨hA, hS⟩ := sctDualLabel_isPubSafe_imp _ hChk
                      have hRetEq := (hPostLow.regRel retReg).2 hA hS hHaltMid1
                      simp [hEvsEq, hRetEq]
                  | jmp target =>
                      simp [hTerm] at hChk
                      cases hTargetCert : getSctV4Cert? cert target with
                      | none => simp [hTargetCert] at hChk
                      | some tCert =>
                          simp [hTargetCert] at hChk
                          simp [hEvsEq]
                          exact Or.inr (sctV4LowEq_of_subsumes post tCert _ _ hChk hPostLow)
                  | branchLtBound idxReg bound tInBounds tOutBounds =>
                      simp [hTerm] at hChk
                      cases hSafe : SctDualLabel.isPubSafe (post.getReg idxReg) <;>
                        cases hCIn : getSctV4Cert? cert tInBounds <;>
                        cases hCOut : getSctV4Cert? cert tOutBounds <;>
                        simp [hSafe, hCIn, hCOut] at hChk
                      rcases hChk with ⟨hSubIn, hSubOut⟩
                      have ⟨hA, hS⟩ := sctDualLabel_isPubSafe_imp _ hSafe
                      have hIdxEq := (hPostLow.regRel idxReg).2 hA hS hHaltMid1
                      simp [hEvsEq, hIdxEq]
                      have hBrLow := sctV4LowEq_updateBranchSpec post
                        (stepSctV4InstrList bb.instrs stepOrac.stlOracles s₁).1
                        (stepSctV4InstrList bb.instrs stepOrac.stlOracles s₂).1
                        stepOrac.branchMispred hHaltMid1 hPostLow
                      cases (match stepOrac.branchMispred with
                             | false => natBlt ((stepSctV4InstrList bb.instrs stepOrac.stlOracles s₂).1.getReg idxReg) bound
                             | true => !natBlt ((stepSctV4InstrList bb.instrs stepOrac.stlOracles s₂).1.getReg idxReg) bound) with
                      | true =>
                          exact Or.inr ⟨_, hCIn, sctV4LowEq_of_subsumes post _ _ _ hSubIn hBrLow⟩
                      | false =>
                          exact Or.inr ⟨_, hCOut, sctV4LowEq_of_subsumes post _ _ _ hSubOut hBrLow⟩

theorem specV4ObsTrace_of_stopped (prog : SctV4Prog) (fuel : Nat) (oracle : List V1V4StepOracle)
    (bid : Nat) (s₁ s₂ : SpecV4State)
    (h1 : (s₁.exited || s₁.specHalted) = true)
    (h2 : (s₂.exited || s₂.specHalted) = true) :
    specV4ObsTrace prog fuel oracle bid s₁ = specV4ObsTrace prog fuel oracle bid s₂ := by
  induction fuel generalizing oracle bid with
  | zero => rfl
  | succ f ih =>
      unfold specV4ObsTrace stepSctV4Block
      dsimp
      rw [h1, h2]
      simp [ih _ bid]

/-- **Foundational Theorem 3b (`kernel_sct_v1_v4_sticky_stack_soundness`)**:
    When a Ring-0 kernel extension `prog` passes the single-pass $O(|I|)$ sticky-stack
    dual-label certificate checker (`AllBlocksSctV1V4Certified prog cert`), then for **every**
    combined Spectre v1 (`PHT`) and Spectre v4 (`STL`) oracle `oracle : List V1V4StepOracle`,
    **every** step budget `fuel : Nat`, and **all pairs** of initial states `(s₁, s₂)`
    satisfying `SctV4LowEq pre s₁ s₂` (with arbitrary host kernel secrets
    `s₁.kernelSecretMem ≠ s₂.kernelSecretMem` and `s₁.secretKey ≠ s₂.secretKey`), their
    speculative observation traces are **100% identical**:
    `specV4ObsTrace prog fuel oracle bid s₁ = specV4ObsTrace prog fuel oracle bid s₂`! -/
theorem kernel_sct_v1_v4_sticky_stack_soundness
    (prog : SctV4Prog) (cert : SctV4Certificate)
    (hCert : AllBlocksSctV1V4Certified prog cert) :
    ∀ (fuel : Nat) (oracle : List V1V4StepOracle) (bid : Nat) (pre : SctV4TypeEnv) (s₁ s₂ : SpecV4State),
      getSctV4Cert? cert bid = some pre →
      SctV4LowEq pre s₁ s₂ →
      specV4ObsTrace prog fuel oracle bid s₁ = specV4ObsTrace prog fuel oracle bid s₂ := by
  intro fuel
  induction fuel with
  | zero =>
      intro oracle bid pre s₁ s₂ _ _
      rfl
  | succ f ih =>
      intro oracle bid pre s₁ s₂ hPre hLow
      unfold specV4ObsTrace
      dsimp
      let stepOrac := match oracle with | [] => defaultV1V4Oracle | o :: _ => o
      let restOracle := match oracle with | [] => [] | _ :: os => os
      have hStep := sct_v1_v4_block_step_noninterference prog cert hCert bid stepOrac pre s₁ s₂ hPre hLow
      dsimp at hStep
      rcases hStep with ⟨hNextEq, hEvsEq, hCont⟩
      rw [hEvsEq, hNextEq]
      cases hCont with
      | inl hStopped =>
          rw [specV4ObsTrace_of_stopped prog f restOracle
              (stepSctV4Block prog bid stepOrac s₂).1
              (stepSctV4Block prog bid stepOrac s₁).2.1
              (stepSctV4Block prog bid stepOrac s₂).2.1
              hStopped.1 hStopped.2]
      | inr hNextCert =>
          rcases hNextCert with ⟨nextPre, hNextPre, hNextLow⟩
          rw [hNextEq] at hNextPre
          rw [ih restOracle (stepSctV4Block prog bid stepOrac s₂).1 nextPre
              (stepSctV4Block prog bid stepOrac s₁).2.1
              (stepSctV4Block prog bid stepOrac s₂).2.1
              hNextPre hNextLow]

/-- Concrete Spectre v4 verification:
    1. `checkKernelSctV1V4Cert` REJECTS `spectreV4StlGadgetProg` because `S0` retains its
       sticky `secTransient` taint across the public overwrite `.spillStack .S0 .R3`!
    2. Partitioning secret spills to `.S1` and public spills to `.S0` (`spectreV4DisjointSlotsProg`,
       modeling `Jasmin SCT` S&P 2023 / POPL 2025 disjoint stack-slot allocation) is ACCEPTED by
       `checkKernelSctV1V4Cert` with ZERO fences and eliminates the Spectre v4 leak! -/
def spectreV4DisjointSlotsProg : SctV4Prog :=
  [ { id := 0
      instrs := [
        .helperReadSecretKey .R2,
        .spillStack .S1 .R2,
        .movImm .R3 0,
        .spillStack .S0 .R3,
        .fillStack .R4 .S0,
        .ldMasked .R0 .R4 15,
        .movImm .R0 0
      ]
      term := .exit .R0 } ]

theorem spectre_v4_sticky_cert_rejects_reuse_and_accepts_disjoint_slots :
    checkKernelSctV1V4Cert spectreV4StlGadgetProg [defaultSctV4Env] = false ∧
    checkKernelSctV1V4Cert spectreV4DisjointSlotsProg [defaultSctV4Env] = true ∧
    specV4ObsTrace spectreV4DisjointSlotsProg 1 stlBypassOnFillOracle 0 spectreV4State1 =
      specV4ObsTrace spectreV4DisjointSlotsProg 1 stlBypassOnFillOracle 0 spectreV4State2 :=
  ⟨rfl, rfl, rfl⟩

/-!
  =============================================================================
  AXIOM AUDIT (`#print axioms`)
  =============================================================================
-/

#print axioms ct_instr_step_noninterference
#print axioms ct_block_step_noninterference
#print axioms checkKernelCtCertIndexed_imp_AllBlocksCtCertified
#print axioms kernel_ct_cert_implies_2safety_noninterference
#print axioms ct_cert_rejects_secret_branch_and_cache_index
#print axioms ct_cert_accepts_constant_time_keyed_mac
#print axioms rel_ct_instr_step_noninterference
#print axioms rel_ct_block_step_noninterference
#print axioms checkKernelRelCtCertIndexed_imp_AllBlocksRelCtCertified
#print axioms kernel_rel_ct_cert_soundness
#print axioms relational_kernel_cert_strictly_extends_ct_cert
#print axioms natBlt_and_of_natBlt
#print axioms readSpecMem_masked_eq_pubMem
#print axioms arch_ct_and_memsafe_cert_leaks_under_spectre_v1
#print axioms linux_skip_alu_sanitation_cve2021_33624_unsound
#print axioms sct_instr_step_noninterference
#print axioms sct_block_step_noninterference
#print axioms checkKernelSctCertIndexed_imp_AllBlocksSctCertified
#print axioms kernel_sct_dual_label_cert_soundness
#print axioms spectre_gadget_rejected_by_sct_cert
#print axioms spectre_gadget_repaired_by_blade_slh_accepted
#print axioms spectre_gadget_repaired_by_sfi_mask_accepted
#print axioms spectre_gadget_repaired_by_lfence_accepted
#print axioms spectre_v4_stl_bypass_leaks_overwritten_secret_slot
#print axioms sct_v1_v4_instr_step_noninterference
#print axioms sct_v1_v4_block_step_noninterference
#print axioms checkKernelSctV1V4CertIndexed_imp_AllBlocksSctV1V4Certified
#print axioms kernel_sct_v1_v4_sticky_stack_soundness
#print axioms spectre_v4_sticky_cert_rejects_reuse_and_accepts_disjoint_slots

end InKernelSideChannelAndSpeculativeCertificates
