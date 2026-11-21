/-!
# Inline Assembly Register/Clobber Framing and `compiler-builtins` Verification

Self-contained, kernel-checked Lean 4 (`v4.34.1`) mechanization using ONLY `Init`
(axiom-free beyond `propext`/`Quot.sound`, structurally total computable definitions) covering:
1. Machine state (`Gpr`, `SimdReg`/`SimdVal`, `flags`, `rsp`, unified word-addressed `stackMem`
   modeling the `128`-byte System V red zone `[rsp0 - 16, rsp0)`, `heapMem`, `hwCsrState`)
   and operational contract checker for `InlineAsmContract`;
2. `registerAlloc_and_frame_soundness` (clobber-ABI framing, flags framing, `nostack` /
   red-zone `iff` preservation framing, and `pure`/`readonly`/`nomem` memory framing)
   plus `virtual_to_physical_coalescing_soundness`;
3. Sharpness counterexamples:
   - `ce1_lateout_aliasing_bug_and_earlyout_fix`: `lateout(reg)` (`=r`) permits
     `phys(out) = phys(inp)` aliasing in `mov {out}, 0; add {out}, {inp}` (`42 -> 0`),
     whereas `out(reg)` (`=&r`) forbids aliasing and preserves `val` for all inputs;
   - `ce2_nostack_redzone_clobber_and_default_fix`: `options(nostack)` suppresses
     red-zone stack adjustment in a leaf function, allowing `push rax; pop rax` to
     clobber `[rsp0 - 8]`, whereas omitting `nostack` adjusts `rsp` below the `128`-byte
     red zone and preserves `[rsp0 - 8]`;
4. Constructive `HiLo64` `128`-bit limb division-remainder `divmod128_sound`
   (`q * d + r = n ∧ r < d` for `0 < d`) modeling `compiler-builtins` `__udivti3` / `__umodti3`,
   plus `noBuiltins_prevents_idiom_self_recursion`.
-/

namespace InlineAsmAndBuiltinsFraming

/-! ## Part 1: Machine State, Architectures, Register Classes, and Options -/

inductive Arch where
  | x86_64
  | aarch64
  deriving DecidableEq, Repr

inductive Gpr where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  | x18 | x19 | x29 | x30 | sp
  deriving DecidableEq, Repr

/-- Reserved registers rejected by `rustc_target::asm::{x86,aarch64}` (`validate`). -/
def isReservedGpr (arch : Arch) (reserveX18 : Bool) (r : Gpr) : Bool :=
  match arch with
  | .x86_64 =>
    match r with
    | .rsp | .rbp | .rbx => true
    | .x18 | .x19 | .x29 | .x30 | .sp => true
    | _ => false
  | .aarch64 =>
    match r with
    | .x19 | .x29 | .sp | .rsp | .rbp | .rbx => true
    | .x18 => reserveX18
    | _ => false

structure SimdReg where
  idx : Nat
  deriving DecidableEq, Repr

/-- Split low-128 and upper-lane (`ymm`/`zmm`) value capturing Win64 `xmm6..15` asymmetry:
    Win64 preserves `lo128` of `xmm6..15` while clobbering `ymm6..15[255:128]` (`hiUpper`),
    forcing `clobber_abi("win64")` to mark `xmm0..15` clobbered (`rustc_target/src/asm/mod.rs:1128`). -/
structure SimdVal where
  lo128   : Nat
  hiUpper : Nat
  deriving DecidableEq, Repr

inductive ClobberAbi where
  | none
  | sysv64
  | win64
  | aarch64C (reserveX18 : Bool)
  deriving DecidableEq, Repr

/-- Caller-saved GPR clobber sets matching `InlineAsmClobberAbi::clobbered_regs`. -/
def abiClobbersGpr : ClobberAbi → Gpr → Bool
  | .none, _ => false
  | .sysv64, r =>
    match r with
    | .rax | .rcx | .rdx | .rsi | .rdi | .r8 | .r9 | .r10 | .r11 => true
    | _ => false
  | .win64, r =>
    match r with
    | .rax | .rcx | .rdx | .r8 | .r9 | .r10 | .r11 => true
    | _ => false
  | .aarch64C reserveX18, r =>
    match r with
    | .rax | .rcx | .rdx | .rsi | .rdi | .r8 | .r9 | .r10 | .r11
    | .r12 | .r13 | .r14 | .r15 | .x30 => true
    | .x18 => !reserveX18
    | _ => false

/-- Caller-saved SIMD clobber sets (`xmm0..15` + `zmm16..31` on x86_64; `v0..31` on AArch64). -/
def abiClobbersSimd : ClobberAbi → SimdReg → Bool
  | .none, _ => false
  | .sysv64, v => Nat.blt v.idx 32
  | .win64, v => Nat.blt v.idx 32
  | .aarch64C _, v => Nat.blt v.idx 32

/-- `rustc_ast::ast::InlineAsmOptions` bitflag abstraction. -/
structure AsmOptions where
  pure_          : Bool := false
  nomem          : Bool := false
  readonly       : Bool := false
  preservesFlags : Bool := false
  nostack        : Bool := false
  noreturn       : Bool := false
  mayUnwind      : Bool := false
  deriving DecidableEq, Repr

/-- Option compatibility predicate matching `rustc_builtin_macros/src/asm.rs:177-238`. -/
def AsmOptions.wellFormed (opts : AsmOptions) (hasRealOutput : Bool) (hasLabels : Bool) : Bool :=
  !(opts.nomem && opts.readonly) &&
  !(opts.pure_ && opts.noreturn) &&
  (!opts.pure_ || (opts.nomem || opts.readonly)) &&
  (!opts.pure_ || hasRealOutput) &&
  (!opts.mayUnwind || !hasLabels)

/-- Concrete machine state over 8-byte word-addressed stack (`stackMem`) and `heapMem`.
    The System V `128`-byte red zone on entry at `rsp0` consists of the `16` 8-byte words
    at addresses `a` satisfying `rsp0 - 16 ≤ a ∧ a < rsp0`. -/
structure MachineState where
  gpr        : Gpr → Nat
  simd       : SimdReg → SimdVal
  flags      : Nat
  rsp        : Nat
  stackMem   : Nat → Nat
  heapMem    : Nat → Nat
  hwCsrState : Nat

def updateGpr (f : Gpr → Nat) (r : Gpr) (v : Nat) : Gpr → Nat :=
  fun r' => if r' = r then v else f r'

def updateMem (f : Nat → Nat) (addr : Nat) (v : Nat) : Nat → Nat :=
  fun a => if a = addr then v else f a

def inRedZone (rsp0 addr : Nat) : Prop :=
  rsp0 - 16 ≤ addr ∧ addr < rsp0

/-! ## Part 2: Virtual Assembly IR, Operational Semantics, and Contract Checker -/

abbrev VReg := Nat

inductive RegRef where
  | virt (v : VReg)
  | fixed (r : Gpr)
  deriving DecidableEq, Repr

def RegRef.resolve (alloc : VReg → Gpr) : RegRef → Gpr
  | .virt v  => alloc v
  | .fixed r => r

inductive AsmInsn where
  | movImm   (dst : RegRef) (imm : Nat)
  | movReg   (dst : RegRef) (src : RegRef)
  | addReg   (dst : RegRef) (src : RegRef)
  | pushReg  (src : RegRef)
  | popReg   (dst : RegRef)
  | loadHeap (dst : RegRef) (addrReg : RegRef)
  | storeHeap (addrReg : RegRef) (valReg : RegRef)
  | writeFlags (newFlags : Nat)
  | touchCsr (newCsr : Nat)
  | abiCall  (abi : ClobberAbi) (seed : Nat)
  deriving DecidableEq, Repr

def execInsn (alloc : VReg → Gpr) (insn : AsmInsn) (s : MachineState) : MachineState :=
  match insn with
  | .movImm dst imm =>
    { s with gpr := updateGpr s.gpr (dst.resolve alloc) imm }
  | .movReg dst src =>
    let v := s.gpr (src.resolve alloc)
    { s with gpr := updateGpr s.gpr (dst.resolve alloc) v }
  | .addReg dst src =>
    let d := dst.resolve alloc
    let v := s.gpr d + s.gpr (src.resolve alloc)
    { s with gpr := updateGpr s.gpr d v }
  | .pushReg src =>
    let rsp' := s.rsp - 1
    let v := s.gpr (src.resolve alloc)
    { s with rsp := rsp', stackMem := updateMem s.stackMem rsp' v }
  | .popReg dst =>
    let v := s.stackMem s.rsp
    let rsp' := s.rsp + 1
    { s with rsp := rsp', gpr := updateGpr s.gpr (dst.resolve alloc) v }
  | .loadHeap dst addrReg =>
    let v := s.heapMem (s.gpr (addrReg.resolve alloc))
    { s with gpr := updateGpr s.gpr (dst.resolve alloc) v }
  | .storeHeap addrReg valReg =>
    let addr := s.gpr (addrReg.resolve alloc)
    let v := s.gpr (valReg.resolve alloc)
    { s with heapMem := updateMem s.heapMem addr v }
  | .writeFlags nf =>
    { s with flags := nf }
  | .touchCsr nc =>
    { s with hwCsrState := nc }
  | .abiCall abi seed =>
    { s with
      gpr  := fun r => if abiClobbersGpr abi r then seed else s.gpr r,
      simd := fun v => if abiClobbersSimd abi v then ⟨seed, seed⟩ else s.simd v }

def execInsns (code : List AsmInsn) (alloc : VReg → Gpr) (s : MachineState) : MachineState :=
  match code with
  | [] => s
  | i :: rest => execInsns rest alloc (execInsn alloc i s)

/-- Unaliased virtual-register machine semantics. -/
structure VirtState where
  vreg : VReg → Nat

def writeVReg (f : VReg → Nat) (v : VReg) (val : Nat) : VReg → Nat :=
  fun v' => if v' = v then val else f v'

def execInsnVirt (insn : AsmInsn) (s : VirtState) : VirtState :=
  match insn with
  | .movImm (.virt dst) imm => { vreg := writeVReg s.vreg dst imm }
  | .movReg (.virt dst) (.virt src) => { vreg := writeVReg s.vreg dst (s.vreg src) }
  | .addReg (.virt dst) (.virt src) =>
    { vreg := writeVReg s.vreg dst (s.vreg dst + s.vreg src) }
  | _ => s

def execInsnsVirt (code : List AsmInsn) (s : VirtState) : VirtState :=
  match code with
  | [] => s
  | i :: rest => execInsnsVirt rest (execInsnVirt i s)

/-- Compiler frame-lowering wrapper around `execInsns`:
    when `!opts.nostack` (`prologueSubRsp128 = true`) on `x86_64` SysV, the prologue shifts `rsp`
    by `16` 8-byte words (`128` bytes) below `rsp0` so stack pushes never hit `[rsp0 - 16, rsp0)`. -/
def execFramed (prologueSubRsp128 : Bool) (code : List AsmInsn) (alloc : VReg → Gpr)
    (s : MachineState) : MachineState :=
  if prologueSubRsp128 then
    let sEnter := { s with rsp := s.rsp - 16 }
    let sMid := execInsns code alloc sEnter
    { sMid with rsp := sMid.rsp + 16 }
  else
    execInsns code alloc s

def insnWritesGpr (alloc : VReg → Gpr) (r : Gpr) : AsmInsn → Bool
  | .movImm dst _   => dst.resolve alloc == r
  | .movReg dst _   => dst.resolve alloc == r
  | .addReg dst _   => dst.resolve alloc == r
  | .popReg dst     => dst.resolve alloc == r
  | .loadHeap dst _ => dst.resolve alloc == r
  | .abiCall abi _  => abiClobbersGpr abi r
  | _               => false

def insnWritesVReg (v : VReg) : AsmInsn → Bool
  | .movImm (.virt u) _   => u == v
  | .movReg (.virt u) _   => u == v
  | .addReg (.virt u) _   => u == v
  | .popReg (.virt u)     => u == v
  | .loadHeap (.virt u) _ => u == v
  | _                     => false

def insnReadsVReg (v : VReg) : AsmInsn → Bool
  | .movReg _ (.virt u)            => u == v
  | .addReg (.virt d) (.virt s)    => d == v || s == v
  | .addReg _ (.virt s)            => s == v
  | .pushReg (.virt u)             => u == v
  | .loadHeap _ (.virt u)          => u == v
  | .storeHeap (.virt a) (.virt b) => a == v || b == v
  | .storeHeap (.virt a) _         => a == v
  | .storeHeap _ (.virt b)         => b == v
  | _                              => false

/-- Decidable Read-Before-First-Write check for `lateout`: returns `true` iff once `outV`
    is written (`writtenOut = true`), `inV` is never read at any later instruction. -/
def readBeforeFirstWriteAux (outV inV : VReg) (writtenOut : Bool) : List AsmInsn → Bool
  | [] => true
  | i :: rest =>
    let readBad := writtenOut && insnReadsVReg inV i
    let written' := writtenOut || insnWritesVReg outV i
    !readBad && readBeforeFirstWriteAux outV inV written' rest

def readBeforeFirstWrite (outV inV : VReg) (code : List AsmInsn) : Bool :=
  readBeforeFirstWriteAux outV inV false code

def insnTouchesStack : AsmInsn → Bool
  | .pushReg _ | .popReg _ => true
  | _ => false

def checkBodyNoStack : List AsmInsn → Bool
  | [] => true
  | i :: rest => !insnTouchesStack i && checkBodyNoStack rest

/-- Balanced push/pop depth check guaranteeing `rsp + depth = baseRsp` at every step
    and `depth = 0` at exit (never exceeding `baseRsp`, never underflowing). -/
def checkBalancedStackAux (depth baseRsp : Nat) : List AsmInsn → Bool
  | [] => depth == 0
  | .pushReg _ :: rest => Nat.blt depth baseRsp && checkBalancedStackAux (depth + 1) baseRsp rest
  | .popReg _ :: rest => Nat.blt 0 depth && checkBalancedStackAux (depth - 1) baseRsp rest
  | _ :: rest => checkBalancedStackAux depth baseRsp rest

def checkBalancedStack (baseRsp : Nat) (code : List AsmInsn) : Bool :=
  checkBalancedStackAux 0 baseRsp code

def insnWritesFlags : AsmInsn → Bool
  | .writeFlags _ => true
  | _ => false

def checkBodyPreservesFlags : List AsmInsn → Bool
  | [] => true
  | i :: rest => !insnWritesFlags i && checkBodyPreservesFlags rest

def insnWritesHeap : AsmInsn → Bool
  | .storeHeap _ _ => true
  | _ => false

def insnReadsHeap : AsmInsn → Bool
  | .loadHeap _ _ => true
  | _ => false

def insnTouchesCsr : AsmInsn → Bool
  | .touchCsr _ => true
  | _ => false

def checkBodyMemOpts (opts : AsmOptions) : List AsmInsn → Bool
  | [] => true
  | i :: rest =>
    let okWrite := !(opts.nomem || opts.readonly) || !insnWritesHeap i
    let okRead  := !opts.nomem || !insnReadsHeap i
    let okPure  := !(opts.pure_ && opts.nomem) || !insnTouchesCsr i
    okWrite && okRead && okPure && checkBodyMemOpts opts rest

def checkBodyClobberAbi (abi : ClobberAbi) : List AsmInsn → Bool
  | [] => true
  | i :: rest =>
    let ok := match i with
      | .abiCall a _ => a == abi
      | _ => true
    ok && checkBodyClobberAbi abi rest

structure InlineAsmContract where
  arch         : Arch
  reserveX18   : Bool
  inRegs       : List VReg
  earlyOutRegs : List VReg
  lateOutRegs  : List VReg
  clobberAbi   : ClobberAbi
  opts         : AsmOptions
  code         : List AsmInsn

def checkEarlyDisjoint (alloc : VReg → Gpr) (earlyOuts ins : List VReg) : Bool :=
  earlyOuts.all (fun eo => ins.all (fun iv => alloc eo != alloc iv))

def checkLateCoalescing (alloc : VReg → Gpr) (lateOuts ins : List VReg) (code : List AsmInsn) : Bool :=
  lateOuts.all (fun lo =>
    ins.all (fun iv => (alloc lo != alloc iv) || readBeforeFirstWrite lo iv code))

def checkNoReserved (arch : Arch) (reserveX18 : Bool) (alloc : VReg → Gpr) (regs : List VReg) : Bool :=
  regs.all (fun v => !isReservedGpr arch reserveX18 (alloc v))

def checkPairwiseDistinctPhys (alloc : VReg → Gpr) : List VReg → Bool
  | [] => true
  | x :: xs => xs.all (fun y => alloc x != alloc y) && checkPairwiseDistinctPhys alloc xs

def checkPureRegBody (inRegs outs : List VReg) : List AsmInsn → Bool
  | [] => true
  | .movImm (.virt d) _ :: rest => outs.contains d && checkPureRegBody inRegs outs rest
  | .movReg (.virt d) (.virt s) :: rest =>
    outs.contains d && (inRegs.contains s || outs.contains s) && checkPureRegBody inRegs outs rest
  | .addReg (.virt d) (.virt s) :: rest =>
    outs.contains d && (inRegs.contains s || outs.contains s) && checkPureRegBody inRegs outs rest
  | _ :: _ => false

def checkInlineAsmContract (c : InlineAsmContract) (alloc : VReg → Gpr) : Bool :=
  let hasOut := !c.earlyOutRegs.isEmpty || !c.lateOutRegs.isEmpty
  c.opts.wellFormed hasOut false &&
  checkNoReserved c.arch c.reserveX18 alloc (c.inRegs ++ c.earlyOutRegs ++ c.lateOutRegs) &&
  checkEarlyDisjoint alloc c.earlyOutRegs c.inRegs &&
  checkLateCoalescing alloc c.lateOutRegs c.inRegs c.code &&
  (!c.opts.nostack || checkBodyNoStack c.code) &&
  (!c.opts.preservesFlags || checkBodyPreservesFlags c.code) &&
  checkBodyMemOpts c.opts c.code &&
  checkBodyClobberAbi c.clobberAbi c.code

/-! ## Part 3: Constructive Frame, Register-Allocation, and Red-Zone Theorems -/

theorem updateGpr_ne (f : Gpr → Nat) {r r' : Gpr} (h : r' ≠ r) (v : Nat) :
    updateGpr f r v r' = f r' :=
  ite_eq_right h

theorem updateGpr_eq (f : Gpr → Nat) (r : Gpr) (v : Nat) :
    updateGpr f r v r = v :=
  ite_eq_left rfl

theorem writeVReg_ne (f : VReg → Nat) {u v : VReg} (h : v ≠ u) (val : Nat) :
    writeVReg f u val v = f v :=
  ite_eq_right h

theorem writeVReg_eq (f : VReg → Nat) (u : VReg) (val : Nat) :
    writeVReg f u val u = val :=
  ite_eq_left rfl

theorem updateMem_ne (f : Nat → Nat) {a a' : Nat} (h : a' ≠ a) (v : Nat) :
    updateMem f a v a' = f a' :=
  ite_eq_right h

theorem updateMem_eq (f : Nat → Nat) (a v : Nat) :
    updateMem f a v a = v :=
  ite_eq_left rfl

theorem execInsns_preserves_gpr_of_unwritten
    (code : List AsmInsn) (alloc : VReg → Gpr) (r : Gpr) (s : MachineState)
    (h_no_write : ∀ i, i ∈ code → insnWritesGpr alloc r i = false) :
    (execInsns code alloc s).gpr r = s.gpr r := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have hi : insnWritesGpr alloc r i = false := h_no_write i List.mem_cons_self
    have hrest : ∀ j, j ∈ rest → insnWritesGpr alloc r j = false :=
      fun j hj => h_no_write j (List.mem_cons_of_mem i hj)
    rw [execInsns, ih (execInsn alloc i s) hrest]
    cases i with
    | movImm dst _ =>
      exact updateGpr_ne s.gpr (fun heq => by subst heq; simp [insnWritesGpr] at hi) _
    | movReg dst _ =>
      exact updateGpr_ne s.gpr (fun heq => by subst heq; simp [insnWritesGpr] at hi) _
    | addReg dst _ =>
      exact updateGpr_ne s.gpr (fun heq => by subst heq; simp [insnWritesGpr] at hi) _
    | pushReg _ => rfl
    | popReg dst =>
      exact updateGpr_ne s.gpr (fun heq => by subst heq; simp [insnWritesGpr] at hi) _
    | loadHeap dst _ =>
      exact updateGpr_ne s.gpr (fun heq => by subst heq; simp [insnWritesGpr] at hi) _
    | storeHeap _ _ | writeFlags _ | touchCsr _ => rfl
    | abiCall abi _ =>
      simp only [execInsn, insnWritesGpr] at hi ⊢
      rw [hi]
      rfl

theorem execInsns_preserves_simd
    (code : List AsmInsn) (alloc : VReg → Gpr) (abi : ClobberAbi) (v : SimdReg) (s : MachineState)
    (h_abi : checkBodyClobberAbi abi code = true)
    (h_not_clob : abiClobbersSimd abi v = false) :
    (execInsns code alloc s).simd v = s.simd v := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [checkBodyClobberAbi, Bool.and_eq_true] at h_abi
    rw [execInsns, ih (execInsn alloc i s) h_abi.2]
    cases i with
    | abiCall a seed =>
      have ha : a = abi := eq_of_beq h_abi.1
      subst ha
      simp only [execInsn, h_not_clob]
      rfl
    | movImm _ _ | movReg _ _ | addReg _ _ | pushReg _ | popReg _
    | loadHeap _ _ | storeHeap _ _ | writeFlags _ | touchCsr _ => rfl

theorem execInsns_preserves_flags
    (code : List AsmInsn) (alloc : VReg → Gpr) (s : MachineState)
    (h_pf : checkBodyPreservesFlags code = true) :
    (execInsns code alloc s).flags = s.flags := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [checkBodyPreservesFlags, Bool.and_eq_true] at h_pf
    rw [execInsns, ih (execInsn alloc i s) h_pf.2]
    cases i with
    | writeFlags _ => simp [insnWritesFlags] at h_pf
    | movImm _ _ | movReg _ _ | addReg _ _ | pushReg _ | popReg _
    | loadHeap _ _ | storeHeap _ _ | touchCsr _ | abiCall _ _ => rfl

theorem execInsns_nostack_preserves_rsp_and_stack
    (code : List AsmInsn) (alloc : VReg → Gpr) (s : MachineState)
    (h_ns : checkBodyNoStack code = true) :
    (execInsns code alloc s).rsp = s.rsp ∧
    (∀ addr, (execInsns code alloc s).stackMem addr = s.stackMem addr) := by
  induction code generalizing s with
  | nil => exact ⟨rfl, fun _ => rfl⟩
  | cons i rest ih =>
    simp only [checkBodyNoStack, Bool.and_eq_true] at h_ns
    have hstep := ih (execInsn alloc i s) h_ns.2
    cases i with
    | pushReg _ | popReg _ => simp [insnTouchesStack] at h_ns
    | movImm _ _ | movReg _ _ | addReg _ _ | loadHeap _ _
    | storeHeap _ _ | writeFlags _ | touchCsr _ | abiCall _ _ =>
      exact hstep

theorem execInsns_preserves_heap_and_csr
    (code : List AsmInsn) (alloc : VReg → Gpr) (opts : AsmOptions) (s : MachineState)
    (h_mem : checkBodyMemOpts opts code = true) :
    ((opts.nomem = true ∨ opts.readonly = true) →
      ∀ addr, (execInsns code alloc s).heapMem addr = s.heapMem addr) ∧
    ((opts.pure_ = true ∧ opts.nomem = true) →
      (execInsns code alloc s).hwCsrState = s.hwCsrState) := by
  induction code generalizing s with
  | nil => exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | cons i rest ih =>
    simp only [checkBodyMemOpts, Bool.and_eq_true] at h_mem
    have hrest := ih (execInsn alloc i s) h_mem.2
    constructor
    · intro hro addr
      rw [execInsns, hrest.1 hro addr]
      cases i with
      | storeHeap _ _ =>
        have hbad := h_mem.1.1.1
        rcases hro with hnm | hro'
        · simp [hnm, insnWritesHeap] at hbad
        · simp [hro', insnWritesHeap] at hbad
      | movImm _ _ | movReg _ _ | addReg _ _ | pushReg _ | popReg _
      | loadHeap _ _ | writeFlags _ | touchCsr _ | abiCall _ _ => rfl
    · intro hpure
      rw [execInsns, hrest.2 hpure]
      cases i with
      | touchCsr _ =>
        have hbad := h_mem.1.2
        simp [hpure.1, hpure.2, insnTouchesCsr] at hbad
      | movImm _ _ | movReg _ _ | addReg _ _ | pushReg _ | popReg _
      | loadHeap _ _ | storeHeap _ _ | writeFlags _ | abiCall _ _ => rfl

theorem blt_lt {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

/-- Balanced stack execution invariant: every `push` lands below `rsp0 - 16`, preserving `[rsp0 - 16, rsp0)`. -/
theorem execInsns_balanced_writes_below_redzone
    (code : List AsmInsn) (alloc : VReg → Gpr) (s : MachineState)
    (depth baseRsp rsp0 addr : Nat)
    (h_red : inRedZone rsp0 addr)
    (h_base : baseRsp ≤ rsp0 - 16)
    (h_inv : s.rsp + depth = baseRsp)
    (h_bal : checkBalancedStackAux depth baseRsp code = true) :
    (execInsns code alloc s).rsp = baseRsp ∧
    (execInsns code alloc s).stackMem addr = s.stackMem addr := by
  induction code generalizing s depth with
  | nil =>
    simp only [checkBalancedStackAux, beq_iff_eq] at h_bal
    subst h_bal
    exact ⟨h_inv, rfl⟩
  | cons i rest ih =>
    cases i with
    | pushReg src =>
      simp only [checkBalancedStackAux, Bool.and_eq_true] at h_bal
      have h_d_lt : depth < baseRsp := blt_lt h_bal.1
      have h_s_pos : 1 ≤ s.rsp := by
        cases hsp : s.rsp with
        | zero =>
          rw [hsp, Nat.zero_add] at h_inv
          rw [h_inv] at h_d_lt
          exact False.elim (Nat.lt_irrefl _ h_d_lt)
        | succ k => exact Nat.succ_le_succ (Nat.zero_le k)
      have h_inv_next : (s.rsp - 1) + (depth + 1) = baseRsp := by
        rw [Nat.add_comm depth 1, ← Nat.add_assoc, Nat.sub_add_cancel h_s_pos]
        exact h_inv
      have h_s_le : s.rsp ≤ rsp0 - 16 := by
        have : s.rsp ≤ s.rsp + depth := Nat.le_add_right _ _
        exact Nat.le_trans this (Nat.le_trans (Nat.le_of_eq h_inv) h_base)
      have h_s1_lt : s.rsp - 1 < addr := by
        have h1 : s.rsp - 1 < s.rsp := Nat.sub_lt h_s_pos (Nat.succ_pos 0)
        exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1 h_s_le) h_red.1
      have h_ne : addr ≠ s.rsp - 1 := Nat.ne_of_gt h_s1_lt
      have hstep := ih (execInsn alloc (.pushReg src) s) (depth + 1) h_inv_next h_bal.2
      exact ⟨hstep.1, Eq.trans hstep.2 (updateMem_ne s.stackMem h_ne _)⟩
    | popReg dst =>
      simp only [checkBalancedStackAux, Bool.and_eq_true] at h_bal
      have h_d_pos : 0 < depth := blt_lt h_bal.1
      have h_d_ge1 : 1 ≤ depth := h_d_pos
      have h_inv_next : (s.rsp + 1) + (depth - 1) = baseRsp := by
        rw [Nat.add_assoc, Nat.add_comm 1 (depth - 1), Nat.sub_add_cancel h_d_ge1]
        exact h_inv
      exact ih (execInsn alloc (.popReg dst) s) (depth - 1) h_inv_next h_bal.2
    | movImm _ _ | movReg _ _ | addReg _ _ | loadHeap _ _
    | storeHeap _ _ | writeFlags _ | touchCsr _ | abiCall _ _ =>
      exact ih (execInsn alloc _ s) depth h_inv h_bal

/-- Master Register-Allocation & Frame-Preservation Soundness Theorem. -/
theorem registerAlloc_and_frame_soundness
    (c : InlineAsmContract) (alloc : VReg → Gpr) (s : MachineState)
    (h_contract : checkInlineAsmContract c alloc = true)
    (h_rsp0 : 16 ≤ s.rsp) :
    (∀ r : Gpr,
      (∀ i, i ∈ c.code → insnWritesGpr alloc r i = false) →
      (execInsns c.code alloc s).gpr r = s.gpr r) ∧
    (∀ v : SimdReg, abiClobbersSimd c.clobberAbi v = false →
      (execInsns c.code alloc s).simd v = s.simd v) ∧
    (c.opts.preservesFlags = true → (execInsns c.code alloc s).flags = s.flags) ∧
    (c.opts.nostack = true →
      (execInsns c.code alloc s).rsp = s.rsp ∧
      (∀ addr, inRedZone s.rsp addr → (execInsns c.code alloc s).stackMem addr = s.stackMem addr)) ∧
    (checkBalancedStack (s.rsp - 16) c.code = true →
      (execFramed true c.code alloc s).rsp = s.rsp ∧
      (∀ addr, inRedZone s.rsp addr → (execFramed true c.code alloc s).stackMem addr = s.stackMem addr)) ∧
    ((c.opts.nomem = true ∨ c.opts.readonly = true) →
      ∀ addr, (execInsns c.code alloc s).heapMem addr = s.heapMem addr) ∧
    ((c.opts.pure_ = true ∧ c.opts.nomem = true) →
      (execInsns c.code alloc s).hwCsrState = s.hwCsrState) := by
  simp only [checkInlineAsmContract, Bool.and_eq_true] at h_contract
  have h_clob := h_contract.2
  have h_mem  := h_contract.1.2
  have h_pf   := h_contract.1.1.2
  have h_ns   := h_contract.1.1.1.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact execInsns_preserves_gpr_of_unwritten c.code alloc r s hr
  · intro v hv
    exact execInsns_preserves_simd c.code alloc c.clobberAbi v s h_clob hv
  · intro hpf_on
    simp only [hpf_on, Bool.not_true, Bool.false_or] at h_pf
    exact execInsns_preserves_flags c.code alloc s h_pf
  · intro hns_on
    simp only [hns_on, Bool.not_true, Bool.false_or] at h_ns
    have hres := execInsns_nostack_preserves_rsp_and_stack c.code alloc s h_ns
    exact ⟨hres.1, fun addr _ => hres.2 addr⟩
  · intro hbal
    have h_le : s.rsp - 16 ≤ s.rsp - 16 := Nat.le_refl _
    have h_spos : 0 < s.rsp := Nat.lt_of_lt_of_le (by decide : 0 < 16) h_rsp0
    have h_rz_dummy : inRedZone s.rsp (s.rsp - 1) :=
      ⟨Nat.sub_le_sub_left (by decide : 1 ≤ 16) s.rsp, Nat.sub_lt h_spos (Nat.succ_pos 0)⟩
    constructor
    · simp only [execFramed, ite_true]
      have h_b := execInsns_balanced_writes_below_redzone c.code alloc { s with rsp := s.rsp - 16 }
        0 (s.rsp - 16) s.rsp (s.rsp - 1) h_rz_dummy h_le rfl hbal
      rw [h_b.1, Nat.sub_add_cancel h_rsp0]
    · intro addr hred
      simp only [execFramed, ite_true]
      exact (execInsns_balanced_writes_below_redzone c.code alloc { s with rsp := s.rsp - 16 }
        0 (s.rsp - 16) s.rsp addr hred h_le rfl hbal).2
  · exact (execInsns_preserves_heap_and_csr c.code alloc c.opts s h_mem).1
  · exact (execInsns_preserves_heap_and_csr c.code alloc c.opts s h_mem).2

theorem if_tt {α : Sort u} (t e : α) : (if true = true then t else e) = t := ite_eq_left rfl
theorem if_ff {α : Sort u} (t e : α) : (if false = true then t else e) = e := ite_eq_right Bool.false_ne_true
theorem ite_false_eq {α : Sort u} {b : Bool} (h : b = false) (t e : α) :
    (if b = true then t else e) = e :=
  ite_eq_right (fun (ht : b = true) => Bool.noConfusion (Eq.trans ht.symm h))

/-- Bidirectional `iff` red-zone framing theorem for a stack-pushing body (`push rax; pop rax`)
    when a leaf caller keeps a live canary in `[rsp - 8]`: caller's red-zone word is preserved
    iff `nostack = false` (forcing prologue frame allocation below the `128`-byte red zone). -/
theorem nostack_redzone_iff_for_push_pop
    (s : MachineState) (h_rsp : 17 ≤ s.rsp) (canary : Nat)
    (h_rz : s.stackMem (s.rsp - 1) = canary)
    (h_ne : s.gpr .rax ≠ canary) :
    ∀ nostackFlag : Bool,
      ((execFramed (!nostackFlag) [.pushReg (.fixed .rax), .popReg (.fixed .rax)]
        (fun _ => .rax) s).stackMem (s.rsp - 1) = canary) ↔ (nostackFlag = false) := by
  intro nostackFlag
  cases nostackFlag with
  | false =>
    refine ⟨fun _ => rfl, fun _ => ?_⟩
    unfold execFramed
    rw [Bool.not_false, if_tt]
    dsimp only [execInsns, execInsn, RegRef.resolve]
    have h_pos16 : 1 ≤ s.rsp - 16 := Nat.le_sub_of_add_le' h_rsp
    have h_lt : (s.rsp - 16) - 1 < s.rsp - 16 := Nat.sub_lt h_pos16 (Nat.succ_pos 0)
    have h_le16 : s.rsp - 16 ≤ s.rsp - 1 := Nat.sub_le_sub_left (by decide : 1 ≤ 16) s.rsp
    have h_ne_addr : s.rsp - 1 ≠ (s.rsp - 16) - 1 :=
      Nat.ne_of_gt (Nat.lt_of_lt_of_le h_lt h_le16)
    rw [updateMem_ne s.stackMem h_ne_addr, h_rz]
  | true =>
    refine ⟨fun h => ?_, fun h => False.elim (Bool.noConfusion h)⟩
    unfold execFramed at h
    rw [Bool.not_true, if_ff] at h
    dsimp only [execInsns, execInsn, RegRef.resolve] at h
    rw [updateMem_eq] at h
    exact False.elim (h_ne h)

/-! ### Part 3b: Virtual-to-Physical Coalescing Soundness -/

theorem vreg_beq_refl (v : VReg) : (v == v) = true := decide_eq_true rfl

theorem vreg_beq_false_of_ne {u v : VReg} (h : u ≠ v) : (u == v) = false := decide_eq_false h

theorem mem_of_contains_true {x : VReg} :
    ∀ {xs : List VReg}, xs.contains x = true → x ∈ xs
  | [], h => by cases h
  | a :: rest, h => by
    simp only [List.contains, List.elem] at h
    cases heq : (x == a) with
    | true => rw [of_decide_eq_true heq]; exact List.Mem.head rest
    | false =>
      rw [heq] at h
      exact List.Mem.tail a (mem_of_contains_true h)

theorem contains_true_of_mem {x : VReg} :
    ∀ {xs : List VReg}, x ∈ xs → xs.contains x = true
  | [], h => by cases h
  | a :: rest, h => by
    cases h with
    | head => simp only [List.contains, List.elem, vreg_beq_refl]
    | tail _ hmem =>
      simp only [List.contains, List.elem]
      cases (x == a) with
      | true => rfl
      | false => exact contains_true_of_mem hmem

theorem mem_of_mem_filter {α : Type} {p : α → Bool} {x : α} :
    ∀ {xs : List α}, x ∈ xs.filter p → x ∈ xs ∧ p x = true
  | [], hx => by cases hx
  | a :: rest, hx => by
    cases hpa : p a with
    | true =>
      simp only [List.filter, hpa] at hx
      cases hx with
      | head => exact ⟨List.Mem.head rest, hpa⟩
      | tail _ hr =>
        have ih := mem_of_mem_filter hr
        exact ⟨List.Mem.tail a ih.1, ih.2⟩
    | false =>
      simp only [List.filter, hpa] at hx
      have ih := mem_of_mem_filter hx
      exact ⟨List.Mem.tail a ih.1, ih.2⟩

theorem all_forall_mem {α : Type} {xs : List α} {p : α → Bool}
    (h : xs.all p = true) : ∀ x, x ∈ xs → p x = true := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons a rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    intro x hx
    cases hx with
    | head => exact h.1
    | tail _ hmem => exact ih h.2 x hmem

theorem pairwiseDistinct_ne {alloc : VReg → Gpr} {xs : List VReg}
    (h_dist : checkPairwiseDistinctPhys alloc xs = true) :
    ∀ {x y : VReg}, x ∈ xs → y ∈ xs → x ≠ y → alloc x ≠ alloc y := by
  induction xs with
  | nil => intro x y hx; cases hx
  | cons a rest ih =>
    simp only [checkPairwiseDistinctPhys, Bool.and_eq_true] at h_dist
    intro x y hx hy hne
    cases hx with
    | head =>
      cases hy with
      | head => exact False.elim (hne rfl)
      | tail _ hmy =>
        have h_all := all_forall_mem h_dist.1 y hmy
        intro heq; rw [heq, bne_self_eq_false] at h_all; cases h_all
    | tail _ hmx =>
      cases hy with
      | head =>
        have h_all := all_forall_mem h_dist.1 x hmx
        intro heq; rw [heq, bne_self_eq_false] at h_all; cases h_all
      | tail _ hmy =>
        exact ih h_dist.2 hmx hmy hne

theorem rbfw_written_blocks_read
    (outV inV : VReg) (code : List AsmInsn)
    (h : readBeforeFirstWriteAux outV inV true code = true) :
    ∀ i, i ∈ code → insnReadsVReg inV i = false := by
  induction code with
  | nil => intro i hi; cases hi
  | cons x rest ih =>
    simp only [readBeforeFirstWriteAux, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true'] at h
    have hx_false : insnReadsVReg inV x = false := h.1
    have ht : (true || insnWritesVReg outV x) = true := rfl
    rw [ht] at h
    intro i hi
    cases hi with
    | head => exact hx_false
    | tail _ hmem => exact ih h.2 i hmem

theorem rbfw_step_tail
    (outV inV : VReg) (written : Bool) (x : AsmInsn) (rest : List AsmInsn)
    (h : readBeforeFirstWriteAux outV inV written (x :: rest) = true) :
    (written = true → insnReadsVReg inV x = false) ∧
    readBeforeFirstWriteAux outV inV (written || insnWritesVReg outV x) rest = true := by
  simp only [readBeforeFirstWriteAux, Bool.and_eq_true] at h
  constructor
  · intro hw
    rw [hw, Bool.true_and, Bool.not_eq_true'] at h
    exact h.1
  · exact h.2

/-- Shared one-step preservation helper for any pure virtual write to `(.virt d)` computing
    the identical `newVal` in both physical (`sPhys`) and virtual (`sVirt`) states. -/
theorem step_pure_write_invariant
    (inRegs earlyOuts lateOuts : List VReg)
    (x : AsmInsn) (rest : List AsmInsn) (alloc : VReg → Gpr)
    (aliveIn : List VReg) (d : VReg) (newVal : Nat)
    (sPhys : MachineState) (sVirt : VirtState)
    (hd_out : d ∈ earlyOuts ++ lateOuts)
    (h_disj_id : ∀ v, v ∈ inRegs → (earlyOuts ++ lateOuts).contains v = false)
    (h_out_dist : checkPairwiseDistinctPhys alloc (earlyOuts ++ lateOuts) = true)
    (h_early_disj : checkEarlyDisjoint alloc earlyOuts inRegs = true)
    (h_alive_sub : ∀ iv, iv ∈ aliveIn → iv ∈ inRegs)
    (h_not_alive : ∀ iv, iv ∈ inRegs → ¬ (iv ∈ aliveIn) → ∃ lo, lo ∈ lateOuts ∧ alloc lo = alloc iv)
    (h_dead_or_rbfw : ∀ iv, iv ∈ inRegs →
      (∀ lo, lo ∈ lateOuts → alloc lo = alloc iv →
        (iv ∈ aliveIn → readBeforeFirstWrite lo iv (x :: rest) = true) ∧
        (¬ (iv ∈ aliveIn) → ∀ i, i ∈ x :: rest → insnReadsVReg iv i = false)))
    (hx_writes : insnWritesVReg d x = true ∧
      ∀ lo, lo ∈ lateOuts → lo ≠ d → insnWritesVReg lo x = false)
    (h_sim_in : ∀ iv, iv ∈ aliveIn → sPhys.gpr (alloc iv) = sVirt.vreg iv)
    (h_sim_out : ∀ o, o ∈ earlyOuts ++ lateOuts → sPhys.gpr (alloc o) = sVirt.vreg o) :
    let aliveNext := aliveIn.filter (fun iv => alloc iv != alloc d)
    let sPhys' := { sPhys with gpr := updateGpr sPhys.gpr (alloc d) newVal }
    let sVirt' : VirtState := { vreg := writeVReg sVirt.vreg d newVal }
    (∀ iv, iv ∈ aliveNext → iv ∈ inRegs) ∧
    (∀ iv, iv ∈ inRegs → ¬ (iv ∈ aliveNext) → ∃ lo, lo ∈ lateOuts ∧ alloc lo = alloc iv) ∧
    (∀ iv, iv ∈ inRegs →
      (∀ lo, lo ∈ lateOuts → alloc lo = alloc iv →
        (iv ∈ aliveNext → readBeforeFirstWrite lo iv rest = true) ∧
        (¬ (iv ∈ aliveNext) → ∀ i, i ∈ rest → insnReadsVReg iv i = false))) ∧
    (∀ iv, iv ∈ aliveNext → sPhys'.gpr (alloc iv) = sVirt'.vreg iv) ∧
    (∀ o, o ∈ earlyOuts ++ lateOuts → sPhys'.gpr (alloc o) = sVirt'.vreg o) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro iv hiv
    exact h_alive_sub iv (mem_of_mem_filter hiv).1
  · intro iv hiv_in hnot_next
    cases hal : aliveIn.contains iv with
    | false =>
      have hnot_prev : ¬ (iv ∈ aliveIn) := fun hm => by
        rw [contains_true_of_mem hm] at hal; cases hal
      exact h_not_alive iv hiv_in hnot_prev
    | true =>
      have hm_prev : iv ∈ aliveIn := mem_of_contains_true hal
      have h_eq_ad : alloc iv = alloc d := by
        cases hdec : (alloc iv == alloc d) with
        | true => exact eq_of_beq hdec
        | false =>
          have hb : (alloc iv != alloc d) = true := by simp [bne, hdec]
          exact False.elim (hnot_next (List.mem_filter.mpr ⟨hm_prev, hb⟩))
      cases List.mem_append.mp hd_out with
      | inl hd_early =>
        have ha1 := all_forall_mem h_early_disj d hd_early
        have ha2 := all_forall_mem ha1 iv hiv_in
        rw [h_eq_ad, bne_self_eq_false] at ha2
        cases ha2
      | inr hd_late =>
        exact ⟨d, hd_late, h_eq_ad.symm⟩
  · intro iv hiv_in lo hlo_mem h_eq
    have hprev := h_dead_or_rbfw iv hiv_in lo hlo_mem h_eq
    constructor
    · intro halive_next
      have halive : iv ∈ aliveIn := (mem_of_mem_filter halive_next).1
      have hstep := rbfw_step_tail lo iv false x rest (hprev.1 halive)
      have hne_ld : lo ≠ d := by
        intro h_eq_ld
        subst h_eq_ld
        have hf := (mem_of_mem_filter halive_next).2
        rw [h_eq, bne_self_eq_false] at hf
        cases hf
      rw [hx_writes.2 lo hlo_mem hne_ld] at hstep
      exact hstep.2
    · intro hnot_next
      cases hal : aliveIn.contains iv with
      | false =>
        have hnot_prev : ¬ (iv ∈ aliveIn) := fun hm => by
          rw [contains_true_of_mem hm] at hal; cases hal
        intro j hj
        exact hprev.2 hnot_prev j (List.mem_cons_of_mem x hj)
      | true =>
        have halive : iv ∈ aliveIn := mem_of_contains_true hal
        have h_eq_ad : alloc iv = alloc d := by
          cases hdec : (alloc iv == alloc d) with
          | true => exact eq_of_beq hdec
          | false =>
            have hb : (alloc iv != alloc d) = true := by simp [bne, hdec]
            exact False.elim (hnot_next (List.mem_filter.mpr ⟨halive, hb⟩))
        have h_d_is_lo : d = lo := by
          cases decEq d lo with
          | isTrue he => exact he
          | isFalse hne =>
            have hlo_all := List.mem_append_right earlyOuts hlo_mem
            have h_phys_ne := pairwiseDistinct_ne h_out_dist hd_out hlo_all hne
            exact False.elim (h_phys_ne (Eq.trans h_eq_ad.symm h_eq.symm))
        subst h_d_is_lo
        have hstep := rbfw_step_tail d iv false x rest (hprev.1 halive)
        rw [hx_writes.1] at hstep
        exact rbfw_written_blocks_read d iv rest hstep.2
  · intro iv hiv
    have halive : iv ∈ aliveIn := (mem_of_mem_filter hiv).1
    have hiv_in : iv ∈ inRegs := h_alive_sub iv halive
    have hiv_not_out : (earlyOuts ++ lateOuts).contains iv = false := h_disj_id iv hiv_in
    have hne_id : iv ≠ d := by
      intro heq; subst heq
      rw [contains_true_of_mem hd_out] at hiv_not_out
      cases hiv_not_out
    have h_phys_ne : alloc iv ≠ alloc d := by
      have hf := (mem_of_mem_filter hiv).2
      intro heq; rw [heq, bne_self_eq_false] at hf; cases hf
    rw [updateGpr_ne sPhys.gpr h_phys_ne, writeVReg_ne sVirt.vreg hne_id]
    exact h_sim_in iv halive
  · intro o ho
    cases decEq o d with
    | isTrue heq =>
      subst heq
      rw [updateGpr_eq, writeVReg_eq]
    | isFalse hne =>
      have h_phys_ne : alloc o ≠ alloc d := pairwiseDistinct_ne h_out_dist ho hd_out hne
      rw [updateGpr_ne sPhys.gpr h_phys_ne, writeVReg_ne sVirt.vreg hne]
      exact h_sim_out o ho

/-- Helper reading a source operand whose value must match between physical and virtual states. -/
theorem read_src_eq
    (inRegs earlyOuts lateOuts : List VReg)
    (x : AsmInsn) (rest : List AsmInsn) (alloc : VReg → Gpr)
    (aliveIn : List VReg) (s : VReg)
    (sPhys : MachineState) (sVirt : VirtState)
    (hs_decl : (inRegs.contains s || (earlyOuts ++ lateOuts).contains s) = true)
    (hs_read : insnReadsVReg s x = true)
    (h_not_alive : ∀ iv, iv ∈ inRegs → ¬ (iv ∈ aliveIn) → ∃ lo, lo ∈ lateOuts ∧ alloc lo = alloc iv)
    (h_dead_or_rbfw : ∀ iv, iv ∈ inRegs →
      (∀ lo, lo ∈ lateOuts → alloc lo = alloc iv →
        (iv ∈ aliveIn → readBeforeFirstWrite lo iv (x :: rest) = true) ∧
        (¬ (iv ∈ aliveIn) → ∀ i, i ∈ x :: rest → insnReadsVReg iv i = false)))
    (h_sim_in : ∀ iv, iv ∈ aliveIn → sPhys.gpr (alloc iv) = sVirt.vreg iv)
    (h_sim_out : ∀ o, o ∈ earlyOuts ++ lateOuts → sPhys.gpr (alloc o) = sVirt.vreg o) :
    sPhys.gpr (alloc s) = sVirt.vreg s := by
  cases hso : (earlyOuts ++ lateOuts).contains s with
  | true => exact h_sim_out s (mem_of_contains_true hso)
  | false =>
    rw [hso, Bool.or_false] at hs_decl
    have hs_in : s ∈ inRegs := mem_of_contains_true hs_decl
    cases hsa : aliveIn.contains s with
    | true => exact h_sim_in s (mem_of_contains_true hsa)
    | false =>
      have hnot_a : ¬ (s ∈ aliveIn) := fun hm => by
        rw [contains_true_of_mem hm] at hsa; cases hsa
      rcases h_not_alive s hs_in hnot_a with ⟨lo, hlo_mem, h_eq⟩
      have h_no_read := (h_dead_or_rbfw s hs_in lo hlo_mem h_eq).2 hnot_a x List.mem_cons_self
      rw [hs_read] at h_no_read
      cases h_no_read

theorem virtual_to_physical_coalescing_aux
    (inRegs earlyOuts lateOuts : List VReg)
    (code : List AsmInsn) (alloc : VReg → Gpr)
    (aliveIn : List VReg)
    (sPhys : MachineState) (sVirt : VirtState)
    (h_pure : checkPureRegBody inRegs (earlyOuts ++ lateOuts) code = true)
    (h_disj_id : ∀ v, v ∈ inRegs → (earlyOuts ++ lateOuts).contains v = false)
    (h_out_dist : checkPairwiseDistinctPhys alloc (earlyOuts ++ lateOuts) = true)
    (h_early_disj : checkEarlyDisjoint alloc earlyOuts inRegs = true)
    (h_alive_sub : ∀ iv, iv ∈ aliveIn → iv ∈ inRegs)
    (h_not_alive : ∀ iv, iv ∈ inRegs → ¬ (iv ∈ aliveIn) → ∃ lo, lo ∈ lateOuts ∧ alloc lo = alloc iv)
    (h_dead_or_rbfw : ∀ iv, iv ∈ inRegs →
      (∀ lo, lo ∈ lateOuts → alloc lo = alloc iv →
        (iv ∈ aliveIn → readBeforeFirstWrite lo iv code = true) ∧
        (¬ (iv ∈ aliveIn) → ∀ i, i ∈ code → insnReadsVReg iv i = false)))
    (h_sim_in : ∀ iv, iv ∈ aliveIn → sPhys.gpr (alloc iv) = sVirt.vreg iv)
    (h_sim_out : ∀ o, o ∈ earlyOuts ++ lateOuts → sPhys.gpr (alloc o) = sVirt.vreg o) :
    ∀ o, o ∈ earlyOuts ++ lateOuts →
      (execInsns code alloc sPhys).gpr (alloc o) = (execInsnsVirt code sVirt).vreg o := by
  induction code generalizing aliveIn sPhys sVirt with
  | nil => exact h_sim_out
  | cons x rest ih =>
    cases x with
    | movImm dst imm =>
      cases dst with
      | fixed _ => simp only [checkPureRegBody] at h_pure; cases h_pure
      | virt d =>
        simp only [checkPureRegBody, Bool.and_eq_true] at h_pure
        have hd_out : d ∈ earlyOuts ++ lateOuts := mem_of_contains_true h_pure.1
        have hx_w : insnWritesVReg d (.movImm (.virt d) imm) = true ∧
            ∀ lo, lo ∈ lateOuts → lo ≠ d → insnWritesVReg lo (.movImm (.virt d) imm) = false :=
          ⟨vreg_beq_refl d, fun lo _ hne => vreg_beq_false_of_ne (Ne.symm hne)⟩
        have hstep := step_pure_write_invariant inRegs earlyOuts lateOuts (.movImm (.virt d) imm) rest
          alloc aliveIn d imm sPhys sVirt hd_out h_disj_id h_out_dist h_early_disj
          h_alive_sub h_not_alive h_dead_or_rbfw hx_w h_sim_in h_sim_out
        exact ih _ _ _ h_pure.2 hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hstep.2.2.2.2
    | movReg dst src =>
      cases dst with
      | fixed _ => simp only [checkPureRegBody] at h_pure; cases h_pure
      | virt d =>
        cases src with
        | fixed _ => simp only [checkPureRegBody] at h_pure; cases h_pure
        | virt s =>
          simp only [checkPureRegBody, Bool.and_eq_true] at h_pure
          have hd_out : d ∈ earlyOuts ++ lateOuts := mem_of_contains_true h_pure.1.1
          have hs_read : insnReadsVReg s (.movReg (.virt d) (.virt s)) = true := by
            simp only [insnReadsVReg, vreg_beq_refl]
          have hs_eq := read_src_eq inRegs earlyOuts lateOuts (.movReg (.virt d) (.virt s)) rest alloc
            aliveIn s sPhys sVirt h_pure.1.2 hs_read h_not_alive h_dead_or_rbfw h_sim_in h_sim_out
          have hx_w : insnWritesVReg d (.movReg (.virt d) (.virt s)) = true ∧
              ∀ lo, lo ∈ lateOuts → lo ≠ d → insnWritesVReg lo (.movReg (.virt d) (.virt s)) = false :=
            ⟨vreg_beq_refl d, fun lo _ hne => vreg_beq_false_of_ne (Ne.symm hne)⟩
          have hstep := step_pure_write_invariant inRegs earlyOuts lateOuts (.movReg (.virt d) (.virt s)) rest
            alloc aliveIn d (sVirt.vreg s) sPhys sVirt hd_out h_disj_id h_out_dist h_early_disj
            h_alive_sub h_not_alive h_dead_or_rbfw hx_w h_sim_in h_sim_out
          simp only [execInsns, execInsnsVirt, execInsn, execInsnVirt, RegRef.resolve, hs_eq]
          exact ih _ _ _ h_pure.2 hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hstep.2.2.2.2
    | addReg dst src =>
      cases dst with
      | fixed _ => simp only [checkPureRegBody] at h_pure; cases h_pure
      | virt d =>
        cases src with
        | fixed _ => simp only [checkPureRegBody] at h_pure; cases h_pure
        | virt s =>
          simp only [checkPureRegBody, Bool.and_eq_true] at h_pure
          have hd_out : d ∈ earlyOuts ++ lateOuts := mem_of_contains_true h_pure.1.1
          have hs_read : insnReadsVReg s (.addReg (.virt d) (.virt s)) = true := by
            simp only [insnReadsVReg, vreg_beq_refl, Bool.or_true]
          have hs_eq := read_src_eq inRegs earlyOuts lateOuts (.addReg (.virt d) (.virt s)) rest alloc
            aliveIn s sPhys sVirt h_pure.1.2 hs_read h_not_alive h_dead_or_rbfw h_sim_in h_sim_out
          have hd_eq : sPhys.gpr (alloc d) = sVirt.vreg d := h_sim_out d hd_out
          have hx_w : insnWritesVReg d (.addReg (.virt d) (.virt s)) = true ∧
              ∀ lo, lo ∈ lateOuts → lo ≠ d → insnWritesVReg lo (.addReg (.virt d) (.virt s)) = false :=
            ⟨vreg_beq_refl d, fun lo _ hne => vreg_beq_false_of_ne (Ne.symm hne)⟩
          have hstep := step_pure_write_invariant inRegs earlyOuts lateOuts (.addReg (.virt d) (.virt s)) rest
            alloc aliveIn d (sVirt.vreg d + sVirt.vreg s) sPhys sVirt hd_out h_disj_id h_out_dist h_early_disj
            h_alive_sub h_not_alive h_dead_or_rbfw hx_w h_sim_in h_sim_out
          simp only [execInsns, execInsnsVirt, execInsn, execInsnVirt, RegRef.resolve, hd_eq, hs_eq]
          exact ih _ _ _ h_pure.2 hstep.1 hstep.2.1 hstep.2.2.1 hstep.2.2.2.1 hstep.2.2.2.2
    | pushReg _ | popReg _ | loadHeap _ _ | storeHeap _ _ | writeFlags _ | touchCsr _ | abiCall _ _ =>
      simp only [checkPureRegBody] at h_pure; cases h_pure

/-- Top-level `virtual_to_physical_coalescing_soundness`:
    Under `checkInlineAsmContract`, distinct output registers, and `checkPureRegBody`,
    any `earlyOut`/`lateOut` allocation (including `lateOut` aliasing `inReg` when
    `readBeforeFirstWrite` holds) computes identical output values to unaliased virtual execution. -/
theorem virtual_to_physical_coalescing_soundness
    (c : InlineAsmContract) (alloc : VReg → Gpr)
    (sPhys : MachineState) (sVirt : VirtState)
    (h_contract : checkInlineAsmContract c alloc = true)
    (h_pure : checkPureRegBody c.inRegs (c.earlyOutRegs ++ c.lateOutRegs) c.code = true)
    (h_disj_id : ∀ v, v ∈ c.inRegs → (c.earlyOutRegs ++ c.lateOutRegs).contains v = false)
    (h_out_dist : checkPairwiseDistinctPhys alloc (c.earlyOutRegs ++ c.lateOutRegs) = true)
    (h_init_in : ∀ iv, iv ∈ c.inRegs → sPhys.gpr (alloc iv) = sVirt.vreg iv)
    (h_init_out : ∀ o, o ∈ c.earlyOutRegs ++ c.lateOutRegs → sPhys.gpr (alloc o) = sVirt.vreg o) :
    ∀ o, o ∈ c.earlyOutRegs ++ c.lateOutRegs →
      (execInsns c.code alloc sPhys).gpr (alloc o) = (execInsnsVirt c.code sVirt).vreg o := by
  simp only [checkInlineAsmContract, Bool.and_eq_true] at h_contract
  have h_early := h_contract.1.1.1.1.1.2
  have h_late  := h_contract.1.1.1.1.2
  refine virtual_to_physical_coalescing_aux c.inRegs c.earlyOutRegs c.lateOutRegs c.code alloc
    c.inRegs sPhys sVirt h_pure h_disj_id h_out_dist h_early
    (fun _ h => h)
    (fun iv _ hnot => False.elim (hnot (by assumption)))
    ?_ h_init_in h_init_out
  intro iv hiv_in lo hlo_mem h_eq
  constructor
  · intro _
    have ha1 := all_forall_mem h_late lo hlo_mem
    have ha2 := all_forall_mem ha1 iv hiv_in
    cases hne : (alloc lo != alloc iv) with
    | true =>
      rw [h_eq, bne_self_eq_false] at hne
      cases hne
    | false =>
      rw [hne, Bool.false_or] at ha2
      exact ha2
  · intro hnot
    exact False.elim (hnot hiv_in)

/-! ## Part 4: Sharpness Counterexamples (CE1 & CE2) -/

/-- CE1 (`lateout` vs. `out` aliasing bug):
    Body: `mov {out}, 0; add {out}, {inp}` (`vOut = 1`, `vInp = 0`).
    1. `readBeforeFirstWrite vOut vInp ce1Code = false` (because `vOut` is written BEFORE `vInp` is read).
    2. An allocator ignoring `readBeforeFirstWrite` (e.g., an unsound `lateout(reg)` annotation
       where LLVM sees `=r,r`) can assign `allocBad vOut = .rax = allocBad vInp`, corrupting `42` -> `0` (`0 ≠ 42`).
    3. Under `out(reg)` (`earlyOutRegs = [1]`), `checkInlineAsmContract` rejects `allocBad` (`false`),
       while for EVERY contract-valid `allocGood` and EVERY input `val : Nat`, execution yields `val`! -/
def ce1Code : List AsmInsn :=
  [.movImm (.virt 1) 0, .addReg (.virt 1) (.virt 0)]

def ce1EarlyOutContract : InlineAsmContract where
  arch := .x86_64
  reserveX18 := true
  inRegs := [0]
  earlyOutRegs := [1]
  lateOutRegs := []
  clobberAbi := .none
  opts := { pure_ := true, nomem := true, nostack := true }
  code := ce1Code

def ce1AllocBad : VReg → Gpr
  | _ => .rax

def ce1AllocGood : VReg → Gpr
  | 0 => .rax
  | _ => .rcx

def ce1MkState (val : Nat) : MachineState where
  gpr        := fun r => if r == .rax then val else 0
  simd       := fun _ => ⟨0, 0⟩
  flags      := 0
  rsp        := 100
  stackMem   := fun _ => 0
  heapMem    := fun _ => 0
  hwCsrState := 0

theorem ce1_lateout_aliasing_bug_and_earlyout_fix :
    readBeforeFirstWrite 1 0 ce1Code = false ∧
    checkInlineAsmContract ce1EarlyOutContract ce1AllocBad = false ∧
    (execInsns ce1Code ce1AllocBad (ce1MkState 42)).gpr (ce1AllocBad 1) = 0 ∧
    (execInsnsVirt ce1Code { vreg := fun v => if v == 0 then 42 else 0 }).vreg 1 = 42 ∧
    checkInlineAsmContract ce1EarlyOutContract ce1AllocGood = true ∧
    (∀ (alloc : VReg → Gpr) (val : Nat) (s : MachineState),
      checkInlineAsmContract ce1EarlyOutContract alloc = true →
      s.gpr (alloc 0) = val →
      (execInsns ce1Code alloc s).gpr (alloc 1) = val) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro alloc val s h_ok h_in
  simp only [ce1EarlyOutContract, checkInlineAsmContract, checkEarlyDisjoint,
    List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h_ok
  have h_bne : (alloc 1 != alloc 0) = true := h_ok.1.1.1.1.1.2
  have h_ne : alloc 1 ≠ alloc 0 := by
    intro heq
    rw [heq, bne_self_eq_false] at h_bne
    cases h_bne
  have h_ne_sym : alloc 0 ≠ alloc 1 := Ne.symm h_ne
  simp only [ce1Code, execInsns, execInsn, RegRef.resolve]
  rw [updateGpr_eq, updateGpr_eq, updateGpr_ne s.gpr h_ne_sym, h_in, Nat.zero_add]

/-- CE2 (`options(nostack)` red-zone clobber on `x86_64` SysV):
    Leaf caller keeps live local `canary = 0x444444444444cccc` at `[rsp0 - 8]` (word `rsp0 - 1`).
    Body `push rax; pop rax` fails `checkBodyNoStack`; running with `prologueSubRsp128 = false`
    (`options(nostack)`) overwrites `stackMem (rsp0 - 1)` with `s.gpr .rax` (`0 ≠ 0x444444444444cccc`),
    whereas `!nostack` (`prologueSubRsp128 = true`) preserves `canary` for ALL `canary : Nat`. -/
def ce2Code : List AsmInsn :=
  [.pushReg (.fixed .rax), .popReg (.fixed .rax)]

def ce2Canary : Nat := 0x444444444444cccc

def ce2State (rsp0 canary : Nat) : MachineState where
  gpr        := fun _ => 0
  simd       := fun _ => ⟨0, 0⟩
  flags      := 0
  rsp        := rsp0
  stackMem   := fun a => if a = rsp0 - 1 then canary else 0
  heapMem    := fun _ => 0
  hwCsrState := 0

theorem ce2_nostack_redzone_clobber_and_default_fix :
    checkBodyNoStack ce2Code = false ∧
    (execFramed false ce2Code (fun _ => .rax) (ce2State 100 ce2Canary)).rsp = 100 ∧
    (execFramed false ce2Code (fun _ => .rax) (ce2State 100 ce2Canary)).stackMem 99 = 0 ∧
    0 ≠ ce2Canary ∧
    (∀ (rsp0 canary : Nat), 17 ≤ rsp0 →
      (execFramed true ce2Code (fun _ => .rax) (ce2State rsp0 canary)).stackMem (rsp0 - 1) = canary) := by
  refine ⟨rfl, rfl, rfl, by decide, ?_⟩
  intro rsp0 canary h_rsp
  simp only [execFramed, ite_true, ce2Code, execInsns, execInsn, RegRef.resolve]
  have h_pos16 : 1 ≤ rsp0 - 16 := Nat.le_sub_of_add_le' h_rsp
  have h_lt : (rsp0 - 16) - 1 < rsp0 - 16 := Nat.sub_lt h_pos16 (Nat.succ_pos 0)
  have h_le16 : rsp0 - 16 ≤ rsp0 - 1 := Nat.sub_le_sub_left (by decide : 1 ≤ 16) rsp0
  have h_ne_addr : rsp0 - 1 ≠ (rsp0 - 16) - 1 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le h_lt h_le16)
  dsimp only [ce2State]
  rw [updateMem_ne _ h_ne_addr]
  exact ite_eq_left rfl

/-! ## Part 5: Constructive `HiLo64` `u128` Division-Remainder (`__udivti3` / `__umodti3`) -/

def W64 : Nat := 2 ^ 64

theorem W64_pos : 0 < W64 := by
  unfold W64
  exact Nat.pow_pos (by decide : 0 < 2)

theorem W64_gt_one : 1 < W64 := by
  unfold W64
  exact Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 1 ≤ 64))

structure HiLo64 where
  hi : Nat
  lo : Nat
  deriving DecidableEq, Repr

def HiLo64.WellFormed (x : HiLo64) : Prop :=
  x.hi < W64 ∧ x.lo < W64

def HiLo64.toNat (x : HiLo64) : Nat :=
  x.hi * W64 + x.lo

theorem HiLo64.toNat_lt_2pow128 {x : HiLo64} (hx : x.WellFormed) :
    x.toNat < W64 * W64 := by
  unfold HiLo64.toNat
  have h_hi : x.hi + 1 ≤ W64 := hx.1
  have h_mul : (x.hi + 1) * W64 ≤ W64 * W64 := Nat.mul_le_mul_right W64 h_hi
  rw [Nat.right_distrib, Nat.one_mul] at h_mul
  have h_sum : x.hi * W64 + x.lo < x.hi * W64 + W64 := Nat.add_lt_add_left hx.2 (x.hi * W64)
  exact Nat.lt_of_lt_of_le h_sum h_mul

/-- Extract bit `idx` (`0 ≤ idx < 128`) using only 64-bit limb shifts. -/
def bitAt128 (n : HiLo64) (idx : Nat) : Nat :=
  if Nat.blt idx 64 then
    (n.lo / 2 ^ idx) % 2
  else
    (n.hi / 2 ^ (idx - 64)) % 2

theorem bitAt128_lt_two (n : HiLo64) (idx : Nat) : bitAt128 n idx < 2 := by
  unfold bitAt128
  cases Nat.blt idx 64 with
  | true => rw [if_tt]; exact Nat.mod_lt _ (by decide : 0 < 2)
  | false => rw [if_ff]; exact Nat.mod_lt _ (by decide : 0 < 2)

theorem W64_mul_W64_eq : W64 * W64 = 2 ^ 128 := by
  unfold W64
  rw [← Nat.pow_add]

theorem bitAt128_eq_div_mod (n : HiLo64) (hn : n.WellFormed) (idx : Nat) (_hidx : idx < 128) :
    bitAt128 n idx = (n.toNat / 2 ^ idx) % 2 := by
  unfold bitAt128 HiLo64.toNat
  cases hlt : Nat.blt idx 64 with
  | true =>
    rw [if_tt]
    have h64 : idx < 64 := blt_lt hlt
    have hle : idx ≤ 63 := Nat.le_pred_of_lt h64
    have hsum : idx + ((63 - idx) + 1) = 64 := by
      rw [← Nat.add_assoc, Nat.add_comm idx (63 - idx), Nat.sub_add_cancel hle]
    have hpow : W64 = (2 ^ (63 - idx) * 2) * 2 ^ idx := by
      unfold W64
      rw [← hsum, Nat.pow_add, Nat.pow_succ, Nat.mul_comm (2 ^ idx)]
    have hp2 : 0 < 2 ^ idx := Nat.pow_pos (by decide : 0 < 2)
    rw [hpow, ← Nat.mul_assoc n.hi (2 ^ (63 - idx) * 2) (2 ^ idx)]
    rw [Nat.add_comm (n.hi * (2 ^ (63 - idx) * 2) * 2 ^ idx) n.lo]
    rw [Nat.add_mul_div_right n.lo (n.hi * (2 ^ (63 - idx) * 2)) hp2]
    rw [← Nat.mul_assoc n.hi (2 ^ (63 - idx)) 2]
    exact Eq.symm (Nat.add_mul_mod_self_right (n.lo / 2 ^ idx) (n.hi * 2 ^ (63 - idx)) 2)
  | false =>
    rw [if_ff]
    have hge : 64 ≤ idx := by
      cases Nat.lt_or_ge idx 64 with
      | inl h =>
        have hb : Nat.blt idx 64 = true := Nat.blt_eq.mpr h
        rw [hb] at hlt
        cases hlt
      | inr h => exact h
    have hsum : 64 + (idx - 64) = idx := Nat.add_sub_of_le hge
    have hpow : 2 ^ idx = W64 * 2 ^ (idx - 64) := by
      have hp : 2 ^ (64 + (idx - 64)) = W64 * 2 ^ (idx - 64) := by
        unfold W64
        exact Nat.pow_add 2 64 (idx - 64)
      rw [hsum] at hp
      exact hp
    rw [hpow, ← Nat.div_div_eq_div_mul]
    rw [Nat.add_comm (n.hi * W64) n.lo, Nat.add_mul_div_right n.lo n.hi W64_pos]
    rw [Nat.div_eq_of_lt hn.2, Nat.zero_add]

/-- Pure 64-bit limb left-shift by 1 plus 1 incoming bit, returning `(carry128, newLo64Pair)`. -/
def shl1AddBit129 (x : HiLo64) (b : Nat) : Bool × HiLo64 :=
  let lo2 := 2 * x.lo + b
  let loCarry := if Nat.ble W64 lo2 then 1 else 0
  let loNew := if Nat.ble W64 lo2 then lo2 - W64 else lo2
  let hi2 := 2 * x.hi + loCarry
  let hiCarry := Nat.ble W64 hi2
  let hiNew := if hiCarry then hi2 - W64 else hi2
  (hiCarry, ⟨hiNew, loNew⟩)

def shl1AddBit128 (x : HiLo64) (b : Nat) : HiLo64 :=
  (shl1AddBit129 x b).2

theorem ble_iff_le (a b : Nat) : Nat.ble a b = true ↔ a ≤ b := by
  cases h : Nat.ble a b with
  | true => exact ⟨fun _ => Nat.le_of_ble_eq_true h, fun _ => rfl⟩
  | false =>
    constructor
    · intro hh; cases hh
    · intro hle
      have ht : Nat.ble a b = true := Nat.ble_eq.mpr hle
      rw [ht] at h; cases h

theorem ble_false_iff_lt (a b : Nat) : Nat.ble a b = false ↔ b < a := by
  cases h : Nat.ble a b with
  | false =>
    constructor
    · intro _
      cases Nat.lt_or_ge b a with
      | inl hlt => exact hlt
      | inr hle =>
        have ht : Nat.ble a b = true := Nat.ble_eq.mpr hle
        rw [ht] at h; cases h
    · intro _; rfl
  | true =>
    have hle : a ≤ b := Nat.le_of_ble_eq_true h
    constructor
    · intro hh; cases hh
    · intro hlt; exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle hlt))

theorem blt_false_iff_le (a b : Nat) : Nat.blt a b = false ↔ b ≤ a := by
  cases h : Nat.blt a b with
  | false =>
    constructor
    · intro _
      cases Nat.lt_or_ge a b with
      | inl hlt =>
        have ht : Nat.blt a b = true := Nat.blt_eq.mpr hlt
        rw [ht] at h; cases h
      | inr hle => exact hle
    · intro _; rfl
  | true =>
    have hlt : a < b := blt_lt h
    constructor
    · intro hh; cases hh
    · intro hle; exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle))

theorem mul_two_add_lt_twice {v b B : Nat} (hv : v < B) (hb : b < 2) :
    2 * v + b < B + B := by
  have h1 : 2 * v + b < 2 * v + 2 := Nat.add_lt_add_left hb (2 * v)
  have h2 : 2 * v + 2 = 2 * (v + 1) := by rw [Nat.mul_succ]
  have h3 : 2 * (v + 1) ≤ 2 * B := Nat.mul_le_mul_left 2 hv
  have h4 : 2 * B = B + B := Nat.two_mul B
  rw [h2] at h1
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1 h3) (Nat.le_of_eq h4)

theorem shl1AddBit129_spec (x : HiLo64) (hx : x.WellFormed) (b : Nat) (hb : b < 2) :
    let res := shl1AddBit129 x b
    res.2.WellFormed ∧
    (if res.1 then W64 * W64 else 0) + res.2.toNat = 2 * x.toNat + b := by
  unfold shl1AddBit129 HiLo64.WellFormed HiLo64.toNat
  dsimp only
  have hlo_lt2 : 2 * x.lo + b < W64 + W64 := mul_two_add_lt_twice hx.2 hb
  have h_lo_split :
      (if Nat.ble W64 (2 * x.lo + b) = true then 1 else 0) * W64 +
      (if Nat.ble W64 (2 * x.lo + b) = true then (2 * x.lo + b) - W64 else 2 * x.lo + b) =
        2 * x.lo + b ∧
      (if Nat.ble W64 (2 * x.lo + b) = true then (2 * x.lo + b) - W64 else 2 * x.lo + b) < W64 ∧
      (if Nat.ble W64 (2 * x.lo + b) = true then 1 else 0) < 2 := by
    cases hbl : Nat.ble W64 (2 * x.lo + b) with
    | true =>
      have hge : W64 ≤ 2 * x.lo + b := (ble_iff_le W64 (2 * x.lo + b)).mp hbl
      repeat rw [if_tt]
      rw [Nat.one_mul]
      exact ⟨Nat.add_sub_of_le hge, Nat.sub_lt_left_of_lt_add hge hlo_lt2, by decide⟩
    | false =>
      have hlt : 2 * x.lo + b < W64 := (ble_false_iff_lt W64 (2 * x.lo + b)).mp hbl
      repeat rw [if_ff]
      rw [Nat.zero_mul, Nat.zero_add]
      exact ⟨rfl, hlt, by decide⟩
  have hhi_lt2 :
      2 * x.hi + (if Nat.ble W64 (2 * x.lo + b) = true then 1 else 0) < W64 + W64 :=
    mul_two_add_lt_twice hx.1 h_lo_split.2.2
  cases hbh : Nat.ble W64 (2 * x.hi + if Nat.ble W64 (2 * x.lo + b) = true then 1 else 0) with
  | true =>
    have hge_hi : W64 ≤ 2 * x.hi + if Nat.ble W64 (2 * x.lo + b) = true then 1 else 0 :=
      (ble_iff_le _ _).mp hbh
    repeat rw [if_tt]
    refine ⟨⟨Nat.sub_lt_left_of_lt_add hge_hi hhi_lt2, h_lo_split.2.1⟩, ?_⟩
    rw [← Nat.add_assoc, ← Nat.right_distrib, Nat.add_sub_of_le hge_hi]
    rw [Nat.right_distrib, Nat.add_assoc, h_lo_split.1]
    rw [← Nat.add_assoc, Nat.mul_assoc 2 x.hi W64, Nat.mul_comm x.hi W64]
    rw [Nat.mul_add 2 (W64 * x.hi) x.lo]
  | false =>
    have hlt_hi : 2 * x.hi + (if Nat.ble W64 (2 * x.lo + b) = true then 1 else 0) < W64 :=
      (ble_false_iff_lt _ _).mp hbh
    repeat rw [if_ff]
    rw [Nat.zero_add]
    refine ⟨⟨hlt_hi, h_lo_split.2.1⟩, ?_⟩
    rw [Nat.right_distrib, Nat.add_assoc, h_lo_split.1]
    rw [← Nat.add_assoc, Nat.mul_assoc 2 x.hi W64, ← Nat.mul_add 2 (x.hi * W64) x.lo]

theorem shl1AddBit128_spec (x : HiLo64) (hx : x.WellFormed) (hx_half : 2 * x.toNat + 1 < W64 * W64)
    (b : Nat) (hb : b < 2) :
    (shl1AddBit128 x b).WellFormed ∧ (shl1AddBit128 x b).toNat = 2 * x.toNat + b := by
  unfold shl1AddBit128
  have hs := shl1AddBit129_spec x hx b hb
  dsimp only at hs
  constructor
  · exact hs.1
  · have hsum_lt : 2 * x.toNat + b < W64 * W64 := by
      have hle : b ≤ 1 := Nat.le_pred_of_lt hb
      exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hle _) hx_half
    cases hc : (shl1AddBit129 x b).1 with
    | false =>
      rw [hc, if_ff, Nat.zero_add] at hs
      exact hs.2
    | true =>
      rw [hc, if_tt] at hs
      have hge : W64 * W64 ≤ 2 * x.toNat + b := by
        rw [← hs.2]
        exact Nat.le_add_right _ _
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hge hsum_lt))

/-- Pure 64-bit limb comparison: `b ≤ carry * 2^128 + a`. -/
def cmpGe129 (carry : Bool) (a b : HiLo64) : Bool :=
  if carry then true
  else if Nat.blt b.hi a.hi then true
  else if Nat.blt a.hi b.hi then false
  else Nat.ble b.lo a.lo

theorem hilo_lt_of_hi_lt {x y : HiLo64} (hx : x.WellFormed) (h_hi : x.hi < y.hi) :
    x.toNat < y.toNat := by
  unfold HiLo64.toNat
  have h1 : x.hi * W64 + x.lo < x.hi * W64 + W64 := Nat.add_lt_add_left hx.2 (x.hi * W64)
  have h2 : x.hi * W64 + W64 = (x.hi + 1) * W64 := by
    rw [Nat.right_distrib, Nat.one_mul]
  have h3 : (x.hi + 1) * W64 ≤ y.hi * W64 := Nat.mul_le_mul_right W64 h_hi
  have h4 : y.hi * W64 ≤ y.hi * W64 + y.lo := Nat.le_add_right _ _
  rw [h2] at h1
  exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h3 h4)

theorem cmpGe129_iff (carry : Bool) (a b : HiLo64) (ha : a.WellFormed) (hb : b.WellFormed) :
    cmpGe129 carry a b = true ↔ b.toNat ≤ (if carry then W64 * W64 else 0) + a.toNat := by
  cases carry with
  | true =>
    unfold cmpGe129
    repeat rw [if_tt]
    exact ⟨fun _ => Nat.le_trans (Nat.le_of_lt (HiLo64.toNat_lt_2pow128 hb)) (Nat.le_add_right _ _),
           fun _ => rfl⟩
  | false =>
    unfold cmpGe129
    repeat rw [if_ff]
    rw [Nat.zero_add]
    cases hba : Nat.blt b.hi a.hi with
    | true =>
      have hlt : b.hi < a.hi := blt_lt hba
      rw [if_tt]
      exact ⟨fun _ => Nat.le_of_lt (hilo_lt_of_hi_lt hb hlt), fun _ => rfl⟩
    | false =>
      have hge_ba : a.hi ≤ b.hi := (blt_false_iff_le b.hi a.hi).mp hba
      rw [if_ff]
      cases hab : Nat.blt a.hi b.hi with
      | true =>
        have hlt : a.hi < b.hi := blt_lt hab
        have h_at_lt_bt : a.toNat < b.toNat := hilo_lt_of_hi_lt ha hlt
        rw [if_tt]
        exact ⟨fun hh => False.elim (Bool.noConfusion hh),
               fun hle => False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_at_lt_bt hle))⟩
      | false =>
        have hge_ab : b.hi ≤ a.hi := (blt_false_iff_le a.hi b.hi).mp hab
        have heq_hi : a.hi = b.hi := Nat.le_antisymm hge_ba hge_ab
        rw [if_ff]
        unfold HiLo64.toNat
        rw [heq_hi]
        exact ⟨fun hble => Nat.add_le_add_left ((ble_iff_le b.lo a.lo).mp hble) (b.hi * W64),
               fun hle => (ble_iff_le b.lo a.lo).mpr (Nat.le_of_add_le_add_left hle)⟩

/-- Pure 64-bit limb subtraction with borrow: `(carry * 2^128 + a) - b`. -/
def sub129 (a b : HiLo64) : HiLo64 :=
  let borrow := if Nat.blt a.lo b.lo then 1 else 0
  let loNew := if Nat.blt a.lo b.lo then a.lo + W64 - b.lo else a.lo - b.lo
  let bHiAdj := b.hi + borrow
  let hiNew := if Nat.blt a.hi bHiAdj then a.hi + W64 - bHiAdj else a.hi - bHiAdj
  ⟨hiNew, loNew⟩

theorem sub129_reassoc (A B L b_lo : Nat) :
    A * W64 + L + (B * W64 + b_lo) = (A + B) * W64 + (L + b_lo) := by
  rw [Nat.add_assoc (A * W64) L (B * W64 + b_lo)]
  rw [Nat.add_comm L (B * W64 + b_lo)]
  rw [Nat.add_assoc (B * W64) b_lo L]
  rw [← Nat.add_assoc (A * W64) (B * W64) (b_lo + L)]
  rw [← Nat.right_distrib, Nat.add_comm b_lo L]

theorem reassoc_carry (A B a_lo : Nat) :
    (A + B) * W64 + (a_lo + W64) = (A + (B + 1)) * W64 + a_lo := by
  rw [Nat.right_distrib A (B + 1) W64, Nat.right_distrib B 1 W64, Nat.one_mul]
  rw [← Nat.add_assoc (A * W64) (B * W64) W64, ← Nat.right_distrib A B W64]
  rw [Nat.add_assoc ((A + B) * W64) W64 a_lo, Nat.add_comm W64 a_lo]

theorem sub129_spec (carry : Bool) (a b : HiLo64) (ha : a.WellFormed) (hb : b.WellFormed)
    (hle : b.toNat ≤ (if carry then W64 * W64 else 0) + a.toNat)
    (hlt : (if carry then W64 * W64 else 0) + a.toNat - b.toNat < W64 * W64) :
    (sub129 a b).WellFormed ∧
    (sub129 a b).toNat + b.toNat = (if carry then W64 * W64 else 0) + a.toNat := by
  unfold sub129 HiLo64.WellFormed HiLo64.toNat
  dsimp only
  cases hbl : Nat.blt a.lo b.lo with
  | false =>
    have h_le_lo : b.lo ≤ a.lo := (blt_false_iff_le a.lo b.lo).mp hbl
    repeat rw [if_ff]
    rw [Nat.add_zero]
    have hlo_wf : a.lo - b.lo < W64 := Nat.lt_of_le_of_lt (Nat.sub_le a.lo b.lo) ha.2
    cases carry with
    | false =>
      rw [if_ff, Nat.zero_add] at hle hlt ⊢
      have h_le_hi : b.hi ≤ a.hi := by
        cases Nat.lt_or_ge a.hi b.hi with
        | inr hge => exact hge
        | inl hlt_hi =>
          exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hilo_lt_of_hi_lt ha hlt_hi) hle))
      have hbh : Nat.blt a.hi b.hi = false := (blt_false_iff_le a.hi b.hi).mpr h_le_hi
      rw [hbh, if_ff]
      refine ⟨⟨Nat.lt_of_le_of_lt (Nat.sub_le a.hi b.hi) ha.1, hlo_wf⟩, ?_⟩
      rw [sub129_reassoc, Nat.sub_add_cancel h_le_hi, Nat.sub_add_cancel h_le_lo]
    | true =>
      rw [if_tt] at hle hlt ⊢
      have ha_lt_b : a.toNat < b.toNat := by
        cases Nat.lt_or_ge a.toNat b.toNat with
        | inl h => exact h
        | inr hge =>
          have hw : W64 * W64 ≤ W64 * W64 + a.toNat - b.toNat := by
            rw [Nat.add_sub_assoc hge]
            exact Nat.le_add_right _ _
          exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hw hlt))
      have h_lt_hi : a.hi < b.hi := by
        cases Nat.lt_or_ge a.hi b.hi with
        | inl h => exact h
        | inr hge =>
          have hb_le : b.toNat ≤ a.toNat := by
            unfold HiLo64.toNat
            exact Nat.add_le_add (Nat.mul_le_mul_right W64 hge) h_le_lo
          exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ha_lt_b hb_le))
      have hbh : Nat.blt a.hi b.hi = true := Nat.blt_eq.mpr h_lt_hi
      rw [hbh, if_tt]
      have h_le_hiw : b.hi ≤ a.hi + W64 := Nat.le_trans (Nat.le_of_lt hb.1) (Nat.le_add_left W64 a.hi)
      have h_lt_hiw : a.hi + W64 < b.hi + W64 := Nat.add_lt_add_right h_lt_hi W64
      refine ⟨⟨Nat.sub_lt_left_of_lt_add h_le_hiw h_lt_hiw, hlo_wf⟩, ?_⟩
      rw [sub129_reassoc, Nat.sub_add_cancel h_le_hiw, Nat.sub_add_cancel h_le_lo]
      rw [Nat.right_distrib, Nat.add_comm (a.hi * W64) (W64 * W64), Nat.add_assoc]
  | true =>
    have h_ab : a.lo < b.lo := blt_lt hbl
    repeat rw [if_tt]
    have h_le_low : b.lo ≤ a.lo + W64 := Nat.le_trans (Nat.le_of_lt hb.2) (Nat.le_add_left W64 a.lo)
    have h_lt_low : a.lo + W64 < b.lo + W64 := Nat.add_lt_add_right h_ab W64
    have hlo_wf : a.lo + W64 - b.lo < W64 := Nat.sub_lt_left_of_lt_add h_le_low h_lt_low
    have hlo_sum : (a.lo + W64 - b.lo) + b.lo = a.lo + W64 := Nat.sub_add_cancel h_le_low
    cases carry with
    | false =>
      rw [if_ff, Nat.zero_add] at hle hlt ⊢
      have h_le_hi : b.hi + 1 ≤ a.hi := by
        cases Nat.lt_or_ge a.hi (b.hi + 1) with
        | inr hge => exact hge
        | inl hlt_hi =>
          have hle_hi : a.hi ≤ b.hi := Nat.le_of_lt_succ hlt_hi
          have h_at_lt_bt : a.toNat < b.toNat := by
            unfold HiLo64.toNat
            exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right W64 hle_hi) h_ab
          exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_at_lt_bt hle))
      have hbh : Nat.blt a.hi (b.hi + 1) = false := (blt_false_iff_le a.hi (b.hi + 1)).mpr h_le_hi
      rw [hbh, if_ff]
      refine ⟨⟨Nat.lt_of_le_of_lt (Nat.sub_le a.hi (b.hi + 1)) ha.1, hlo_wf⟩, ?_⟩
      rw [sub129_reassoc, hlo_sum, reassoc_carry, Nat.sub_add_cancel h_le_hi]
    | true =>
      rw [if_tt] at hle hlt ⊢
      have ha_lt_b : a.toNat < b.toNat := by
        cases Nat.lt_or_ge a.toNat b.toNat with
        | inl h => exact h
        | inr hge =>
          have hw : W64 * W64 ≤ W64 * W64 + a.toNat - b.toNat := by
            rw [Nat.add_sub_assoc hge]
            exact Nat.le_add_right _ _
          exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hw hlt))
      have h_lt_hi : a.hi < b.hi + 1 := by
        cases Nat.lt_or_ge a.hi (b.hi + 1) with
        | inl h => exact h
        | inr hge =>
          have hb_lt_at : b.toNat < a.toNat := by
            unfold HiLo64.toNat
            have h1 : b.hi * W64 + b.lo < (b.hi + 1) * W64 := by
              rw [Nat.right_distrib, Nat.one_mul]
              exact Nat.add_lt_add_left hb.2 (b.hi * W64)
            have h2 : (b.hi + 1) * W64 ≤ a.hi * W64 := Nat.mul_le_mul_right W64 hge
            exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 (Nat.le_add_right _ _))
          exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans ha_lt_b hb_lt_at))
      have hbh : Nat.blt a.hi (b.hi + 1) = true := Nat.blt_eq.mpr h_lt_hi
      rw [hbh, if_tt]
      have h_le_hiw : b.hi + 1 ≤ a.hi + W64 := Nat.le_trans hb.1 (Nat.le_add_left W64 a.hi)
      have h_lt_hiw : a.hi + W64 < (b.hi + 1) + W64 := Nat.add_lt_add_right h_lt_hi W64
      refine ⟨⟨Nat.sub_lt_left_of_lt_add h_le_hiw h_lt_hiw, hlo_wf⟩, ?_⟩
      rw [sub129_reassoc, hlo_sum, reassoc_carry, Nat.sub_add_cancel h_le_hiw]
      rw [Nat.right_distrib, Nat.add_comm (a.hi * W64) (W64 * W64), Nat.add_assoc]

/-- One MSB-to-LSB binary restoring division-remainder step over 64-bit limbs. -/
def divmod128Step (d quo rem : HiLo64) (bit : Nat) : HiLo64 × HiLo64 :=
  let shifted := shl1AddBit129 rem bit
  if cmpGe129 shifted.1 shifted.2 d then
    (shl1AddBit128 quo 1, sub129 shifted.2 d)
  else
    (shl1AddBit128 quo 0, shifted.2)

/-- 128-step MSB-to-LSB binary restoring division-remainder in pure 64-bit limbs. -/
def divmod128Loop (n d quo rem : HiLo64) : Nat → HiLo64 × HiLo64
  | 0 => (quo, rem)
  | stepIdx + 1 =>
    let next := divmod128Step d quo rem (bitAt128 n stepIdx)
    divmod128Loop n d next.1 next.2 stepIdx

def divmod128 (n d : HiLo64) : HiLo64 × HiLo64 :=
  divmod128Loop n d ⟨0, 0⟩ ⟨0, 0⟩ 128

def udivti3 (n d : HiLo64) : HiLo64 := (divmod128 n d).1
def umodti3 (n d : HiLo64) : HiLo64 := (divmod128 n d).2

theorem divmod128Loop_zero (n d quo rem : HiLo64) :
    divmod128Loop n d quo rem 0 = (quo, rem) := rfl

theorem divmod128Loop_succ (n d quo rem : HiLo64) (stepIdx : Nat) :
    divmod128Loop n d quo rem (stepIdx + 1) =
      divmod128Loop n d
        (divmod128Step d quo rem (bitAt128 n stepIdx)).1
        (divmod128Step d quo rem (bitAt128 n stepIdx)).2
        stepIdx := rfl

theorem divmod128_q_half (stepIdx : Nat) (quo : HiLo64)
    (hq_bound : quo.toNat < 2 ^ (128 - (stepIdx + 1))) :
    2 * quo.toNat + 1 < W64 * W64 := by
  rw [W64_mul_W64_eq]
  have h_exp_le : 128 - (stepIdx + 1) ≤ 127 := by
    rw [Nat.succ_sub_succ]
    exact Nat.sub_le 127 stepIdx
  have h_pow_le : 2 ^ (128 - (stepIdx + 1)) ≤ 2 ^ 127 :=
    Nat.pow_le_pow_right (by decide : 0 < 2) h_exp_le
  have h_q_lt127 : quo.toNat < 2 ^ 127 := Nat.lt_of_lt_of_le hq_bound h_pow_le
  have h1 : 2 * quo.toNat + 1 < 2 * (quo.toNat + 1) := by
    rw [Nat.mul_succ]
    exact Nat.lt_succ_self _
  have h2 : 2 * (quo.toNat + 1) ≤ 2 * 2 ^ 127 := Nat.mul_le_mul_left 2 h_q_lt127
  have h3 : 2 * 2 ^ 127 = 2 ^ 128 := by rw [Nat.mul_comm, ← Nat.pow_succ]
  rw [h3] at h2
  exact Nat.lt_of_lt_of_le h1 h2

theorem divmod128_q_next_bound (stepIdx : Nat) (quo : HiLo64)
    (hidx_lt : stepIdx < 128) (hq_bound : quo.toNat < 2 ^ (128 - (stepIdx + 1))) :
    ∀ b, b < 2 → 2 * quo.toNat + b < 2 ^ (128 - stepIdx) := by
  intro b hb
  have h_sub_succ : 128 - stepIdx = (128 - (stepIdx + 1)) + 1 := by
    have hpos : 0 < 128 - stepIdx := Nat.sub_pos_of_lt hidx_lt
    rw [Nat.sub_add_eq, Nat.sub_add_cancel hpos]
  rw [h_sub_succ, Nat.pow_succ, Nat.mul_comm _ 2]
  have h1 : 2 * quo.toNat + b < 2 * quo.toNat + 2 := Nat.add_lt_add_left hb (2 * quo.toNat)
  have h2 : 2 * quo.toNat + 2 = 2 * (quo.toNat + 1) := by rw [Nat.mul_succ]
  have h3 : 2 * (quo.toNat + 1) ≤ 2 * 2 ^ (128 - (stepIdx + 1)) := Nat.mul_le_mul_left 2 hq_bound
  rw [h2] at h1
  exact Nat.lt_of_lt_of_le h1 h3

/-- Modular single-step soundness parameterized over abstract `(c, rShifted, bit)`
    so `divmod128Loop_inv` never duplicates `shl1AddBit129` expressions in the kernel. -/
theorem divmod128Step_true
    (d quo rem rShifted : HiLo64) (c : Bool) (bit divPrev divCur : Nat)
    (hq_wf : quo.WellFormed) (hr_lt : rem.toNat < d.toNat) (hd : d.WellFormed)
    (hb_lt : bit < 2) (hq_half : 2 * quo.toNat + 1 < W64 * W64)
    (hr_wf : rShifted.WellFormed)
    (hT_eq : (if c then W64 * W64 else 0) + rShifted.toNat = 2 * rem.toNat + bit)
    (h_eq : quo.toNat * d.toNat + rem.toNat = divPrev)
    (h_div : divCur = 2 * divPrev + bit)
    (hcmp : cmpGe129 c rShifted d = true) :
    (shl1AddBit128 quo 1).WellFormed ∧
    (sub129 rShifted d).WellFormed ∧
    (sub129 rShifted d).toNat < d.toNat ∧
    (shl1AddBit128 quo 1).toNat * d.toNat + (sub129 rShifted d).toNat = divCur ∧
    (shl1AddBit128 quo 1).toNat = 2 * quo.toNat + 1 := by
  have hT_lt_2d : (if c then W64 * W64 else 0) + rShifted.toNat < d.toNat + d.toNat := by
    rw [hT_eq]
    exact mul_two_add_lt_twice hr_lt hb_lt
  have hle_dT : d.toNat ≤ (if c then W64 * W64 else 0) + rShifted.toNat :=
    (cmpGe129_iff c rShifted d hr_wf hd).mp hcmp
  have hlt_sub_d : (if c then W64 * W64 else 0) + rShifted.toNat - d.toNat < d.toNat :=
    Nat.sub_lt_left_of_lt_add hle_dT hT_lt_2d
  have hlt_sub_w : (if c then W64 * W64 else 0) + rShifted.toNat - d.toNat < W64 * W64 :=
    Nat.lt_trans hlt_sub_d (HiLo64.toNat_lt_2pow128 hd)
  have hsub := sub129_spec c rShifted d hr_wf hd hle_dT hlt_sub_w
  have hrem_lt : (sub129 rShifted d).toNat < d.toNat := by
    rw [← Nat.add_sub_cancel (sub129 rShifted d).toNat d.toNat, hsub.2]
    exact hlt_sub_d
  have hq1 := shl1AddBit128_spec quo hq_wf hq_half 1 (by decide : 1 < 2)
  refine ⟨hq1.1, hsub.1, hrem_lt, ?_, hq1.2⟩
  apply Nat.add_right_cancel (m := d.toNat)
  rw [Nat.add_assoc, hsub.2, hT_eq, hq1.2, Nat.right_distrib, Nat.one_mul]
  rw [Nat.add_assoc (2 * quo.toNat * d.toNat) d.toNat]
  rw [Nat.add_comm d.toNat (2 * rem.toNat + bit)]
  rw [← Nat.add_assoc (2 * quo.toNat * d.toNat)]
  rw [Nat.mul_assoc 2 quo.toNat d.toNat, ← Nat.add_assoc (2 * (quo.toNat * d.toNat)) (2 * rem.toNat) bit]
  rw [← Nat.mul_add 2 (quo.toNat * d.toNat) rem.toNat, h_eq, ← h_div]

theorem divmod128Step_false
    (d quo rem rShifted : HiLo64) (c : Bool) (bit divPrev divCur : Nat)
    (hq_wf : quo.WellFormed) (hd : d.WellFormed)
    (hq_half : 2 * quo.toNat + 1 < W64 * W64)
    (hr_wf : rShifted.WellFormed)
    (hT_eq : (if c then W64 * W64 else 0) + rShifted.toNat = 2 * rem.toNat + bit)
    (h_eq : quo.toNat * d.toNat + rem.toNat = divPrev)
    (h_div : divCur = 2 * divPrev + bit)
    (hcmp : cmpGe129 c rShifted d = false) :
    (shl1AddBit128 quo 0).WellFormed ∧
    rShifted.WellFormed ∧
    rShifted.toNat < d.toNat ∧
    (shl1AddBit128 quo 0).toNat * d.toNat + rShifted.toNat = divCur ∧
    (shl1AddBit128 quo 0).toNat = 2 * quo.toNat := by
  have hnot_le : ¬ (d.toNat ≤ (if c then W64 * W64 else 0) + rShifted.toNat) := by
    intro hle
    have ht := (cmpGe129_iff c rShifted d hr_wf hd).mpr hle
    rw [ht] at hcmp; cases hcmp
  have hT_lt_d : (if c then W64 * W64 else 0) + rShifted.toNat < d.toNat := by
    cases Nat.lt_or_ge ((if c then W64 * W64 else 0) + rShifted.toNat) d.toNat with
    | inl hlt => exact hlt
    | inr hle => exact False.elim (hnot_le hle)
  have h_c_false : c = false := by
    cases hc : c with
    | false => rfl
    | true =>
      have hh : cmpGe129 true rShifted d = true := by unfold cmpGe129; exact if_tt _ _
      rw [hc, hh] at hcmp; cases hcmp
  rw [ite_false_eq h_c_false, Nat.zero_add] at hT_lt_d hT_eq
  have hq0 := shl1AddBit128_spec quo hq_wf hq_half 0 (by decide : 0 < 2)
  refine ⟨hq0.1, hr_wf, hT_lt_d, ?_, by rw [hq0.2, Nat.add_zero]⟩
  rw [hq0.2, Nat.add_zero, hT_eq, Nat.mul_assoc 2 quo.toNat d.toNat]
  rw [← Nat.add_assoc, ← Nat.mul_add 2 (quo.toNat * d.toNat) rem.toNat, h_eq, ← h_div]

theorem divmod128Step_spec
    (d quo rem : HiLo64) (bit divPrev divCur qLim : Nat)
    (hq_wf : quo.WellFormed) (hr_wf : rem.WellFormed) (hr_lt : rem.toNat < d.toNat) (hd : d.WellFormed)
    (hb_lt : bit < 2) (hq_half : 2 * quo.toNat + 1 < W64 * W64)
    (h_eq : quo.toNat * d.toNat + rem.toNat = divPrev)
    (h_div : divCur = 2 * divPrev + bit)
    (hq_lim : ∀ b, b < 2 → 2 * quo.toNat + b < qLim) :
    (divmod128Step d quo rem bit).1.WellFormed ∧
    (divmod128Step d quo rem bit).2.WellFormed ∧
    (divmod128Step d quo rem bit).2.toNat < d.toNat ∧
    (divmod128Step d quo rem bit).1.toNat * d.toNat + (divmod128Step d quo rem bit).2.toNat = divCur ∧
    (divmod128Step d quo rem bit).1.toNat < qLim := by
  have hsh := shl1AddBit129_spec rem hr_wf bit hb_lt
  dsimp only at hsh
  cases hcmp : cmpGe129 (shl1AddBit129 rem bit).1 (shl1AddBit129 rem bit).2 d with
  | true =>
    have hstep : divmod128Step d quo rem bit = (shl1AddBit128 quo 1, sub129 (shl1AddBit129 rem bit).2 d) := by
      unfold divmod128Step
      exact ite_eq_left hcmp
    rw [hstep]
    have hs := divmod128Step_true d quo rem (shl1AddBit129 rem bit).2 (shl1AddBit129 rem bit).1
      bit divPrev divCur hq_wf hr_lt hd hb_lt hq_half hsh.1 hsh.2 h_eq h_div hcmp
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
    rw [hs.2.2.2.2]
    exact hq_lim 1 (by decide : 1 < 2)
  | false =>
    have hstep : divmod128Step d quo rem bit = (shl1AddBit128 quo 0, (shl1AddBit129 rem bit).2) := by
      unfold divmod128Step
      exact ite_false_eq hcmp _ _
    rw [hstep]
    have hs := divmod128Step_false d quo rem (shl1AddBit129 rem bit).2 (shl1AddBit129 rem bit).1
      bit divPrev divCur hq_wf hd hq_half hsh.1 hsh.2 h_eq h_div hcmp
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
    rw [hs.2.2.2.2]
    have h0 := hq_lim 0 (by decide : 0 < 2)
    rw [Nat.add_zero] at h0
    exact h0

theorem divmod128Loop_inv (n d : HiLo64) (hn : n.WellFormed) (hd : d.WellFormed) (_hd_pos : 0 < d.toNat) :
    ∀ (k : Nat) (quo rem : HiLo64),
      k ≤ 128 →
      quo.WellFormed →
      rem.WellFormed →
      rem.toNat < d.toNat →
      quo.toNat * d.toNat + rem.toNat = n.toNat / 2 ^ k →
      quo.toNat < 2 ^ (128 - k) →
      (divmod128Loop n d quo rem k).1.WellFormed ∧
      (divmod128Loop n d quo rem k).2.WellFormed ∧
      (divmod128Loop n d quo rem k).1.toNat * d.toNat + (divmod128Loop n d quo rem k).2.toNat = n.toNat ∧
      (divmod128Loop n d quo rem k).2.toNat < d.toNat := by
  intro k
  induction k with
  | zero =>
    intro quo rem _ hq_wf hr_wf hr_lt h_eq _
    rw [divmod128Loop_zero]
    rw [Nat.pow_zero, Nat.div_one] at h_eq
    exact ⟨hq_wf, hr_wf, h_eq, hr_lt⟩
  | succ stepIdx ih =>
    intro quo rem hk_le hq_wf hr_wf hr_lt h_eq hq_bound
    have hidx_lt : stepIdx < 128 := hk_le
    have hbit_lt : bitAt128 n stepIdx < 2 := bitAt128_lt_two n stepIdx
    have hbit_eq : bitAt128 n stepIdx = (n.toNat / 2 ^ stepIdx) % 2 :=
      bitAt128_eq_div_mod n hn stepIdx hidx_lt
    have h_div_step : n.toNat / 2 ^ stepIdx = 2 * (n.toNat / 2 ^ (stepIdx + 1)) + bitAt128 n stepIdx := by
      rw [hbit_eq, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
      exact Eq.symm (Nat.div_add_mod (n.toNat / 2 ^ stepIdx) 2)
    have h_q_half : 2 * quo.toNat + 1 < W64 * W64 := divmod128_q_half stepIdx quo hq_bound
    have h_q_next_bound : ∀ b, b < 2 → 2 * quo.toNat + b < 2 ^ (128 - stepIdx) :=
      divmod128_q_next_bound stepIdx quo hidx_lt hq_bound
    have hs := divmod128Step_spec d quo rem (bitAt128 n stepIdx)
      (n.toNat / 2 ^ (stepIdx + 1)) (n.toNat / 2 ^ stepIdx) (2 ^ (128 - stepIdx))
      hq_wf hr_wf hr_lt hd hbit_lt h_q_half h_eq h_div_step h_q_next_bound
    rw [divmod128Loop_succ]
    exact ih _ _ (Nat.le_of_lt hidx_lt) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2

theorem divmod128_sound (n d : HiLo64) (hn : n.WellFormed) (hd : d.WellFormed) (hd_pos : 0 < d.toNat) :
    (udivti3 n d).WellFormed ∧
    (umodti3 n d).WellFormed ∧
    (udivti3 n d).toNat * d.toNat + (umodti3 n d).toNat = n.toNat ∧
    (umodti3 n d).toNat < d.toNat := by
  have h0_wf : (⟨0, 0⟩ : HiLo64).WellFormed := ⟨W64_pos, W64_pos⟩
  have h0_toNat : (⟨0, 0⟩ : HiLo64).toNat = 0 := rfl
  have h_n_div : n.toNat / 2 ^ 128 = 0 := by
    apply Nat.div_eq_of_lt
    rw [← W64_mul_W64_eq]
    exact HiLo64.toNat_lt_2pow128 hn
  have h_inv := divmod128Loop_inv n d hn hd hd_pos 128 ⟨0, 0⟩ ⟨0, 0⟩ (Nat.le_refl 128)
    h0_wf h0_wf (by rw [h0_toNat]; exact hd_pos)
    (by rw [h0_toNat, Nat.zero_mul, Nat.zero_add, h_n_div])
    (by rw [h0_toNat, Nat.sub_self, Nat.pow_zero]; exact Nat.succ_pos 0)
  exact h_inv

theorem divmod128_eq_div_mod (n d : HiLo64) (hn : n.WellFormed) (hd : d.WellFormed) (hd_pos : 0 < d.toNat) :
    (udivti3 n d).toNat = n.toNat / d.toNat ∧
    (umodti3 n d).toNat = n.toNat % d.toNat := by
  have hs := divmod128_sound n d hn hd hd_pos
  have h_eq := hs.2.2.1
  have h_lt := hs.2.2.2
  constructor
  · rw [← h_eq, Nat.add_comm, Nat.add_mul_div_right _ _ hd_pos, Nat.div_eq_of_lt h_lt, Nat.zero_add]
  · rw [← h_eq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_lt]

/-! ## Part 6: `#[no_builtins]` LoopIdiomRecognize Non-Self-Recursion Invariant -/

/-- Formal model of LLVM `LoopIdiomRecognize::runOnLoop` (`LoopIdiomRecognize.cpp:331-355`)
    + `TargetLibraryInfo` (`TargetLibraryInfo.h:298-299`). -/
inductive BuiltinSym where
  | memcpy | memset | setBytesHelper | copyForwardHelper | userFn
  deriving DecidableEq, Repr

structure FnLoweringCtx where
  fnName         : BuiltinSym
  hasNoBuiltins  : Bool
  hasByteLoop    : Bool
  callsHelper    : Option BuiltinSym
  deriving DecidableEq, Repr

def lirTransformsLoopToCall (ctx : FnLoweringCtx) : Option BuiltinSym :=
  if !ctx.hasByteLoop || ctx.hasNoBuiltins then
    none
  else if ctx.fnName == .memcpy || ctx.fnName == .memset then
    none -- `LoopIdiomRecognize.cpp:332` guards ONLY literal `memcpy`/`memset`
  else
    some .memset

theorem noBuiltins_prevents_idiom_self_recursion (ctx : FnLoweringCtx) :
    (ctx.hasNoBuiltins = true → lirTransformsLoopToCall ctx = none) ∧
    (lirTransformsLoopToCall { fnName := .setBytesHelper, hasNoBuiltins := false, hasByteLoop := true, callsHelper := none } = some .memset) ∧
    (lirTransformsLoopToCall { fnName := .setBytesHelper, hasNoBuiltins := true, hasByteLoop := true, callsHelper := none } = none) := by
  refine ⟨?_, rfl, rfl⟩
  intro hnb
  simp [lirTransformsLoopToCall, hnb]

end InlineAsmAndBuiltinsFraming

#print axioms InlineAsmAndBuiltinsFraming.registerAlloc_and_frame_soundness
#print axioms InlineAsmAndBuiltinsFraming.nostack_redzone_iff_for_push_pop
#print axioms InlineAsmAndBuiltinsFraming.virtual_to_physical_coalescing_soundness
#print axioms InlineAsmAndBuiltinsFraming.ce1_lateout_aliasing_bug_and_earlyout_fix
#print axioms InlineAsmAndBuiltinsFraming.ce2_nostack_redzone_clobber_and_default_fix
#print axioms InlineAsmAndBuiltinsFraming.divmod128_sound
#print axioms InlineAsmAndBuiltinsFraming.divmod128_eq_div_mod
#print axioms InlineAsmAndBuiltinsFraming.noBuiltins_prevents_idiom_self_recursion
