/-
  two_tier_isa_dialect_and_elf_refinement_probe.lean
  Standalone Lean 4.34.1 mechanization for Chunk 6:
  `opencompl/riscv-lean`, `opencompl/lean-mlir`, and `BasisResearch/ship-your-interpreter`.

  This probe mechanizes:
  1. The `opencompl/riscv-lean` (commit `7c6b500c1744f40d928fb131125cd06edf9f4fce`)
     two-stage, three-tier ISA purification architecture:
     - Tier 1: Monadic Sail-style executor (`SailM := EStateM SailError SeqState`)
       with `rX_bits`, `wX_bits`, `get_arch_pc`, and instruction executors across
       RV64I, Zba (`adduw`, `sh1add`, `sh2add`, `sh3add`), Zbb (`andn`, `orn`,
       `xnor`, `maxu`, `minu`, `sextb`, `sexth`, `zexth`, `cpop`), and Zicond
       (`czero.eqz`, `czero.nez`).
     - Stage 1 (`RISCV/Skeleton.lean`, `RISCV/SailPure.lean`, `RISCV/SailToRV64.lean`):
       Monadic skeleton wrappers (`skeleton_unary`, `skeleton_binary`,
       `skeleton_utype_lui`, `skeleton_utype_auipc`) around `SailRV64` pure functions,
       including formal counterexamples demonstrating why `Zicond` and unified `UTYPE`
       cannot be proved unconditionally equal to `skeleton_binary` / `skeleton_utype`,
       and invariant-based monadic `forIn'` loop purification for `cpop`.
     - Stage 2 (`RISCV/Instructions.lean`, `RISCV/SailPureToInstructions.lean`):
       Equivalence between `SailRV64` functions and the pure bit-blastable `RV64`
       `BitVec 64` dialect (noting the `(rs2_val, rs1_val)` parameter convention).
  2. The `opencompl/lean-mlir` (commit `b8c4a771319a044854a4bbb49b8821381ef86ff8`)
     hybrid dialect (`LLVMPlusRiscV`) refinement relation (`PoisonOr.IsRefinedBy`)
     and why directional poison refinement (`poison ⊑ value v`) is a preorder but not
     symmetric equality (explaining `PeepholeRefine.lean`'s `toPeepholeUNSOUND`).
  3. The `BasisResearch/ship-your-interpreter` (commit `fb07094cff916318c34b07494a7d739f1e53989b`)
     ELF `TextPiece` / `CodeAt` byte-range pinning + normal-form `decodeN` / `decodeW`
     decoding composed with Anneal's Layer 1A / Layer 1B refinement algebra
     (`Trusted/StepResult.lean` and `Trusted/Refinement.lean`, `pass_trans`) to verify
     a 4-instruction RV64I+Zba+Zbb ELF leaf function end-to-end from MIR to machine
     code using only standard Lean axioms (`propext`, `Quot.sound`, `Classical.choice`).
-/

namespace TwoTierIsaDialectAndElfRefinementProbe

/-! ============================================================================
    SECTION 1: ANNEAL LAYER 1A & LAYER 1B REFINEMENT ALGEBRA
    (`trusted/lean/Trusted/StepResult.lean` & `trusted/lean/Trusted/Refinement.lean`)
    ============================================================================ -/

inductive Partial (α : Type u) : Type u where
  | val (a : α)
  | div
  | ub

namespace Partial

def refines (t s : Partial α) : Prop :=
  match s with
  | .ub    => True
  | .val a => t = .val a
  | .div   => t = .div

infix:50 " ⊑ₚ " => Partial.refines

theorem refines_refl (x : Partial α) : x ⊑ₚ x := by
  cases x <;> first | trivial | rfl

theorem refines_trans {x y z : Partial α}
    (hxy : x ⊑ₚ y) (hyz : y ⊑ₚ z) : x ⊑ₚ z := by
  cases z with
  | ub => trivial
  | val a =>
    change y = .val a at hyz
    subst hyz
    exact hxy
  | div =>
    change y = .div at hyz
    subst hyz
    exact hxy

end Partial

structure Language where
  Program : Type
  Input   : Type
  Output  : Type
  exec    : Program → Input → Partial Output → Prop

def Compiles
    (L₁ L₂ : Language)
    (relateIn  : L₁.Input → L₂.Input → Prop)
    (relateOut : L₁.Output → L₂.Output → Prop)
    (p₁ : L₁.Program) (p₂ : L₂.Program) : Prop :=
  ∀ i₁ i₂, relateIn i₁ i₂ →
    ∀ b₂, L₂.exec p₂ i₂ b₂ →
      ∃ b₁, L₁.exec p₁ i₁ b₁ ∧
        match b₁ with
        | .ub     => True
        | .div    => b₂ = .div
        | .val o₁ => ∃ o₂, b₂ = .val o₂ ∧ relateOut o₁ o₂

def Abstracts
    (L₁ L₂ : Language)
    (p₁ : L₁.Program) (p₂ : L₂.Program)
    (liftIn : L₁.Input → L₂.Input)
    (embedOut : L₂.Output → L₁.Output) : Prop :=
  Compiles L₁ L₂
    (fun i₁ i₂ => i₂ = liftIn i₁)
    (fun o₁ o₂ => o₁ = embedOut o₂)
    p₁ p₂

theorem abstracts_id_iff (L₁ L₂ : Language)
    (hIn : L₁.Input = L₂.Input) (hOut : L₂.Output = L₁.Output)
    (p₁ : L₁.Program) (p₂ : L₂.Program) :
    Abstracts L₁ L₂ p₁ p₂ (hIn ▸ id) (hOut ▸ id) ↔
      (∀ i, ∀ b₂, L₂.exec p₂ (hIn ▸ i) b₂ →
        ∃ b₁, L₁.exec p₁ i b₁ ∧ (hOut ▸ b₂) ⊑ₚ b₁) := by
  rcases L₁ with ⟨_, _, _, _⟩
  rcases L₂ with ⟨_, _, _, _⟩
  dsimp at hIn hOut ⊢
  subst hIn; subst hOut
  simp only [Abstracts, Compiles, id_eq]
  constructor
  · intro h i b₂ hb₂
    obtain ⟨b₁, hb₁, href⟩ := h i i rfl b₂ hb₂
    refine ⟨b₁, hb₁, ?_⟩
    cases b₁ with
    | ub => trivial
    | div => exact href
    | val o₁ =>
      obtain ⟨o₂, rfl, rfl⟩ := href
      rfl
  · intro h i₁ i₂ hi b₂ hb₂
    subst hi
    obtain ⟨b₁, hb₁, href⟩ := h _ b₂ hb₂
    refine ⟨b₁, hb₁, ?_⟩
    cases b₁ with
    | ub => trivial
    | div => exact href
    | val o₁ => exact ⟨o₁, href, rfl⟩

structure Compiler (Source Target : Language) where
  compile   : Source.Program → Option Target.Program
  relateIn  : Source.Input → Target.Input → Prop
  relateOut : Source.Output → Target.Output → Prop

def Compiler.Verified (C : Compiler S T) : Prop :=
  ∀ s t, C.compile s = some t → Compiles S T C.relateIn C.relateOut s t

theorem pass_trans
    {L₁ L₂ L₃ : Language}
    {rIn₁₂ : L₁.Input → L₂.Input → Prop}
    {rIn₂₃ : L₂.Input → L₃.Input → Prop}
    {rOut₁₂ : L₁.Output → L₂.Output → Prop}
    {rOut₂₃ : L₂.Output → L₃.Output → Prop}
    {p₁ : L₁.Program} {p₂ : L₂.Program} {p₃ : L₃.Program}
    (h₁₂ : Compiles L₁ L₂ rIn₁₂ rOut₁₂ p₁ p₂)
    (h₂₃ : Compiles L₂ L₃ rIn₂₃ rOut₂₃ p₂ p₃)
    {i₁ : L₁.Input} {i₂ : L₂.Input} {i₃ : L₃.Input}
    (hi₁₂ : rIn₁₂ i₁ i₂) (hi₂₃ : rIn₂₃ i₂ i₃) :
    ∀ b₃, L₃.exec p₃ i₃ b₃ →
      ∃ b₁, L₁.exec p₁ i₁ b₁ ∧
        match b₁ with
        | .ub     => True
        | .div    => b₃ = .div
        | .val o₁ => ∃ o₂ o₃, b₃ = .val o₃ ∧ rOut₁₂ o₁ o₂ ∧ rOut₂₃ o₂ o₃ := by
  intro b₃ hb₃
  obtain ⟨b₂, hb₂, href₂₃⟩ := h₂₃ i₂ i₃ hi₂₃ b₃ hb₃
  obtain ⟨b₁, hb₁, href₁₂⟩ := h₁₂ i₁ i₂ hi₁₂ b₂ hb₂
  refine ⟨b₁, hb₁, ?_⟩
  cases b₁ with
  | ub => trivial
  | div =>
    subst href₁₂
    exact href₂₃
  | val o₁ =>
    obtain ⟨o₂, rfl, ho₁₂⟩ := href₁₂
    obtain ⟨o₃, hb₃_eq, ho₂₃⟩ := href₂₃
    exact ⟨o₂, o₃, hb₃_eq, ho₁₂, ho₂₃⟩

inductive StepResult (State Value : Type) where
  | cont (next : State)
  | term (val  : Value)
  | trap

structure SmallStepMachine where
  Program : Type
  Input   : Type
  State   : Type
  Output  : Type
  init    : Program → Input → State
  step    : Program → State → StepResult State Output

namespace SmallStepMachine

def ReachesIn (M : SmallStepMachine) (p : M.Program) :
    Nat → M.State → StepResult M.State M.Output → Prop
  | 0, s, r     => M.step p s = r
  | n + 1, s, r =>
    ∃ s', M.step p s = .cont s' ∧ M.ReachesIn p n s' r

def ReachesPrefix (M : SmallStepMachine) (p : M.Program) (n : Nat) (s : M.State)
    (r : StepResult M.State M.Output) : Prop :=
  M.ReachesIn p n s r ∧
  (∀ k, k < n → ∃ s', M.ReachesIn p k s (.cont s'))

theorem ReachesIn_deterministic (M : SmallStepMachine) (p : M.Program) :
    ∀ n s r₁ r₂, M.ReachesIn p n s r₁ → M.ReachesIn p n s r₂ → r₁ = r₂
  | 0, _, _, _, h₁, h₂ => h₁.symm.trans h₂
  | n + 1, _, _, _, ⟨s₁, hs₁, hr₁⟩, ⟨s₂, hs₂, hr₂⟩ => by
    have hEq : StepResult.cont s₁ = StepResult.cont s₂ := hs₁.symm.trans hs₂
    injection hEq with hEq'
    subst hEq'
    exact M.ReachesIn_deterministic p n s₁ _ _ hr₁ hr₂

def DivergesFrom (M : SmallStepMachine) (p : M.Program) (s : M.State) : Prop :=
  ∀ n, ∃ s', M.ReachesIn p n s (.cont s')

inductive BehaviorOf (M : SmallStepMachine) (p : M.Program) (i : M.Input)
    : Partial M.Output → Prop where
  | terminates (n : Nat) (v : M.Output) :
      M.ReachesPrefix p n (M.init p i) (.term v) →
      M.BehaviorOf p i (.val v)
  | diverges :
      M.DivergesFrom p (M.init p i) →
      M.BehaviorOf p i .div
  | traps (n : Nat) :
      M.ReachesPrefix p n (M.init p i) .trap →
      M.BehaviorOf p i .ub

def toLanguage (M : SmallStepMachine) : Language where
  Program := M.Program
  Input   := M.Input
  Output  := M.Output
  exec    := M.BehaviorOf

end SmallStepMachine


/-! ============================================================================
    SECTION 2: `opencompl/riscv-lean` TWO-STAGE PURIFICATION ARCHITECTURE
    (`RISCV/Skeleton.lean`, `RISCV/SailPure.lean`, `RISCV/SailToRV64.lean`,
     `RISCV/Instructions.lean`, `RISCV/SailPureToInstructions.lean`)
    ============================================================================ -/

inductive SailError where
  | Unreachable
  | AssertionFailure (msg : String)
  deriving DecidableEq, Repr

inductive ExecutionResult where
  | RETIRE_SUCCESS
  | Memory_Exception
  | Illegal_Instruction
  deriving DecidableEq, Repr

abbrev RegIdx := Fin 32

/-- Sequential architectural state modeling `LeanRV64D.Sail.SequentialState`.
    Using `Option (BitVec 64)` for registers (`xregs` and `pc`) faithfully models
    `s.regs.get? r` in `lean-sail`, where reading an uninitialized register throws
    `SailError.Unreachable` (`RISCV/SailToRV64.lean:27-37, 428-437`). -/
structure SeqState where
  xregs  : Fin 32 → Option (BitVec 64)
  pc     : Option (BitVec 64)
  nextPC : BitVec 64
  mem    : Nat → BitVec 8
  halted : Bool

abbrev SailM := EStateM SailError SeqState

/-- Total register lookup with default `0#64` (`RISCV/Skeleton.lean:8-15`). -/
def rX_pure (s : SeqState) (r : RegIdx) : BitVec 64 :=
  if r.val = 0 then 0#64 else (s.xregs r).getD 0#64

/-- Monadic register read (`rX_bits` in `LeanRV64D`). Reading `x0` always returns
    `0#64` without touching `s.xregs`; reading `x1..x31` looks up `s.xregs r`
    and throws `.Unreachable` if uninitialized. -/
def rX_bits (r : RegIdx) : SailM (BitVec 64) := fun s =>
  if r.val = 0 then
    .ok 0#64 s
  else
    match s.xregs r with
    | some v => .ok v s
    | none   => .error .Unreachable s

/-- Monadic register write (`wX_bits` in `LeanRV64D`). Writing `x0` is a no-op;
    writing `x1..x31` updates `s.xregs`. -/
def wX_bits (r : RegIdx) (v : BitVec 64) : SailM Unit := fun s =>
  if r.val = 0 then
    .ok () s
  else
    .ok () { s with xregs := fun k => if k = r then some v else s.xregs k }

/-- Monadic `PC` read (`get_arch_pc` in `LeanRV64D`). -/
def get_arch_pc : SailM (BitVec 64) := fun s =>
  match s.pc with
  | some v => .ok v s
  | none   => .error .Unreachable s

/-- Monadic assertion (`Sail.assert` in `rems-project/lean-sail`). -/
def sailAssert (cond : Bool) (msg : String := "") : SailM Unit := fun s =>
  if cond then .ok () s else .error (.AssertionFailure msg) s

/-! ### Stage 1 Skeletons (`RISCV/Skeleton.lean:17-58`) -/

def skeleton_unary (rs1 rd : RegIdx) (f : BitVec 64 → BitVec 64) : SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  wX_bits rd (f rs1_val)
  pure .RETIRE_SUCCESS

def skeleton_binary (rs2 rs1 rd : RegIdx) (f : BitVec 64 → BitVec 64 → BitVec 64) :
    SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  wX_bits rd (f rs1_val rs2_val)
  pure .RETIRE_SUCCESS

/-- Unified `UTYPE` skeleton from `RISCV/Skeleton.lean:28-32`, which reads `get_arch_pc`
    unconditionally (even for `LUI`). -/
def skeleton_utype (imm : BitVec 20) (rd : RegIdx) (op : Bool)
    (f : BitVec 20 → BitVec 64 → Bool → BitVec 64) : SailM ExecutionResult := do
  let off : BitVec 64 := BitVec.signExtend 64 (imm ++ (0#12 : BitVec 12))
  let pc_val ← get_arch_pc
  let ret := f imm pc_val op
  let _ := off
  wX_bits rd ret
  pure .RETIRE_SUCCESS

/-- Split `LUI` and `AUIPC` skeletons (`RISCV/Skeleton.lean:34-43`). -/
def skeleton_utype_lui (imm : BitVec 20) (rd : RegIdx)
    (f : BitVec 20 → BitVec 64) : SailM ExecutionResult := do
  wX_bits rd (f imm)
  pure .RETIRE_SUCCESS

def skeleton_utype_auipc (imm : BitVec 20) (rd : RegIdx)
    (f : BitVec 20 → BitVec 64 → BitVec 64) : SailM ExecutionResult := do
  let pc_val ← get_arch_pc
  wX_bits rd (f imm pc_val)
  pure .RETIRE_SUCCESS

/-! ### Authoritative Monadic Instruction Executors (Tier 1) -/

inductive IOp where | ADDI | ANDI | ORI | XORI deriving DecidableEq, Repr
inductive ROp where | ADD | SUB | AND | OR | XOR deriving DecidableEq, Repr
inductive ShiftIOp where | SLLI | SRLI | SRAI deriving DecidableEq, Repr
inductive ZbaROpUW where | ADDUW | SH1ADDUW | SH2ADDUW | SH3ADDUW deriving DecidableEq, Repr
inductive ZbaROp where | SH1ADD | SH2ADD | SH3ADD deriving DecidableEq, Repr
inductive ZbbROp where | ANDN | ORN | XNOR | MAXU | MINU deriving DecidableEq, Repr
inductive ZbbExtOp where | SEXTB | SEXTH | ZEXTH deriving DecidableEq, Repr
inductive ZicondOp where | CZERO_EQZ | CZERO_NEZ deriving DecidableEq, Repr

def execute_ITYPE (imm : BitVec 12) (rs1 rd : RegIdx) (op : IOp) : SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let immext : BitVec 64 := BitVec.signExtend 64 imm
  let result : BitVec 64 :=
    match op with
    | .ADDI => rs1_val + immext
    | .ANDI => rs1_val &&& immext
    | .ORI  => rs1_val ||| immext
    | .XORI => rs1_val ^^^ immext
  wX_bits rd result
  pure .RETIRE_SUCCESS

def execute_RTYPE (rs2 rs1 rd : RegIdx) (op : ROp) : SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result : BitVec 64 :=
    match op with
    | .ADD => rs1_val + rs2_val
    | .SUB => rs1_val - rs2_val
    | .AND => rs1_val &&& rs2_val
    | .OR  => rs1_val ||| rs2_val
    | .XOR => rs1_val ^^^ rs2_val
  wX_bits rd result
  pure .RETIRE_SUCCESS

def execute_UTYPE (imm : BitVec 20) (rd : RegIdx) (isAuipc : Bool) : SailM ExecutionResult := do
  let off : BitVec 64 := BitVec.signExtend 64 (imm ++ (0#12 : BitVec 12))
  let ret ←
    if isAuipc then do
      let pc_val ← get_arch_pc
      pure (pc_val + off)
    else
      pure off
  wX_bits rd ret
  pure .RETIRE_SUCCESS

def execute_ZBA_RTYPEUW (rs2 rs1 rd : RegIdx) (op : ZbaROpUW) : SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let shamt : Nat :=
    match op with
    | .ADDUW    => 0
    | .SH1ADDUW => 1
    | .SH2ADDUW => 2
    | .SH3ADDUW => 3
  let result : BitVec 64 := (BitVec.zeroExtend 64 (rs1_val.extractLsb' 0 32) <<< shamt) + rs2_val
  wX_bits rd result
  pure .RETIRE_SUCCESS

def execute_ZBA_RTYPE (rs2 rs1 rd : RegIdx) (op : ZbaROp) : SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let shamt : Nat :=
    match op with
    | .SH1ADD => 1
    | .SH2ADD => 2
    | .SH3ADD => 3
  let result : BitVec 64 := (rs1_val <<< shamt) + rs2_val
  wX_bits rd result
  pure .RETIRE_SUCCESS

def execute_ZBB_RTYPE (rs2 rs1 rd : RegIdx) (op : ZbbROp) : SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result : BitVec 64 :=
    match op with
    | .ANDN => rs1_val &&& ~~~rs2_val
    | .ORN  => rs1_val ||| ~~~rs2_val
    | .XNOR => ~~~(rs1_val ^^^ rs2_val)
    | .MAXU => if rs1_val.toNat < rs2_val.toNat then rs2_val else rs1_val
    | .MINU => if rs1_val.toNat < rs2_val.toNat then rs1_val else rs2_val
  wX_bits rd result
  pure .RETIRE_SUCCESS

def execute_ZBB_EXTOP (rs1 rd : RegIdx) (op : ZbbExtOp) : SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let result : BitVec 64 :=
    match op with
    | .SEXTB => BitVec.signExtend 64 (rs1_val.extractLsb' 0 8)
    | .SEXTH => BitVec.signExtend 64 (rs1_val.extractLsb' 0 16)
    | .ZEXTH => BitVec.zeroExtend 64 (rs1_val.extractLsb' 0 16)
  wX_bits rd result
  pure .RETIRE_SUCCESS

/-- Sail's `execute_ZICOND_RTYPE` (`RISCV/SailToRV64.lean:428-437`):
    Note that Sail reads `rs2` FIRST and only executes `rX_bits rs1` in the branch
    where `rs2_val` does not zero the output! -/
def execute_ZICOND_RTYPE (rs2 rs1 rd : RegIdx) (op : ZicondOp) : SailM ExecutionResult := do
  let rs2_val ← rX_bits rs2
  let zero_cond : Bool :=
    match op with
    | .CZERO_EQZ => rs2_val == 0#64
    | .CZERO_NEZ => rs2_val != 0#64
  let result ←
    if zero_cond then
      pure 0#64
    else
      rX_bits rs1
  wX_bits rd result
  pure .RETIRE_SUCCESS

/-! ### Intermediate Purified Representation `SailRV64` (`RISCV/SailPure.lean`)
    Note the `(rs2_val, rs1_val)` argument order in binary functions (`SailPure.lean:25-196`). -/

namespace SailRV64

def itype (imm : BitVec 12) (rs1_val : BitVec 64) (op : IOp) : BitVec 64 :=
  let immext : BitVec 64 := BitVec.signExtend 64 imm
  match op with
  | .ADDI => rs1_val + immext
  | .ANDI => rs1_val &&& immext
  | .ORI  => rs1_val ||| immext
  | .XORI => rs1_val ^^^ immext

def rtype (op : ROp) (rs2_val rs1_val : BitVec 64) : BitVec 64 :=
  match op with
  | .ADD => rs1_val + rs2_val
  | .SUB => rs1_val - rs2_val
  | .AND => rs1_val &&& rs2_val
  | .OR  => rs1_val ||| rs2_val
  | .XOR => rs1_val ^^^ rs2_val

def utype (imm : BitVec 20) (pc : BitVec 64) (isAuipc : Bool) : BitVec 64 :=
  let off : BitVec 64 := BitVec.signExtend 64 (imm ++ (0#12 : BitVec 12))
  if isAuipc then pc + off else off

def utype_lui (imm : BitVec 20) : BitVec 64 :=
  BitVec.signExtend 64 (imm ++ (0#12 : BitVec 12))

def utype_auipc (imm : BitVec 20) (pc : BitVec 64) : BitVec 64 :=
  pc + BitVec.signExtend 64 (imm ++ (0#12 : BitVec 12))

def zba_rtypeuw (op : ZbaROpUW) (rs2_val rs1_val : BitVec 64) : BitVec 64 :=
  let shamt : Nat :=
    match op with
    | .ADDUW    => 0
    | .SH1ADDUW => 1
    | .SH2ADDUW => 2
    | .SH3ADDUW => 3
  (BitVec.zeroExtend 64 (rs1_val.extractLsb' 0 32) <<< shamt) + rs2_val

def zba_rtype (op : ZbaROp) (rs2_val rs1_val : BitVec 64) : BitVec 64 :=
  let shamt : Nat :=
    match op with
    | .SH1ADD => 1
    | .SH2ADD => 2
    | .SH3ADD => 3
  (rs1_val <<< shamt) + rs2_val

def zbb_rtype (op : ZbbROp) (rs2_val rs1_val : BitVec 64) : BitVec 64 :=
  match op with
  | .ANDN => rs1_val &&& ~~~rs2_val
  | .ORN  => rs1_val ||| ~~~rs2_val
  | .XNOR => ~~~(rs1_val ^^^ rs2_val)
  | .MAXU => if rs1_val.toNat < rs2_val.toNat then rs2_val else rs1_val
  | .MINU => if rs1_val.toNat < rs2_val.toNat then rs1_val else rs2_val

def zbb_extop (op : ZbbExtOp) (rs1_val : BitVec 64) : BitVec 64 :=
  match op with
  | .SEXTB => BitVec.signExtend 64 (rs1_val.extractLsb' 0 8)
  | .SEXTH => BitVec.signExtend 64 (rs1_val.extractLsb' 0 16)
  | .ZEXTH => BitVec.zeroExtend 64 (rs1_val.extractLsb' 0 16)

def zicond_rtype (op : ZicondOp) (rs2_val rs1_val : BitVec 64) : BitVec 64 :=
  let zero_cond : Bool :=
    match op with
    | .CZERO_EQZ => rs2_val == 0#64
    | .CZERO_NEZ => rs2_val != 0#64
  if zero_cond then 0#64 else rs1_val

end SailRV64

/-! ### Stage 1 Equivalence Theorems & Counterexamples (`RISCV/SailToRV64.lean`) -/

theorem itype_eq (imm : BitVec 12) (rs1 rd : RegIdx) (op : IOp) :
    execute_ITYPE imm rs1 rd op =
      skeleton_unary rs1 rd (fun val => SailRV64.itype imm val op) := by
  cases op <;> rfl

theorem rtype_eq (rs2 rs1 rd : RegIdx) (op : ROp) :
    execute_RTYPE rs2 rs1 rd op =
      skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.rtype op val2 val1) := by
  cases op <;> rfl

theorem zba_rtypeuw_eq (rs2 rs1 rd : RegIdx) (op : ZbaROpUW) :
    execute_ZBA_RTYPEUW rs2 rs1 rd op =
      skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zba_rtypeuw op val2 val1) := by
  cases op <;> rfl

theorem zba_rtype_eq (rs2 rs1 rd : RegIdx) (op : ZbaROp) :
    execute_ZBA_RTYPE rs2 rs1 rd op =
      skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zba_rtype op val2 val1) := by
  cases op <;> rfl

theorem zbb_rtype_eq (rs2 rs1 rd : RegIdx) (op : ZbbROp) :
    execute_ZBB_RTYPE rs2 rs1 rd op =
      skeleton_binary rs2 rs1 rd (fun val1 val2 => SailRV64.zbb_rtype op val2 val1) := by
  cases op <;> rfl

theorem zbb_extop_eq (rs1 rd : RegIdx) (op : ZbbExtOp) :
    execute_ZBB_EXTOP rs1 rd op =
      skeleton_unary rs1 rd (fun val => SailRV64.zbb_extop op val) := by
  cases op <;> rfl

/-- Finding 1(c): `LUI` does not read `PC`, whereas `skeleton_utype` does.
    When `s.pc = none`, `execute_UTYPE imm rd false` succeeds while `skeleton_utype`
    throws `.Unreachable`. Splitting into `skeleton_utype_lui` and `skeleton_utype_auipc`
    restores unconditional equality (`RISCV/SailToRV64.lean:27-57`). -/
theorem utype_lui_not_unconditional_skeleton_utype :
    ∃ (imm : BitVec 20) (rd : RegIdx) (s : SeqState),
      (execute_UTYPE imm rd false).run s ≠
        (skeleton_utype imm rd false SailRV64.utype).run s := by
  refine ⟨0#20, ⟨1, by decide⟩, ⟨fun _ => some 0#64, none, 0#64, fun _ => 0#8, false⟩, ?_⟩
  intro h
  injection h

theorem utype_eq (imm : BitVec 20) (rd : RegIdx) (isAuipc : Bool)
    (s : SeqState) (pc_val : BitVec 64) (h_pc : s.pc = some pc_val) :
    (execute_UTYPE imm rd isAuipc).run s =
      (skeleton_utype imm rd isAuipc SailRV64.utype).run s := by
  cases isAuipc <;>
    simp [execute_UTYPE, skeleton_utype, get_arch_pc, SailRV64.utype,
      bind, EStateM.bind, pure, EStateM.pure, EStateM.run, h_pc]

theorem utype_lui_eq (imm : BitVec 20) (rd : RegIdx) :
    execute_UTYPE imm rd false = skeleton_utype_lui imm rd SailRV64.utype_lui := rfl

theorem utype_auipc_eq (imm : BitVec 20) (rd : RegIdx) :
    execute_UTYPE imm rd true = skeleton_utype_auipc imm rd SailRV64.utype_auipc := rfl

/-- Finding 1(b): Formal counterexample showing why `zicond_rtype_eq` in
    `RISCV/SailToRV64.lean:428-437` CANNOT be stated as unconditional function
    equality on `SailM`. When `rs2` holds `0#64` and `rs1` (`x1`) is uninitialized
    (`s.xregs 1 = none`), `execute_ZICOND_RTYPE` short-circuits `rX_bits rs1` and
    succeeds with `0#64`, whereas `skeleton_binary` reads `rs1` first and fails
    with `.error .Unreachable`. -/
theorem zicond_not_unconditional_skeleton_binary :
    ∃ (rs2 rs1 rd : RegIdx) (s : SeqState),
      (execute_ZICOND_RTYPE rs2 rs1 rd .CZERO_EQZ).run s ≠
        (skeleton_binary rs2 rs1 rd
          (fun val1 val2 => SailRV64.zicond_rtype .CZERO_EQZ val2 val1)).run s := by
  let rs2 : RegIdx := ⟨2, by decide⟩
  let rs1 : RegIdx := ⟨1, by decide⟩
  let rd  : RegIdx := ⟨3, by decide⟩
  let s : SeqState := {
    xregs  := fun r => if r = rs2 then some 0#64 else none
    pc     := some 0#64
    nextPC := 4#64
    mem    := fun _ => 0#8
    halted := false
  }
  refine ⟨rs2, rs1, rd, s, ?_⟩
  intro h
  injection h

theorem rX_bits_run (rs : RegIdx) (s : SeqState) :
    (rX_bits rs).run s = .ok (rX_pure s rs) s ∨ ∃ e, (rX_bits rs).run s = .error e s := by
  dsimp only [rX_bits, rX_pure, EStateM.run]
  split
  · exact .inl rfl
  · cases s.xregs rs
    · exact .inr ⟨.Unreachable, rfl⟩
    · exact .inl rfl

/-- With `riscv-lean`'s register-initialized precondition `(h : (rX_bits rs1).run s = .ok (rX_pure s rs1) s)`,
    `execute_ZICOND_RTYPE` agrees with `skeleton_binary` (`RISCV/SailToRV64.lean:428-437`). -/
theorem zicond_rtype_eq (rs2 rs1 rd : RegIdx) (op : ZicondOp) (s : SeqState)
    (h : (rX_bits rs1).run s = .ok (rX_pure s rs1) s) :
    (execute_ZICOND_RTYPE rs2 rs1 rd op).run s =
      (skeleton_binary rs2 rs1 rd
        (fun val1 val2 => SailRV64.zicond_rtype op val2 val1)).run s := by
  simp only [EStateM.run] at h ⊢
  unfold execute_ZICOND_RTYPE SailRV64.zicond_rtype skeleton_binary
  rcases rX_bits_run rs2 s with h2 | ⟨e, h2⟩ <;> simp only [EStateM.run] at h2 <;>
    cases op <;> simp [bind, EStateM.bind, pure, EStateM.pure, h, h2]
  · by_cases hc : rX_pure s rs2 = 0#64 <;> simp [hc, h, EStateM.pure, EStateM.bind]
  · by_cases hc : rX_pure s rs2 = 0#64 <;> simp [hc, h, EStateM.pure, EStateM.bind]

/-- Finding 1(a): Invariant-based monadic loop purification for `cpop`
    (`RISCV/SailToRV64.lean:274-314`). Sail's `execute_CPOP` increments `counts` inside
    a 64-iteration loop and runs `sailAssert (counts + 1 ≤ 64)` whenever bit `i` is set.
    By carrying the invariant `counts ≤ i`, the monadic loop collapses to the pure
    popcount loop without `bv_decide`. -/
def cpopLoopSail (v : BitVec 64) : Nat → Nat → SailM Nat
  | 0, counts => pure counts
  | k + 1, counts => do
    let i := 64 - (k + 1)
    let counts' ←
      if v.getLsbD i then do
        sailAssert (decide (counts + 1 ≤ 64)) "cpop overflow"
        pure (counts + 1)
      else
        pure counts
    cpopLoopSail v k counts'

def cpopLoopPure (v : BitVec 64) : Nat → Nat → Nat
  | 0, counts => counts
  | k + 1, counts =>
    let i := 64 - (k + 1)
    let counts' := if v.getLsbD i then counts + 1 else counts
    cpopLoopPure v k counts'

theorem cpopLoopSail_eq_pure (v : BitVec 64) :
    ∀ (k counts : Nat) (s : SeqState),
      counts + k ≤ 64 →
      (cpopLoopSail v k counts).run s = .ok (cpopLoopPure v k counts) s
  | 0, counts, s, _ => rfl
  | k + 1, counts, s, hbound => by
    unfold cpopLoopSail cpopLoopPure
    by_cases hb : v.getLsbD (64 - (k + 1))
    · have hle : decide (counts + 1 ≤ 64) = true := decide_eq_true (by omega)
      simp only [hb, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure,
        EStateM.run, sailAssert, hle]
      exact cpopLoopSail_eq_pure v k (counts + 1) s (by omega)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind,
        pure, EStateM.pure, EStateM.run]
      exact cpopLoopSail_eq_pure v k counts s (by omega)


/-! ### Stage 2: Pure `RV64` `BitVec 64` Dialect (`RISCV/Instructions.lean` & `RISCV/SailPureToInstructions.lean`) -/

namespace RV64

def addi (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  rs1_val + BitVec.signExtend 64 imm

def andi (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  rs1_val &&& BitVec.signExtend 64 imm

def ori (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  rs1_val ||| BitVec.signExtend 64 imm

def xori (imm : BitVec 12) (rs1_val : BitVec 64) : BitVec 64 :=
  rs1_val ^^^ BitVec.signExtend 64 imm

/-- Note `riscv-lean`'s parameter convention (`RISCV/Instructions.lean:94-129`):
    `(rs2_val : BitVec 64) (rs1_val : BitVec 64)`. -/
def add (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val + rs2_val
def sub (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val - rs2_val
def and (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val &&& rs2_val
def or  (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val ||| rs2_val
def xor (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val ^^^ rs2_val

def lui (imm : BitVec 20) : BitVec 64 :=
  BitVec.signExtend 64 (imm ++ (0#12 : BitVec 12))

def auipc (imm : BitVec 20) (pc : BitVec 64) : BitVec 64 :=
  pc + BitVec.signExtend 64 (imm ++ (0#12 : BitVec 12))

def adduw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  (BitVec.zeroExtend 64 (rs1_val.extractLsb' 0 32) <<< 0) + rs2_val

def sh1adduw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  (BitVec.zeroExtend 64 (rs1_val.extractLsb' 0 32) <<< 1) + rs2_val

def sh2adduw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  (BitVec.zeroExtend 64 (rs1_val.extractLsb' 0 32) <<< 2) + rs2_val

def sh3adduw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  (BitVec.zeroExtend 64 (rs1_val.extractLsb' 0 32) <<< 3) + rs2_val

def sh1add (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  (rs1_val <<< 1) + rs2_val

def sh2add (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  (rs1_val <<< 2) + rs2_val

def sh3add (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  (rs1_val <<< 3) + rs2_val

def andn (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  rs1_val &&& ~~~rs2_val

def orn (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  rs1_val ||| ~~~rs2_val

def xnor (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  ~~~(rs1_val ^^^ rs2_val)

def maxu (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  if rs1_val < rs2_val then rs2_val else rs1_val

def minu (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  if rs1_val < rs2_val then rs1_val else rs2_val

def sextb (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (rs1_val.extractLsb' 0 8)

def sexth (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64 (rs1_val.extractLsb' 0 16)

def zexth (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.zeroExtend 64 (rs1_val.extractLsb' 0 16)

def czeroeqz (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  if rs2_val == 0#64 then 0#64 else rs1_val

def czeronez (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  if rs2_val != 0#64 then 0#64 else rs1_val

end RV64

theorem sailPure_sh2add_eq (rs2_val rs1_val : BitVec 64) :
    SailRV64.zba_rtype .SH2ADD rs2_val rs1_val = RV64.sh2add rs2_val rs1_val := rfl

theorem sailPure_andn_eq (rs2_val rs1_val : BitVec 64) :
    SailRV64.zbb_rtype .ANDN rs2_val rs1_val = RV64.andn rs2_val rs1_val := rfl

theorem sailPure_maxu_eq (rs2_val rs1_val : BitVec 64) :
    SailRV64.zbb_rtype .MAXU rs2_val rs1_val = RV64.maxu rs2_val rs1_val := rfl

theorem sailPure_czeroeqz_eq (rs2_val rs1_val : BitVec 64) :
    SailRV64.zicond_rtype .CZERO_EQZ rs2_val rs1_val = RV64.czeroeqz rs2_val rs1_val := rfl


/-! ============================================================================
    SECTION 3: `opencompl/lean-mlir` HYBRID DIALECT & POISON REFINEMENT AUDIT
    (`SSA/Projects/LLVMRiscV/LLVMAndRiscv.lean` & `PeepholeRefine.lean`)
    ============================================================================ -/

/-- `LeanMLIR.PoisonOr` models LLVM's `poison` semantics (`PoisonOr (BitVec w)`). -/
inductive PoisonOr (α : Type) where
  | poison
  | value (a : α)
  deriving DecidableEq, Repr

namespace PoisonOr

/-- `src ⊑ tgt` (`PoisonOr.IsRefinedBy` in `lean-mlir`):
    if `src` is `.poison`, any target value refines it; if `src` is `.value a`,
    `tgt` must be `.value a`. -/
def IsRefinedBy (src tgt : PoisonOr α) : Prop :=
  match src with
  | .poison  => True
  | .value a => tgt = .value a

infix:50 " ⊑_llvm " => PoisonOr.IsRefinedBy

theorem IsRefinedBy.refl (x : PoisonOr α) : x ⊑_llvm x := by
  cases x <;> first | trivial | rfl

theorem IsRefinedBy.trans {x y z : PoisonOr α}
    (hxy : x ⊑_llvm y) (hyz : y ⊑_llvm z) : x ⊑_llvm z := by
  cases x with
  | poison => trivial
  | value a =>
    change y = .value a at hxy
    subst hxy
    exact hyz

/-- Finding 2: `PoisonOr.IsRefinedBy` is directional (not symmetric).
    `.poison ⊑_llvm .value 0#64` holds, but `.value 0#64 ⊑_llvm .poison` is false.
    Because `lean-mlir`'s generic `multiRewritePeephole` pass infrastructure requires
    symmetric denotation equality (`lhs.denote = rhs.denote`), `SSA/Projects/LLVMRiscV/PeepholeRefine.lean:34-46`
    postulated `axiom refinement_correctness {p : Prop} : p` inside `toPeepholeUNSOUND`.
    In Anneal, Layer 1A's `Compiles` / `Partial.refines` is natively directional. -/
theorem poison_refines_value_not_symm :
    (PoisonOr.poison ⊑_llvm PoisonOr.value (0#64)) ∧
    ¬ (PoisonOr.value (0#64) ⊑_llvm PoisonOr.poison) := by
   refine ⟨trivial, fun h => by injection h⟩

end PoisonOr

/-- `SSA/Projects/LLVMRiscV/LLVMAndRiscv.lean:24-34`: Hybrid dialect casts. -/
def castLLVMToriscv {w : Nat} : PoisonOr (BitVec w) → BitVec 64
  | .value v => BitVec.signExtend 64 v
  | .poison  => 0#64

def castriscvToLLVM (w : Nat) (v : BitVec 64) : PoisonOr (BitVec w) :=
  .value (BitVec.signExtend w v)

def llvmAdd64 (x y : PoisonOr (BitVec 64)) : PoisonOr (BitVec 64) :=
  match x, y with
  | .value a, .value b => .value (a + b)
  | _, _               => .poison

def llvmShl64NoOverflow (x : PoisonOr (BitVec 64)) (shamt : BitVec 64) : PoisonOr (BitVec 64) :=
  match x with
  | .value a => if shamt.toNat < 64 then .value (a <<< shamt.toNat) else .poison
  | .poison  => .poison

def llvmAnd64 (x y : PoisonOr (BitVec 64)) : PoisonOr (BitVec 64) :=
  match x, y with
  | .value a, .value b => .value (a &&& b)
  | _, _               => .poison

def llvmXor64 (x y : PoisonOr (BitVec 64)) : PoisonOr (BitVec 64) :=
  match x, y with
  | .value a, .value b => .value (a ^^^ b)
  | _, _               => .poison

/-- Sound instruction-selection refinement for `Zba` `sh2add`:
    lowering `llvm.add (llvm.shl x, 2), y` to `RV64.sh2add y x` wrapped in
    `castLLVMToriscv` / `castriscvToLLVM 64` is a valid `IsRefinedBy` refinement
    proved algebraically with ZERO `bv_decide` (`Lean.ofReduceBool`) and ZERO custom axioms. -/
theorem llvm_zba_sh2add_peephole_refine (x y : PoisonOr (BitVec 64)) :
    llvmAdd64 (llvmShl64NoOverflow x 2#64) y ⊑_llvm
      castriscvToLLVM 64 (RV64.sh2add (castLLVMToriscv y) (castLLVMToriscv x)) := by
  cases x with
  | poison => trivial
  | value a =>
    cases y with
    | poison => trivial
    | value b =>
      simp [llvmAdd64, llvmShl64NoOverflow, castLLVMToriscv, castriscvToLLVM,
        RV64.sh2add, PoisonOr.IsRefinedBy]

def llvmNot64 (x : PoisonOr (BitVec 64)) : PoisonOr (BitVec 64) :=
  match x with
  | .value a => .value (~~~a)
  | .poison  => .poison

/-- Sound instruction-selection refinement for `Zbb` `andn`:
    lowering `llvm.and x, (llvm.not y)` to `RV64.andn y x` is a valid `IsRefinedBy`
    refinement proved without `bv_decide`. -/
theorem llvm_zbb_andn_peephole_refine (x y : PoisonOr (BitVec 64)) :
    llvmAnd64 x (llvmNot64 y) ⊑_llvm
      castriscvToLLVM 64 (RV64.andn (castLLVMToriscv y) (castLLVMToriscv x)) := by
  cases x with
  | poison => trivial
  | value a =>
    cases y with
    | poison => trivial
    | value b =>
      simp [llvmAnd64, llvmNot64, castLLVMToriscv, castriscvToLLVM,
        RV64.andn, PoisonOr.IsRefinedBy]


/-! ============================================================================
    SECTION 4: `BasisResearch/ship-your-interpreter` ELF `TextPiece` & `decodeN`
    COMPOSED WITH ANNEAL LAYER 1A / 1B END-TO-END REFINEMENT
    (`Vsa/Sim/TextImage.lean`, `Vsa/Sim/DecodeNF.lean`, `VsaIris/Vsa/SymExec.lean`)
    ============================================================================ -/

/-- `Vsa/MemRepr.lean` & `Vsa/Sim/TextImage.lean`:
    `TextLoaded T m` states that every `(addr, byte)` pair in `T` is present in `m`. -/
def TextLoaded (T : List (Nat × BitVec 8)) (m : Nat → BitVec 8) : Prop :=
  ∀ p ∈ T, m p.1 = p.2

/-- Contiguous byte ranges `[lo, hi)` backed by an image function `img : Nat → BitVec 8`
    (`Vsa/Sim/TextImage.lean:15-27`). -/
structure TextPiece where
  img    : Nat → BitVec 8
  ranges : List (Nat × Nat)

def inRangesB (rs : List (Nat × Nat)) (a : Nat) : Bool :=
  rs.any fun r => decide (r.1 ≤ a ∧ a < r.2)

def pieceText (p : TextPiece) : List (Nat × BitVec 8) :=
  p.ranges.flatMap fun r =>
    (List.range (r.2 - r.1)).map fun k => (r.1 + k, p.img (r.1 + k))

def piecesText (ps : List TextPiece) : List (Nat × BitVec 8) :=
  ps.flatMap pieceText

def piecesHasB (ps : List TextPiece) (a : Nat) (b : BitVec 8) : Bool :=
  ps.any fun p => inRangesB p.ranges a && (p.img a == b)

theorem mem_pieceText_of_inRangesB {p : TextPiece} {a : Nat}
    (h : inRangesB p.ranges a = true) : (a, p.img a) ∈ pieceText p := by
  simp only [inRangesB, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨lo, hi⟩, hr, hlo, hhi⟩ := h
  simp only [pieceText, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨(lo, hi), hr, a - lo, by omega, ?_⟩
  have h_add : lo + (a - lo) = a := by omega
  rw [h_add]

theorem textLoaded_pin {ps : List TextPiece} {m : Nat → BitVec 8}
    (hm : TextLoaded (piecesText ps) m) {a : Nat} {b : BitVec 8}
    (h : piecesHasB ps a b = true) : m a = b := by
  simp only [piecesHasB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨p, hp, hr, hb⟩ := h
  subst hb
  apply hm (a, p.img a)
  simp only [piecesText, List.mem_flatMap]
  exact ⟨p, hp, mem_pieceText_of_inRangesB hr⟩

/-- `VsaIris/Vsa/SymExec.lean:59-68`: Little-endian 32-bit word assembly from 4 bytes. -/
def assembleWord32 (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  (((b3.append b2).append b1).append b0)

def wordBytesHasB (ps : List TextPiece) (pc : Nat) (w : BitVec 32) : Bool :=
  piecesHasB ps pc       (w.extractLsb' 0 8)  &&
  piecesHasB ps (pc + 1) (w.extractLsb' 8 8)  &&
  piecesHasB ps (pc + 2) (w.extractLsb' 16 8) &&
  piecesHasB ps (pc + 3) (w.extractLsb' 24 8) &&
  (assembleWord32 (w.extractLsb' 0 8) (w.extractLsb' 8 8)
    (w.extractLsb' 16 8) (w.extractLsb' 24 8) == w)

theorem fetchWord32_of_wordBytesHasB {ps : List TextPiece} {m : Nat → BitVec 8}
    (hm : TextLoaded (piecesText ps) m) {pc : Nat} {w : BitVec 32}
    (hw : wordBytesHasB ps pc w = true) :
    assembleWord32 (m pc) (m (pc + 1)) (m (pc + 2)) (m (pc + 3)) = w := by
  simp only [wordBytesHasB, Bool.and_eq_true, beq_iff_eq] at hw
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, hcomb⟩ := hw
  rw [textLoaded_pin hm h0, textLoaded_pin hm h1, textLoaded_pin hm h2, textLoaded_pin hm h3]
  exact hcomb

/-! ### Normal-Form 32-bit RISC-V Instruction Decoder (`Vsa/Sim/DecodeNF.lean`) -/

inductive DecodedInstr where
  | itype      (imm : BitVec 12) (rs1 rd : RegIdx) (op : IOp)
  | rtype      (rs2 rs1 rd : RegIdx) (op : ROp)
  | zba_rtype  (rs2 rs1 rd : RegIdx) (op : ZbaROp)
  | zbb_rtype  (rs2 rs1 rd : RegIdx) (op : ZbbROp)
  | ret
  | illegal
  deriving DecidableEq, Repr

/-- Pure normal-form decoder (`decodeN` in `Vsa/Sim/DecodeNF.lean:20-43`).
    Evaluates in `O(1)` by `rfl` on any concrete 32-bit instruction word `w`. -/
def decodeN (w : BitVec 32) : DecodedInstr :=
  let opcode := w.extractLsb' 0 7
  let rd     : RegIdx := (w.extractLsb' 7 5).toFin
  let funct3 := w.extractLsb' 12 3
  let rs1    : RegIdx := (w.extractLsb' 15 5).toFin
  let rs2    : RegIdx := (w.extractLsb' 20 5).toFin
  let funct7 := w.extractLsb' 25 7
  let immI   := w.extractLsb' 20 12
  if opcode == 0b0010011#7 then
    if funct3 == 0b000#3 then .itype immI rs1 rd .ADDI
    else if funct3 == 0b111#3 then .itype immI rs1 rd .ANDI
    else if funct3 == 0b110#3 then .itype immI rs1 rd .ORI
    else if funct3 == 0b100#3 then .itype immI rs1 rd .XORI
    else .illegal
  else if opcode == 0b0110011#7 then
    if funct7 == 0b0010000#7 then
      if funct3 == 0b010#3 then .zba_rtype rs2 rs1 rd .SH1ADD
      else if funct3 == 0b100#3 then .zba_rtype rs2 rs1 rd .SH2ADD
      else if funct3 == 0b110#3 then .zba_rtype rs2 rs1 rd .SH3ADD
      else .illegal
    else if funct7 == 0b0100000#7 then
      if funct3 == 0b000#3 then .rtype rs2 rs1 rd .SUB
      else if funct3 == 0b111#3 then .zbb_rtype rs2 rs1 rd .ANDN
      else if funct3 == 0b110#3 then .zbb_rtype rs2 rs1 rd .ORN
      else if funct3 == 0b100#3 then .zbb_rtype rs2 rs1 rd .XNOR
      else .illegal
    else if funct7 == 0b0000101#7 then
      if funct3 == 0b110#3 then .zbb_rtype rs2 rs1 rd .MAXU
      else if funct3 == 0b100#3 then .zbb_rtype rs2 rs1 rd .MINU
      else .illegal
    else if funct7 == 0b0000000#7 then
      if funct3 == 0b000#3 then .rtype rs2 rs1 rd .ADD
      else if funct3 == 0b111#3 then .rtype rs2 rs1 rd .AND
      else if funct3 == 0b110#3 then .rtype rs2 rs1 rd .OR
      else if funct3 == 0b100#3 then .rtype rs2 rs1 rd .XOR
      else .illegal
    else .illegal
  else if w == 0x00008067#32 then
    .ret
  else
    .illegal

/-! ### Concrete 4-Instruction RV64I + Zba + Zbb ELF `.text` Image at `0x80000000`
    Computes `((base + (idx << 2)) &&& ~~~mask) + 16`:
    - `0x80000000`: `sh2add a0, a1, a0` (`0x20a5c533`, `rd=x10, rs1=x11, rs2=x10, funct3=4, funct7=0x10`)
    - `0x80000004`: `andn   a0, a0, a2` (`0x40c57533`, `rd=x10, rs1=x10, rs2=x12, funct3=7, funct7=0x20`)
    - `0x80000008`: `addi   a0, a0, 16` (`0x01050513`, `rd=x10, rs1=x10, imm=16`)
    - `0x8000000c`: `jalr   x0, 0(ra)`  (`0x00008067`, `ret`) -/

def regA0 : RegIdx := (10#5).toFin
def regA1 : RegIdx := (11#5).toFin
def regA2 : RegIdx := (12#5).toFin

def elfLeafByte (addr : Nat) : BitVec 8 :=
  match addr - 0x80000000 with
  -- 0x80000000: 0x20a5c533 (`sh2add a0, a1, a0`)
  | 0  => 0x33#8 | 1  => 0xc5#8 | 2  => 0xa5#8 | 3  => 0x20#8
  -- 0x80000004: 0x40c57533 (`andn a0, a0, a2`)
  | 4  => 0x33#8 | 5  => 0x75#8 | 6  => 0xc5#8 | 7  => 0x40#8
  -- 0x80000008: 0x01050513 (`addi a0, a0, 16`)
  | 8  => 0x13#8 | 9  => 0x05#8 | 10 => 0x05#8 | 11 => 0x01#8
  -- 0x8000000c: 0x00008067 (`ret`)
  | 12 => 0x67#8 | 13 => 0x80#8 | 14 => 0x00#8 | 15 => 0x00#8
  | _  => 0x00#8

def elfLeafPieces : List TextPiece :=
  [{ img := elfLeafByte, ranges := [(0x80000000, 0x80000010)] }]

def elfLeafText : List (Nat × BitVec 8) := piecesText elfLeafPieces

/-- Each 32-bit word decode obligation is closed by `rfl` on `decodeN` (`Vsa/Sim/DecodeNF.lean`). -/
theorem decode_insn0 :
    decodeN 0x20a5c533#32 = .zba_rtype regA0 regA1 regA0 .SH2ADD := rfl

theorem decode_insn1 :
    decodeN 0x40c57533#32 = .zbb_rtype regA2 regA0 regA0 .ANDN := rfl

theorem decode_insn2 :
    decodeN 0x01050513#32 = .itype 0x010#12 regA0 regA0 .ADDI := rfl

theorem decode_insn3 :
    decodeN 0x00008067#32 = .ret := rfl

/-! ### Three Languages Composed via Anneal's `pass_trans`:
    1. `mirLang`: Source Rust MIR function specification.
    2. `rv64BlockLang`: Tier 2 pure `RV64` `BitVec 64` SSA block dialect (`riscv-lean` / `lean-mlir`).
    3. `rv64ElfLang`: Tier 1 byte-addressed Sail RV64 small-step ELF machine (`SmallStepMachine.toLanguage`). -/

structure LeafArgs where
  base : BitVec 64
  idx  : BitVec 64
  mask : BitVec 64

/-- Source MIR specification language (`L₁`). -/
def mirIndexMaskAddSpec (args : LeafArgs) : BitVec 64 :=
  ((args.base + (args.idx <<< 2)) &&& ~~~args.mask) + 16#64

def mirLang : Language where
  Program := Unit
  Input   := LeafArgs
  Output  := BitVec 64
  exec    := fun _ args b => b = .val (mirIndexMaskAddSpec args)

/-- Tier 2 Pure `RV64` SSA Block Dialect language (`L₂`), using `RV64.sh2add`, `RV64.andn`, `RV64.addi`. -/
def rv64DialectBlockDenote (args : LeafArgs) : BitVec 64 :=
  let v0 := RV64.sh2add args.base args.idx
  let v1 := RV64.andn args.mask v0
  let v2 := RV64.addi 0x010#12 v1
  v2

def rv64BlockLang : Language where
  Program := Unit
  Input   := LeafArgs
  Output  := BitVec 64
  exec    := fun _ args b => b = .val (rv64DialectBlockDenote args)

/-- Pass 1 (`mirLang → rv64BlockLang`): MIR to `RV64` SSA dialect lowering. -/
theorem mirToDialect_compiles :
    Compiles mirLang rv64BlockLang (fun a₁ a₂ => a₁ = a₂) (fun o₁ o₂ => o₁ = o₂) () () := by
  intro a₁ a₂ ha b₂ hb₂
  subst ha; subst hb₂
  refine ⟨.val (mirIndexMaskAddSpec a₁), rfl, rv64DialectBlockDenote a₁, rfl, ?_⟩
  simp only [mirIndexMaskAddSpec, rv64DialectBlockDenote, RV64.sh2add, RV64.andn, RV64.addi]
  rw [BitVec.add_comm a₁.base (a₁.idx <<< 2)]
  rfl

/-- Tier 1 Byte-Addressed Sail RV64 Small-Step Machine (`L₃ := rv64ElfMachine.toLanguage`). -/
structure ElfInput where
  args : LeafArgs
  mem  : Nat → BitVec 8

def executeDecoded (ins : DecodedInstr) : SailM ExecutionResult :=
  match ins with
  | .itype imm rs1 rd op     => execute_ITYPE imm rs1 rd op
  | .rtype rs2 rs1 rd op     => execute_RTYPE rs2 rs1 rd op
  | .zba_rtype rs2 rs1 rd op => execute_ZBA_RTYPE rs2 rs1 rd op
  | .zbb_rtype rs2 rs1 rd op => execute_ZBB_RTYPE rs2 rs1 rd op
  | .ret => fun s => .ok .RETIRE_SUCCESS { s with halted := true }
  | .illegal => fun _ => .error .Unreachable ‹_›

def rv64ElfStep (s : SeqState) : StepResult SeqState (BitVec 64) :=
  if s.halted then
    match s.xregs regA0 with
    | some v => .term v
    | none   => .trap
  else
    match s.pc with
    | none => .trap
    | some pc =>
      let addr := pc.toNat
      let w := assembleWord32 (s.mem addr) (s.mem (addr + 1)) (s.mem (addr + 2)) (s.mem (addr + 3))
      let ast := decodeN w
      match (executeDecoded ast).run s with
      | .ok .RETIRE_SUCCESS s' =>
        if s'.halted then
          match s'.xregs regA0 with
          | some v => .term v
          | none   => .trap
        else
          .cont { s' with pc := some (pc + 4#64), nextPC := pc + 8#64 }
      | _ => .trap

def initElfState (inp : ElfInput) : SeqState where
  xregs := fun r =>
    if r = regA0 then some inp.args.base
    else if r = regA1 then some inp.args.idx
    else if r = regA2 then some inp.args.mask
    else some 0#64
  pc     := some 0x80000000#64
  nextPC := 0x80000004#64
  mem    := inp.mem
  halted := false

def rv64ElfMachine : SmallStepMachine where
  Program := List TextPiece
  Input   := ElfInput
  State   := SeqState
  Output  := BitVec 64
  init    := fun _ inp => initElfState inp
  step    := fun _ s   => rv64ElfStep s

abbrev rv64ElfLang : Language := rv64ElfMachine.toLanguage

/-- Relational input condition requiring the ELF `.text` segment to be loaded in `inp.mem`. -/
def RelateDialectElfIn (ps : List TextPiece) (args : LeafArgs) (inp : ElfInput) : Prop :=
  inp.args = args ∧ TextLoaded (piecesText ps) inp.mem

/-- Using `fetchWord32_of_wordBytesHasB` (`by decide`), `decodeN` (`by rfl`), and the
    Stage 1 + Stage 2 purification definitions, the 4-instruction ELF leaf reaches `.term`
    in 3 steps (`n = 3`) from `initElfState inp` with output `rv64DialectBlockDenote inp.args`. -/
theorem elfLeaf_reaches_term (inp : ElfInput)
    (hmem : TextLoaded (piecesText elfLeafPieces) inp.mem) :
    rv64ElfMachine.ReachesPrefix elfLeafPieces 3 (initElfState inp)
      (.term (rv64DialectBlockDenote inp.args)) := by
  have hw0 : assembleWord32 (inp.mem 0x80000000) (inp.mem 0x80000001)
      (inp.mem 0x80000002) (inp.mem 0x80000003) = 0x20a5c533#32 :=
    fetchWord32_of_wordBytesHasB hmem (by decide)
  have hw1 : assembleWord32 (inp.mem 0x80000004) (inp.mem 0x80000005)
      (inp.mem 0x80000006) (inp.mem 0x80000007) = 0x40c57533#32 :=
    fetchWord32_of_wordBytesHasB hmem (by decide)
  have hw2 : assembleWord32 (inp.mem 0x80000008) (inp.mem 0x80000009)
      (inp.mem 0x8000000a) (inp.mem 0x8000000b) = 0x01050513#32 :=
    fetchWord32_of_wordBytesHasB hmem (by decide)
  have hw3 : assembleWord32 (inp.mem 0x8000000c) (inp.mem 0x8000000d)
      (inp.mem 0x8000000e) (inp.mem 0x8000000f) = 0x00008067#32 :=
    fetchWord32_of_wordBytesHasB hmem (by decide)
  let s0 := initElfState inp
  have hstep0 : rv64ElfStep s0 = .cont {
      s0 with
      xregs  := fun k => if k = regA0 then some (RV64.sh2add inp.args.base inp.args.idx) else s0.xregs k
      pc     := some 0x80000004#64
      nextPC := 0x80000008#64
    } := by
    unfold rv64ElfStep s0 initElfState
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    change (let w := assembleWord32 (inp.mem 0x80000000) (inp.mem 0x80000001)
              (inp.mem 0x80000002) (inp.mem 0x80000003); _) = _
    rw [hw0, decode_insn0]
    rfl
  let s1 : SeqState := {
    s0 with
    xregs  := fun k => if k = regA0 then some (RV64.sh2add inp.args.base inp.args.idx) else s0.xregs k
    pc     := some 0x80000004#64
    nextPC := 0x80000008#64
  }
  have hstep1 : rv64ElfStep s1 = .cont {
      s1 with
      xregs  := fun k => if k = regA0 then some (RV64.andn inp.args.mask (RV64.sh2add inp.args.base inp.args.idx)) else s1.xregs k
      pc     := some 0x80000008#64
      nextPC := 0x8000000c#64
    } := by
    unfold rv64ElfStep s1 s0 initElfState
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    change (let w := assembleWord32 (inp.mem 0x80000004) (inp.mem 0x80000005)
              (inp.mem 0x80000006) (inp.mem 0x80000007); _) = _
    rw [hw1, decode_insn1]
    rfl
  let s2 : SeqState := {
    s1 with
    xregs  := fun k => if k = regA0 then some (RV64.andn inp.args.mask (RV64.sh2add inp.args.base inp.args.idx)) else s1.xregs k
    pc     := some 0x80000008#64
    nextPC := 0x8000000c#64
  }
  have hstep2 : rv64ElfStep s2 = .cont {
      s2 with
      xregs  := fun k => if k = regA0 then some (rv64DialectBlockDenote inp.args) else s2.xregs k
      pc     := some 0x8000000c#64
      nextPC := 0x80000010#64
    } := by
    unfold rv64ElfStep s2 s1 s0 initElfState
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    change (let w := assembleWord32 (inp.mem 0x80000008) (inp.mem 0x80000009)
              (inp.mem 0x8000000a) (inp.mem 0x8000000b); _) = _
    rw [hw2, decode_insn2]
    rfl
  let s3 : SeqState := {
    s2 with
    xregs  := fun k => if k = regA0 then some (rv64DialectBlockDenote inp.args) else s2.xregs k
    pc     := some 0x8000000c#64
    nextPC := 0x80000010#64
  }
  have hstep3 : rv64ElfStep s3 = .term (rv64DialectBlockDenote inp.args) := by
    unfold rv64ElfStep s3 s2 s1 s0 initElfState
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    change (let w := assembleWord32 (inp.mem 0x8000000c) (inp.mem 0x8000000d)
              (inp.mem 0x8000000e) (inp.mem 0x8000000f); _) = _
    rw [hw3, decode_insn3]
    rfl
  have hreach3 : rv64ElfMachine.ReachesIn elfLeafPieces 3 s0 (.term (rv64DialectBlockDenote inp.args)) :=
    ⟨s1, hstep0, s2, hstep1, s3, hstep2, hstep3⟩
  refine ⟨hreach3, ?_⟩
  intro k hk
  match k with
  | 0 => exact ⟨s1, hstep0⟩
  | 1 => exact ⟨s2, s1, hstep0, hstep1⟩
  | 2 => exact ⟨s3, s1, hstep0, s2, hstep1, hstep2⟩
  | k + 3 => omega

/-- Because `rv64ElfMachine` is deterministic (`ReachesIn_deterministic`), any behavior
    `b₃` of `elfLeafPieces` under `TextLoaded` must equal `.val (rv64DialectBlockDenote inp.args)`. -/
theorem elfLeaf_behavior_unique (inp : ElfInput)
    (hmem : TextLoaded (piecesText elfLeafPieces) inp.mem)
    (b₃ : Partial (BitVec 64))
    (hb₃ : rv64ElfMachine.BehaviorOf elfLeafPieces inp b₃) :
    b₃ = .val (rv64DialectBlockDenote inp.args) := by
  rcases hb₃ with ⟨n, v, hreach_n, hpre_n⟩ | hdiv | ⟨n, hreach_n, hpre_n⟩
  · obtain ⟨hreach3, hpre3⟩ := elfLeaf_reaches_term inp hmem
    by_cases hlt : n < 3
    · obtain ⟨s', hs'⟩ := hpre3 n hlt
      have hEq := rv64ElfMachine.ReachesIn_deterministic elfLeafPieces n _ _ _ hreach_n hs'
      injection hEq
    · by_cases hgt : 3 < n
      · obtain ⟨s', hs'⟩ := hpre_n 3 hgt
        have hEq := rv64ElfMachine.ReachesIn_deterministic elfLeafPieces 3 _ _ _ hreach3 hs'
        injection hEq
      · have hn : n = 3 := by omega
        subst hn
        have hEq := rv64ElfMachine.ReachesIn_deterministic elfLeafPieces 3 _ _ _ hreach_n hreach3
        injection hEq with hEq'
        exact congrArg Partial.val hEq'
  · obtain ⟨hreach3, _⟩ := elfLeaf_reaches_term inp hmem
    obtain ⟨s', hs'⟩ := hdiv 3
    have hEq := rv64ElfMachine.ReachesIn_deterministic elfLeafPieces 3 _ _ _ hreach3 hs'
    injection hEq
  · obtain ⟨hreach3, hpre3⟩ := elfLeaf_reaches_term inp hmem
    by_cases hlt : n < 3
    · obtain ⟨s', hs'⟩ := hpre3 n hlt
      have hEq := rv64ElfMachine.ReachesIn_deterministic elfLeafPieces n _ _ _ hreach_n hs'
      injection hEq
    · by_cases hgt : 3 < n
      · obtain ⟨s', hs'⟩ := hpre_n 3 hgt
        have hEq := rv64ElfMachine.ReachesIn_deterministic elfLeafPieces 3 _ _ _ hreach3 hs'
        injection hEq
      · have hn : n = 3 := by omega
        subst hn
        have hEq := rv64ElfMachine.ReachesIn_deterministic elfLeafPieces 3 _ _ _ hreach_n hreach3
        injection hEq

/-- Pass 2 (`rv64BlockLang → rv64ElfLang`): Pure `RV64` dialect block to byte-pinned ELF image. -/
theorem dialectToElf_compiles :
    Compiles rv64BlockLang rv64ElfLang
      (RelateDialectElfIn elfLeafPieces) (fun o₂ o₃ => o₂ = o₃) () elfLeafPieces := by
  intro args inp ⟨hargs, hmem⟩ b₃ hb₃
  have hb₃_eq := elfLeaf_behavior_unique inp hmem b₃ hb₃
  subst hargs
  exact ⟨.val (rv64DialectBlockDenote inp.args), rfl,
    rv64DialectBlockDenote inp.args, hb₃_eq, rfl⟩

/-- End-to-End Compiler (`mirLang → rv64ElfLang`) verified via Anneal's `pass_trans`. -/
def mirToRiscv64ElfCompiler : Compiler mirLang rv64ElfLang where
  compile   := fun _ => some elfLeafPieces
  relateIn  := RelateDialectElfIn elfLeafPieces
  relateOut := fun o₁ o₃ => o₁ = o₃

theorem mirToRiscv64ElfCompiler_verified : mirToRiscv64ElfCompiler.Verified := by
  intro s t hcomp
  cases s
  injection hcomp with ht
  subst ht
  intro args inp hin b₃ hb₃
  obtain ⟨b₁, hb₁, hchain⟩ :=
    pass_trans mirToDialect_compiles dialectToElf_compiles (i₂ := args) rfl hin b₃ hb₃
  refine ⟨b₁, hb₁, ?_⟩
  cases b₁ with
  | ub => trivial
  | div => exact hchain
  | val o₁ =>
    obtain ⟨o₂, o₃, hb₃_eq, rfl, rfl⟩ := hchain
    exact ⟨o₁, hb₃_eq, rfl⟩


/-! ============================================================================
    SECTION 5: AXIOM BOUNDARY AUDIT (`#guard_msgs` + `#print axioms`)
    Verifies compatibility with `trusted/audit/TrustedBoundary.lean` and
    `trusted/lean/foundation-lock.json` (zero `sorryAx`, zero `Lean.ofReduceBool`).
    ============================================================================ -/

/-- info: 'TwoTierIsaDialectAndElfRefinementProbe.zicond_not_unconditional_skeleton_binary' does not depend on any axioms -/
#guard_msgs in
#print axioms zicond_not_unconditional_skeleton_binary

/-- info: 'TwoTierIsaDialectAndElfRefinementProbe.zicond_rtype_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms zicond_rtype_eq

/-- info: 'TwoTierIsaDialectAndElfRefinementProbe.cpopLoopSail_eq_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cpopLoopSail_eq_pure

/-- info: 'TwoTierIsaDialectAndElfRefinementProbe.llvm_zba_sh2add_peephole_refine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms llvm_zba_sh2add_peephole_refine

/-- info: 'TwoTierIsaDialectAndElfRefinementProbe.llvm_zbb_andn_peephole_refine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms llvm_zbb_andn_peephole_refine

/-- info: 'TwoTierIsaDialectAndElfRefinementProbe.mirToRiscv64ElfCompiler_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mirToRiscv64ElfCompiler_verified

end TwoTierIsaDialectAndElfRefinementProbe
