/-
  sail_tiny_arm_and_capability_bridge_probe.lean

  Standalone Lean 4.34.1 mechanization for Chunk 5:
    (1) Anneal's exact `StepResult`, `SmallStepMachine`, `BehaviorOf`, and
        `BridgeTransition` refinement vocabulary (`Trusted/StepResult.lean`,
        `Trusted/Refinement.lean`, `Trusted/Memory.lean`).
    (2) The `rems-project/sail-tiny-arm-lean` (`SailTinyArmUser`, commit
        `4a474cfc415e46a0f6251c8c7d58a85e6411eb7b`) monadic `PreSailM`/`PreSailME`
        decode-execute architecture (`decode : BitVec 32 → SailM ast`,
        `execute : ast → SailM Unit`, `fetch_and_execute : Unit → SailM Unit`
        with `SailME.run` early-return semantics) bridged into `BridgeTransition`.
    (3) A CHERI capability-tagged register and memory machine (`CapWord`,
        `CapBounds`, `Perms`, 16-byte capability granules) capturing Arm Morello
        (`CTSRD-CHERI/sail-morello`), CHERI-RISC-V (`CTSRD-CHERI/sail-cheri-riscv`),
        and CHERIoT (`CHERIoT-Platform/cheriot-sail`), proving:
        - capability monotonicity (`cSetBounds`, `cAndPerm`, `cIncOffset`),
        - raw byte stores unconditionally strip the enclosing capability tag
          (`writeRawByte_strips_enclosing_cap_tag`),
        - capability loads without `LoadCap` permission strip the loaded tag
          (`readCapGranule_without_loadCap_strips_tag`), and
        - hardware-enforced capability bounds/permissions refine Anneal's
          spatial and provenance memory safety checks via `BridgeTransition`.
-/

namespace SailArmX86CheriRiscvProbe

/-! ## Part 1: Anneal Trusted Core Refinement Vocabulary (`Trusted/StepResult.lean`, `Trusted/Refinement.lean`) -/

structure Preorder (α : Type u) where
  le : α → α → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c

abbrev Partial (α : Type u) := α → Prop

namespace Partial

def subset {α : Type u} (P Q : Partial α) : Prop :=
  ∀ a, P a → Q a

def preorder (α : Type u) : Preorder (Partial α) where
  le := subset
  refl := by intro P a ha; exact ha
  trans := by intro P Q R hPQ hQR a ha; exact hQR a (hPQ a ha)

end Partial

inductive StepResult (σ : Type u) where
  | next (s' : σ)
  | done
  | trap
  | stuck
  deriving DecidableEq, Repr

inductive PrefixOutcome where
  | running
  | terminated
  | trapped
  | wentStuck
  deriving DecidableEq, Repr

structure SmallStepMachine (σ : Type u) (ε : Type v) where
  init : σ → Prop
  step : σ → StepResult (σ × List ε)

inductive ReachesPrefix {σ : Type u} {ε : Type v}
    (m : SmallStepMachine σ ε) : σ → List ε → PrefixOutcome → Prop where
  | zero (s : σ) :
      ReachesPrefix m s [] .running
  | done {s : σ} :
      m.step s = .done →
      ReachesPrefix m s [] .terminated
  | trap {s : σ} :
      m.step s = .trap →
      ReachesPrefix m s [] .trapped
  | stuck {s : σ} :
      m.step s = .stuck →
      ReachesPrefix m s [] .wentStuck
  | step {s s' : σ} {ev rest : List ε} {out : PrefixOutcome} :
      m.step s = .next (s', ev) →
      ReachesPrefix m s' rest out →
      ReachesPrefix m s (ev ++ rest) out

def BehaviorOf {σ : Type u} {ε : Type v}
    (m : SmallStepMachine σ ε) : Partial (List ε × PrefixOutcome) :=
  fun ⟨trace, out⟩ => ∃ s₀, m.init s₀ ∧ ReachesPrefix m s₀ trace out

structure BridgeTransition (σ : Type u) where
  pre : σ → Prop
  step : σ → StepResult σ
  nextRel : σ → σ → Prop
  sound :
    ∀ s, pre s →
      match step s with
      | .next s' => nextRel s s'
      | .done => True
      | .trap => True
      | .stuck => False

theorem BridgeTransition.no_stuck {σ : Type u}
    (br : BridgeTransition σ) {s : σ} (hpre : br.pre s) :
    br.step s ≠ .stuck := by
  intro hstuck
  have hsound := br.sound s hpre
  rw [hstuck] at hsound
  exact hsound

/-! ## Part 2: `sail-tiny-arm-lean` (`SailTinyArmUser`) Monadic Decode-Execute Architecture -/

namespace SailTinyArmModel

/-- Architectural register identifiers from `SailTinyArmUser/Defs.lean`. -/
inductive Register where
  | R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  | R16 | R17 | R18 | R19 | R20 | R21 | R22 | R23
  | R24 | R25 | R26 | R27 | R28 | R29 | R30
  | _PC
  | NZCV
  | SP_EL0
  deriving DecidableEq, Repr

/-- Sail runtime error type (`Sail.Error`). -/
inductive Error where
  | Exit
  | Unreachable
  | Assertion (msg : String)
  deriving DecidableEq, Repr

/-- Sequential machine state backing `SailM` in `SailTinyArmUser`. -/
structure SequentialState where
  gprs : Fin 31 → BitVec 64
  pc : BitVec 64
  nzcv : BitVec 4
  sp_el0 : BitVec 64
  mem : BitVec 64 → BitVec 8

/-- `SailM α` is `ExceptT Error (StateM SequentialState) α`. -/
abbrev SailM (α : Type) := SequentialState → Except Error (α × SequentialState)

instance : Monad SailM where
  pure a := fun s => .ok (a, s)
  bind m f := fun s =>
    match m s with
    | .ok (a, s') => f a s'
    | .error e => .error e

@[simp] theorem sailM_pure (a : α) (s : SequentialState) :
    (pure a : SailM α) s = .ok (a, s) := rfl

@[simp] theorem sailM_bind (m : SailM α) (f : α → SailM β) (s : SequentialState) :
    (m >>= f) s = match m s with | .ok (a, s') => f a s' | .error e => .error e := rfl

def sailThrow (e : Error) : SailM α :=
  fun _ => .error e

def sailAssert (cond : Bool) (msg : String) : SailM Unit :=
  if cond then pure () else sailThrow (.Assertion msg)

/-- Early-return monad transformer `SailME e α` emitted by `sail --lean` (`v7`). -/
abbrev SailME (e α : Type) := ExceptT e SailM α

namespace SailME

def throw (v : e) : SailME e α :=
  ExceptT.mk (pure (.error v))

def lift (m : SailM α) : SailME e α :=
  ExceptT.mk (do let a ← m; pure (.ok a))

def run (m : SailME α α) : SailM α := do
  let r ← ExceptT.run m
  match r with
  | .ok a => pure a
  | .error a => pure a

end SailME

/-- Read 64-bit general-purpose register (`X31` is hardwired zero `XZR`). -/
def rX (n : Fin 32) : SailM (BitVec 64) :=
  fun s =>
    if h : n.val < 31 then
      .ok (s.gprs ⟨n.val, h⟩, s)
    else
      .ok (0#64, s)

/-- Write 64-bit general-purpose register (`X31` writes are ignored). -/
def wX (n : Fin 32) (v : BitVec 64) : SailM Unit :=
  fun s =>
    if h : n.val < 31 then
      let r : Fin 31 := ⟨n.val, h⟩
      .ok ((), { s with gprs := fun i => if i = r then v else s.gprs i })
    else
      .ok ((), s)

def rPC : SailM (BitVec 64) :=
  fun s => .ok (s.pc, s)

def wPC (v : BitVec 64) : SailM Unit :=
  fun s => .ok ((), { s with pc := v })

/-- User-mode address translation (`SailTinyArmUser/Translation.lean:55-56`). -/
def translate_address (va : BitVec 64) : Option (BitVec 64) :=
  some va

/-- Little-endian 64-bit read from byte-addressed memory. -/
def rMem64 (pa : BitVec 64) : SailM (BitVec 64) :=
  fun s =>
    let b0 := (s.mem (pa + 0#64)).zeroExtend 64
    let b1 := (s.mem (pa + 1#64)).zeroExtend 64 <<< 8
    let b2 := (s.mem (pa + 2#64)).zeroExtend 64 <<< 16
    let b3 := (s.mem (pa + 3#64)).zeroExtend 64 <<< 24
    let b4 := (s.mem (pa + 4#64)).zeroExtend 64 <<< 32
    let b5 := (s.mem (pa + 5#64)).zeroExtend 64 <<< 40
    let b6 := (s.mem (pa + 6#64)).zeroExtend 64 <<< 48
    let b7 := (s.mem (pa + 7#64)).zeroExtend 64 <<< 56
    .ok (b0 ||| b1 ||| b2 ||| b3 ||| b4 ||| b5 ||| b6 ||| b7, s)

/-- Little-endian 64-bit write to byte-addressed memory. -/
def wMem64 (pa : BitVec 64) (v : BitVec 64) : SailM Unit :=
  fun s =>
    let b0 : BitVec 8 := (v >>> 0).truncate 8
    let b1 : BitVec 8 := (v >>> 8).truncate 8
    let b2 : BitVec 8 := (v >>> 16).truncate 8
    let b3 : BitVec 8 := (v >>> 24).truncate 8
    let b4 : BitVec 8 := (v >>> 32).truncate 8
    let b5 : BitVec 8 := (v >>> 40).truncate 8
    let b6 : BitVec 8 := (v >>> 48).truncate 8
    let b7 : BitVec 8 := (v >>> 56).truncate 8
    let mem' : BitVec 64 → BitVec 8 := fun a =>
      if a = pa + 0#64 then b0
      else if a = pa + 1#64 then b1
      else if a = pa + 2#64 then b2
      else if a = pa + 3#64 then b3
      else if a = pa + 4#64 then b4
      else if a = pa + 5#64 then b5
      else if a = pa + 6#64 then b6
      else if a = pa + 7#64 then b7
      else s.mem a
    .ok ((), { s with mem := mem' })

/-- Little-endian 32-bit instruction fetch (`iFetch`). -/
def iFetch (pa : BitVec 64) : SailM (BitVec 32) :=
  fun s =>
    let b0 := (s.mem (pa + 0#64)).zeroExtend 32
    let b1 := (s.mem (pa + 1#64)).zeroExtend 32 <<< 8
    let b2 := (s.mem (pa + 2#64)).zeroExtend 32 <<< 16
    let b3 := (s.mem (pa + 3#64)).zeroExtend 32 <<< 24
    .ok (b0 ||| b1 ||| b2 ||| b3, s)

/-- Representative subset of `SailTinyArmUser`'s 17-constructor `ast` inductive. -/
inductive ast where
  | Movz (rd : Fin 32) (imm : BitVec 16) (hw : BitVec 2)
  | AddSub (op : BitVec 1) (rd : Fin 32) (rn : Fin 32) (rm : Fin 32)
  | Load (rt : Fin 32) (rn : Fin 32) (rm : Fin 32)
  | Store (rt : Fin 32) (rn : Fin 32) (rm : Fin 32)
  | CompareAndBranch (rt : Fin 32) (iszero : Bool) (offset : BitVec 64)
  | Nop
  deriving DecidableEq, Repr

def regOfBits5 (b : BitVec 5) : Fin 32 :=
  ⟨b.toNat, b.isLt⟩

/-- Monadic `decode : BitVec 32 → SailM ast` matching `SailTinyArmUser/TinyArm.lean:56-538`. -/
def decode (op : BitVec 32) : SailM ast := do
  if op == 0xD503201F#32 then
    pure .Nop
  else if op.extractLsb 31 23 == 0b110100101#9 then
    let hw := op.extractLsb 22 21
    let imm := op.extractLsb 20 5
    let rd := regOfBits5 (op.extractLsb 4 0)
    pure (.Movz rd imm hw)
  else if (op.extractLsb 31 31 == 0b1#1) && (op.extractLsb 29 21 == 0b001011000#9) &&
          (op.extractLsb 15 10 == 0b000000#6) then
    let subOp := op.extractLsb 30 30
    let rm := regOfBits5 (op.extractLsb 20 16)
    let rn := regOfBits5 (op.extractLsb 9 5)
    let rd := regOfBits5 (op.extractLsb 4 0)
    pure (.AddSub subOp rd rn rm)
  else if (op.extractLsb 31 21 == 0b11111000011#11) && (op.extractLsb 15 10 == 0b011010#6) then
    let rm := regOfBits5 (op.extractLsb 20 16)
    let rn := regOfBits5 (op.extractLsb 9 5)
    let rt := regOfBits5 (op.extractLsb 4 0)
    pure (.Load rt rn rm)
  else if (op.extractLsb 31 21 == 0b11111000001#11) && (op.extractLsb 15 10 == 0b011010#6) then
    let rm := regOfBits5 (op.extractLsb 20 16)
    let rn := regOfBits5 (op.extractLsb 9 5)
    let rt := regOfBits5 (op.extractLsb 4 0)
    pure (.Store rt rn rm)
  else if op.extractLsb 31 25 == 0b1011010#7 then
    let isnotzero := op.extractLsb 24 24
    let imm19 := op.extractLsb 23 5
    let rt := regOfBits5 (op.extractLsb 4 0)
    let offset : BitVec 64 := (imm19 ++ 0b00#2).signExtend 64
    pure (.CompareAndBranch rt (isnotzero == 0b0#1) offset)
  else
    sailThrow (.Assertion "decode: unsupported instruction")

def execute_Movz (rd : Fin 32) (imm : BitVec 16) (hw : BitVec 2) : SailM Unit := do
  let shift := hw.toNat * 16
  let val : BitVec 64 := (imm.zeroExtend 64) <<< shift
  wX rd val
  let pc ← rPC
  wPC (pc + 4#64)

def execute_AddSub (op : BitVec 1) (rd rn rm : Fin 32) : SailM Unit := do
  let v1 ← rX rn
  let v2 ← rX rm
  let res := if op == 0b0#1 then v1 + v2 else v1 - v2
  wX rd res
  let pc ← rPC
  wPC (pc + 4#64)

/-- `execute_Load` with `SailME.run` early-return pattern from `SailTinyArmUser/TinyArm.lean`. -/
def execute_Load (rt rn rm : Fin 32) : SailM Unit :=
  SailME.run do
    let base ← SailME.lift (rX rn)
    let off ← SailME.lift (rX rm)
    let va := base + off
    let pa ← match translate_address va with
      | some addr => pure addr
      | none => SailME.throw ()
    let data ← SailME.lift (rMem64 pa)
    SailME.lift (wX rt data)
    let pc ← SailME.lift rPC
    SailME.lift (wPC (pc + 4#64))

/-- `execute_Store` with `SailME.run` early-return pattern from `SailTinyArmUser/TinyArm.lean`. -/
def execute_Store (rt rn rm : Fin 32) : SailM Unit :=
  SailME.run do
    let base ← SailME.lift (rX rn)
    let off ← SailME.lift (rX rm)
    let va := base + off
    let pa ← match translate_address va with
      | some addr => pure addr
      | none => SailME.throw ()
    let data ← SailME.lift (rX rt)
    SailME.lift (wMem64 pa data)
    let pc ← SailME.lift rPC
    SailME.lift (wPC (pc + 4#64))

def execute_CompareAndBranch (rt : Fin 32) (iszero : Bool) (offset : BitVec 64) : SailM Unit := do
  let operand ← rX rt
  let pc ← rPC
  if (operand == 0#64) == iszero then
    wPC (pc + offset)
  else
    wPC (pc + 4#64)

def execute (ins : ast) : SailM Unit :=
  match ins with
  | .Movz rd imm hw => execute_Movz rd imm hw
  | .AddSub op rd rn rm => execute_AddSub op rd rn rm
  | .Load rt rn rm => execute_Load rt rn rm
  | .Store rt rn rm => execute_Store rt rn rm
  | .CompareAndBranch rt iszero offset => execute_CompareAndBranch rt iszero offset
  | .Nop => do
      let pc ← rPC
      wPC (pc + 4#64)

/-- `fetch_and_execute` matching `SailTinyArmUser/TinyArm.lean:1058-1071`. -/
def fetch_and_execute (_ : Unit) : SailM Unit :=
  SailME.run do
    let va ← SailME.lift rPC
    let pa ← match translate_address va with
      | some addr => pure addr
      | none => SailME.throw ()
    let machineCode ← SailME.lift (iFetch pa)
    let instr ← SailME.lift (decode machineCode)
    SailME.lift (execute instr)

/-- `XZR` (`X31`) always reads as `0#64` and ignores writes. -/
theorem rX_xzr (s : SequentialState) :
    rX ⟨31, by decide⟩ s = .ok (0#64, s) := rfl

theorem wX_xzr (v : BitVec 64) (s : SequentialState) :
    wX ⟨31, by decide⟩ v s = .ok ((), s) := rfl

/-- Decoding `0xD503201F` (`NOP`) succeeds and yields `.Nop`. -/
theorem decode_nop (s : SequentialState) :
    decode 0xD503201F#32 s = .ok (.Nop, s) := rfl

/-- Decoding `ADD X0, X1, X2` (`0x8B020020`) yields `.AddSub 0b0 0 1 2`. -/
theorem decode_add_x0_x1_x2 (s : SequentialState) :
    decode 0x8B020020#32 s =
      .ok (.AddSub 0b0#1 ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩, s) := rfl

/-- Executing `AddSub 0b0 X0 X1 X2` writes `X1 + X2` to `X0` and advances `_PC` by 4. -/
theorem execute_add_x0_x1_x2 (s : SequentialState) :
    execute (.AddSub 0b0#1 ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩) s =
      .ok ((), { s with
        gprs := fun i =>
          if i = ⟨0, by decide⟩ then
            s.gprs ⟨1, by decide⟩ + s.gprs ⟨2, by decide⟩
          else s.gprs i
        pc := s.pc + 4#64 }) := rfl

/-- Converting `SailM Unit` into Anneal's `StepResult SequentialState` (never `.stuck`). -/
def sailToStepResult (m : SailM Unit) (s : SequentialState) : StepResult SequentialState :=
  match m s with
  | .ok ((), s') => .next s'
  | .error _ => .trap

/-- BridgeTransition packaging `SailTinyArmUser`'s `fetch_and_execute` into Anneal's TCB. -/
def tinyArmBridge : BridgeTransition SequentialState where
  pre := fun _ => True
  step := sailToStepResult (fetch_and_execute ())
  nextRel := fun s s' => fetch_and_execute () s = .ok ((), s')
  sound := by
    intro s _
    unfold sailToStepResult
    cases h : fetch_and_execute () s with
    | ok pair =>
      rcases pair with ⟨⟨⟩, s'⟩
      simp
    | error _ =>
      simp

theorem tinyArmBridge_never_stuck (s : SequentialState) :
    tinyArmBridge.step s ≠ .stuck :=
  tinyArmBridge.no_stuck trivial

end SailTinyArmModel

/-! ## Part 2b: `sail-tiny-x86` RIP-Relative Effective Address Bug (`decode.sail:300-308`) -/

namespace SailTinyX86DecodeAudit

/-- Effective address computed by `rems-project/sail-tiny-x86/model/decode.sail:300-308`
    when `mod == 0b00 & three_bit_rm_reg == 5`: adds sign-extended 32-bit displacement to
    the un-incremented `rip` passed into `decode(rip)` before `new_rip` is computed. -/
def tinyX86DecodedRipRelativeAddr (ripAtFetch : BitVec 64) (disp32 : BitVec 32) : BitVec 64 :=
  ripAtFetch + disp32.signExtend 64

/-- Architectural x86-64 RIP-relative effective address (`new_rip + signExtend(disp32)`),
    where `new_rip = ripAtFetch + instrLen`. -/
def archX86RipRelativeAddr
    (ripAtFetch instrLen : BitVec 64) (disp32 : BitVec 32) : BitVec 64 :=
  (ripAtFetch + instrLen) + disp32.signExtend 64

/-- Exact algebraic discrepancy: `archX86RipRelativeAddr` exceeds `tinyX86DecodedRipRelativeAddr`
    by `instrLen`. -/
theorem tinyX86_rip_relative_discrepancy
    (ripAtFetch instrLen : BitVec 64) (disp32 : BitVec 32) :
    archX86RipRelativeAddr ripAtFetch instrLen disp32 -
      tinyX86DecodedRipRelativeAddr ripAtFetch disp32 = instrLen := by
  unfold archX86RipRelativeAddr tinyX86DecodedRipRelativeAddr
  bv_omega

/-- Concrete counterexample: a 7-byte `MOV RAX, [RIP + 0x10]` (`48 8B 05 10 00 00 00`)
    at `rip = 0x1000` resolves to `0x1010` in `sail-tiny-x86` instead of `0x1017`. -/
theorem tinyX86_mov_rip_rel_counterexample :
    tinyX86DecodedRipRelativeAddr 0x1000#64 0x10#32 = 0x1010#64 ∧
    archX86RipRelativeAddr 0x1000#64 7#64 0x10#32 = 0x1017#64 ∧
    tinyX86DecodedRipRelativeAddr 0x1000#64 0x10#32 ≠
      archX86RipRelativeAddr 0x1000#64 7#64 0x10#32 := by
  decide

end SailTinyX86DecodeAudit

/-! ## Part 3: CHERI Capability Machine & Refinement to Anneal Spatial/Provenance Memory -/

namespace CheriCapabilityBridge

/-- Architectural capability permissions (`CTSRD-CHERI/sail-morello` & `sail-cheri-riscv`). -/
structure Perms where
  canLoad : Bool
  canStore : Bool
  canExecute : Bool
  canLoadCap : Bool
  canStoreCap : Bool
  canSeal : Bool
  canUnseal : Bool
  isGlobal : Bool
  deriving DecidableEq, Repr

namespace Perms

/-- Permission inclusion order (`p₁` has at most the permissions of `p₂`). -/
def le (p₁ p₂ : Perms) : Prop :=
  (p₁.canLoad = true → p₂.canLoad = true) ∧
  (p₁.canStore = true → p₂.canStore = true) ∧
  (p₁.canExecute = true → p₂.canExecute = true) ∧
  (p₁.canLoadCap = true → p₂.canLoadCap = true) ∧
  (p₁.canStoreCap = true → p₂.canStoreCap = true) ∧
  (p₁.canSeal = true → p₂.canSeal = true) ∧
  (p₁.canUnseal = true → p₂.canUnseal = true) ∧
  (p₁.isGlobal = true → p₂.isGlobal = true)

/-- Bitwise permission masking (`CAndPerm`). -/
def inter (p mask : Perms) : Perms where
  canLoad := p.canLoad && mask.canLoad
  canStore := p.canStore && mask.canStore
  canExecute := p.canExecute && mask.canExecute
  canLoadCap := p.canLoadCap && mask.canLoadCap
  canStoreCap := p.canStoreCap && mask.canStoreCap
  canSeal := p.canSeal && mask.canSeal
  canUnseal := p.canUnseal && mask.canUnseal
  isGlobal := p.isGlobal && mask.isGlobal

theorem le_refl (p : Perms) : Perms.le p p := by
  exact ⟨id, id, id, id, id, id, id, id⟩

theorem le_trans {p₁ p₂ p₃ : Perms} (h₁₂ : Perms.le p₁ p₂) (h₂₃ : Perms.le p₂ p₃) :
    Perms.le p₁ p₃ := by
  rcases h₁₂ with ⟨l1, s1, x1, lc1, sc1, se1, us1, g1⟩
  rcases h₂₃ with ⟨l2, s2, x2, lc2, sc2, se2, us2, g2⟩
  exact ⟨fun h => l2 (l1 h), fun h => s2 (s1 h), fun h => x2 (x1 h),
         fun h => lc2 (lc1 h), fun h => sc2 (sc1 h), fun h => se2 (se1 h),
         fun h => us2 (us1 h), fun h => g2 (g1 h)⟩

theorem inter_le_left (p mask : Perms) : Perms.le (p.inter mask) p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; simp [inter, Bool.and_eq_true] at h; exact h.1)

end Perms

/-- Decoded capability bounds `[base, top)` (`getCapBounds` in CHERI Sail models). -/
structure CapBounds where
  base : Nat
  top : Nat
  deriving DecidableEq, Repr

namespace CapBounds

/-- Half-open range containment `[addr, addr + width) ⊆ [base, top)`. -/
def containsRange (b : CapBounds) (addr width : Nat) : Bool :=
  decide (b.base ≤ addr ∧ addr + width ≤ b.top)

/-- Bounds inclusion (`b₁ ⊆ b₂`). -/
def subset (b₁ b₂ : CapBounds) : Prop :=
  b₂.base ≤ b₁.base ∧ b₁.top ≤ b₂.top

theorem subset_refl (b : CapBounds) : CapBounds.subset b b :=
  ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem subset_trans {b₁ b₂ b₃ : CapBounds}
    (h₁₂ : CapBounds.subset b₁ b₂) (h₂₃ : CapBounds.subset b₂ b₃) :
    CapBounds.subset b₁ b₃ :=
  ⟨Nat.le_trans h₂₃.1 h₁₂.1, Nat.le_trans h₁₂.2 h₂₃.2⟩

theorem containsRange_mono {b₁ b₂ : CapBounds} {addr width : Nat}
    (hsub : CapBounds.subset b₁ b₂)
    (hin : b₁.containsRange addr width = true) :
    b₂.containsRange addr width = true := by
  simp only [containsRange, decide_eq_true_eq] at hin ⊢
  exact ⟨Nat.le_trans hsub.1 hin.1, Nat.le_trans hin.2 hsub.2⟩

end CapBounds

/-- A CHERI capability word (`CapWord`) with out-of-band validity `tag : Bool`
    and ghost allocation provenance `allocId : Option Nat` for the Anneal bridge. -/
structure CapWord where
  addr : BitVec 64
  bounds : CapBounds
  perms : Perms
  otype : Nat
  tag : Bool
  allocId : Option Nat
  deriving DecidableEq, Repr

namespace CapWord

/-- Unsealed capabilities have `otype = 0` (`CAP_OTYPE_UNSEALED` in Morello). -/
def isUnsealed (c : CapWord) : Bool :=
  decide (c.otype = 0)

/-- Check whether `[c.addr, c.addr + width)` lies within `c.bounds`. -/
def inBounds (c : CapWord) (width : Nat) : Bool :=
  c.bounds.containsRange c.addr.toNat width

/-- `CAndPerm`: masks permissions; clears tag if input capability is sealed. -/
def cAndPerm (c : CapWord) (mask : Perms) : CapWord :=
  { c with
    perms := c.perms.inter mask
    tag := c.tag && c.isUnsealed }

/-- `CSetBounds`: narrows bounds to `[c.addr, c.addr + reqLen)`; clears tag if
    sealed, out-of-bounds, or non-representable (`exact`). -/
def cSetBounds (c : CapWord) (reqLen : Nat) (representable : Bool) : CapWord :=
  let newBase := c.addr.toNat
  let newTop := newBase + reqLen
  let withinOld := decide (c.bounds.base ≤ newBase ∧ newTop ≤ c.bounds.top)
  { c with
    bounds := { base := newBase, top := newTop }
    tag := c.tag && c.isUnsealed && withinOld && representable }

/-- `CIncOffset`: increments address by `delta`; clears tag if sealed or
    if the new address violates representability bounds. -/
def cIncOffset (c : CapWord) (delta : BitVec 64) (representable : Bool) : CapWord :=
  { c with
    addr := c.addr + delta
    tag := c.tag && c.isUnsealed && representable }

/-- Monotonicity predicate (`leq_cap` in `coq-cheri-capabilities` / `prop_setbounds_monotonic`
    in `CHERIoT-Platform/cheriot-sail`): any tagged result capability derives from a tagged
    unsealed parent with narrower-or-equal bounds, subset permissions, and identical provenance. -/
def DerivedMonotone (c' c : CapWord) : Prop :=
  c'.tag = true →
    c.tag = true ∧
    c.isUnsealed = true ∧
    CapBounds.subset c'.bounds c.bounds ∧
    Perms.le c'.perms c.perms ∧
    c'.allocId = c.allocId

theorem cAndPerm_monotone (c : CapWord) (mask : Perms) :
    DerivedMonotone (c.cAndPerm mask) c := by
  intro htag
  simp only [cAndPerm, Bool.and_eq_true] at htag
  exact ⟨htag.1, htag.2, CapBounds.subset_refl _, Perms.inter_le_left _ _, rfl⟩

theorem cSetBounds_monotone (c : CapWord) (reqLen : Nat) (rep : Bool) :
    DerivedMonotone (c.cSetBounds reqLen rep) c := by
  intro htag
  simp only [cSetBounds, Bool.and_eq_true, decide_eq_true_eq] at htag
  rcases htag with ⟨⟨⟨ht, hu⟩, hwithin⟩, _⟩
  exact ⟨ht, hu, hwithin, Perms.le_refl _, rfl⟩

theorem cIncOffset_monotone (c : CapWord) (delta : BitVec 64) (rep : Bool) :
    DerivedMonotone (c.cIncOffset delta rep) c := by
  intro htag
  simp only [cIncOffset, Bool.and_eq_true] at htag
  rcases htag with ⟨⟨ht, hu⟩, _⟩
  exact ⟨ht, hu, CapBounds.subset_refl _, Perms.le_refl _, rfl⟩

end CapWord

/-- 16-byte capability granule index (`Align(addr, CAPABILITY_DBYTES)` in Morello
    and `addr_to_tag_addr` in `sail-cheri-riscv`). -/
def capGranule (addr : Nat) : Nat :=
  addr / 16

/-- Capability-tagged memory modeling Morello (`src/mem.sail`) and CHERI-RISC-V
    (`src/cheri_mem.sail`, `src/cheri_mem_metadata.sail`). -/
structure CapMem where
  bytes : Nat → BitVec 8
  capTags : Nat → Bool
  capWords : Nat → CapWord

namespace CapMem

/-- Raw data byte write (`__WriteMem` in `sail-morello/src/mem.sail:87-98` and
    `__WriteRAM_Meta(..., false)` in `sail-cheri-riscv/src/cheri_mem_metadata.sail:77-93`):
    writes the byte at `addr` and **unconditionally clears the capability tag** of the
    enclosing 16-byte capability granule `capGranule addr`. -/
def writeRawByte (m : CapMem) (addr : Nat) (b : BitVec 8) : CapMem where
  bytes := fun a => if a = addr then b else m.bytes a
  capTags := fun g => if g = capGranule addr then false else m.capTags g
  capWords := m.capWords

/-- Raw byte write unconditionally strips the enclosing capability granule's tag. -/
theorem writeRawByte_strips_enclosing_cap_tag (m : CapMem) (addr : Nat) (b : BitVec 8) :
    (m.writeRawByte addr b).capTags (capGranule addr) = false := by
  simp [writeRawByte]

/-- Raw byte write preserves capability tags of all disjoint 16-byte granules. -/
theorem writeRawByte_preserves_disjoint_granule_tag
    (m : CapMem) (addr : Nat) (b : BitVec 8) {g : Nat} (hg : g ≠ capGranule addr) :
    (m.writeRawByte addr b).capTags g = m.capTags g := by
  simp [writeRawByte, hg]

/-- Checked capability load (`__ReadTaggedMem` + `LoadCap` permission gating). -/
def readCapGranule (m : CapMem) (auth : CapWord) : StepResult CapWord :=
  if auth.tag && auth.isUnsealed && auth.perms.canLoad &&
     decide (auth.addr.toNat % 16 = 0) && auth.inBounds 16 then
    let g := capGranule auth.addr.toNat
    let stored := m.capWords g
    let effectiveTag := stored.tag && m.capTags g && auth.perms.canLoadCap
    .next { stored with tag := effectiveTag }
  else
    .trap

/-- Checked capability store (`__WriteTaggedMem` + `StoreCap` permission gating). -/
def writeCapGranule (m : CapMem) (auth : CapWord) (val : CapWord) : StepResult CapMem :=
  if auth.tag && auth.isUnsealed && auth.perms.canStore &&
     (!val.tag || auth.perms.canStoreCap) &&
     decide (auth.addr.toNat % 16 = 0) && auth.inBounds 16 then
    let g := capGranule auth.addr.toNat
    .next {
      bytes := m.bytes
      capTags := fun g' => if g' = g then val.tag else m.capTags g'
      capWords := fun g' => if g' = g then val else m.capWords g'
    }
  else
    .trap

/-- If an authority capability lacks `LoadCap` permission, any capability loaded
    through it has `tag = false` (cannot be used to dereference memory). -/
theorem readCapGranule_without_loadCap_strips_tag
    (m : CapMem) (auth : CapWord) (cOut : CapWord)
    (hnoLC : auth.perms.canLoadCap = false)
    (hread : m.readCapGranule auth = .next cOut) :
    cOut.tag = false := by
  unfold readCapGranule at hread
  split at hread
  · simp only [StepResult.next.injEq] at hread
    subst hread
    simp [hnoLC]
  · contradiction

/-- After a raw byte write at `addr`, any subsequent capability load from the
    enclosing 16-byte granule `capGranule addr` yields an untagged (`tag = false`)
    capability, preventing pointer/capability forgery via raw byte overwrites. -/
theorem readCapGranule_after_writeRawByte_untagged
    (m : CapMem) (addr : Nat) (b : BitVec 8) (auth : CapWord) (cOut : CapWord)
    (hgran : capGranule auth.addr.toNat = capGranule addr)
    (hread : (m.writeRawByte addr b).readCapGranule auth = .next cOut) :
    cOut.tag = false := by
  unfold readCapGranule at hread
  split at hread
  · simp only [StepResult.next.injEq] at hread
    subst hread
    simp [hgran, writeRawByte_strips_enclosing_cap_tag]
  · contradiction

end CapMem

/-! ## Part 4: Refinement Bridge to Anneal's Allocation-Provenance Memory (`Trusted/Memory.lean`) -/

/-- Anneal abstract allocation metadata (`Trusted/Memory.lean`). -/
structure AnnealAlloc where
  base : Nat
  len : Nat
  writable : Bool
  live : Bool
  deriving DecidableEq, Repr

/-- Anneal abstract provenance-tracked memory. -/
structure AnnealMem where
  allocs : Nat → Option AnnealAlloc
  bytes : Nat → BitVec 8

namespace AnnealMem

/-- Anneal spatial + provenance check for a `width`-byte read at `(allocId, addr)`. -/
def canRead (am : AnnealMem) (allocId : Option Nat) (addr width : Nat) : Bool :=
  match allocId with
  | none => false
  | some id =>
    match am.allocs id with
    | none => false
    | some a => a.live && decide (a.base ≤ addr ∧ addr + width ≤ a.base + a.len)

/-- Anneal spatial + provenance check for a `width`-byte write at `(allocId, addr)`. -/
def canWrite (am : AnnealMem) (allocId : Option Nat) (addr width : Nat) : Bool :=
  match allocId with
  | none => false
  | some id =>
    match am.allocs id with
    | none => false
    | some a =>
      a.live && a.writable && decide (a.base ≤ addr ∧ addr + width ≤ a.base + a.len)

end AnnealMem

/-- Capability-to-Anneal refinement invariant: every valid (`tag = true`),
    unsealed capability is backed by a live Anneal allocation whose bounds
    enclose `c.bounds` and whose mutability dominates `c.perms.canStore`. -/
def CapRefinesAnneal (c : CapWord) (am : AnnealMem) : Prop :=
  c.tag = true →
  c.isUnsealed = true →
    ∃ id alloc,
      c.allocId = some id ∧
      am.allocs id = some alloc ∧
      alloc.live = true ∧
      alloc.base ≤ c.bounds.base ∧
      c.bounds.top ≤ alloc.base + alloc.len ∧
      (c.perms.canStore = true → alloc.writable = true)

/-- Monotonic capability derivation (`cSetBounds`, `cAndPerm`, `cIncOffset`)
    preserves `CapRefinesAnneal` without consulting the allocator. -/
theorem CapRefinesAnneal.of_derivedMonotone
    {c' c : CapWord} {am : AnnealMem}
    (hmono : CapWord.DerivedMonotone c' c)
    (href : CapRefinesAnneal c am) :
    CapRefinesAnneal c' am := by
  intro htag' _
  obtain ⟨htag, hunsealed, hsub, hperm, hid⟩ := hmono htag'
  obtain ⟨id, alloc, hcid, halloc, hlive, hbase, htop, hwritable⟩ := href htag hunsealed
  refine ⟨id, alloc, hid.trans hcid, halloc, hlive,
    Nat.le_trans hbase hsub.1, Nat.le_trans hsub.2 htop, ?_⟩
  intro hstore'
  exact hwritable (hperm.2.1 hstore')

theorem CapRefinesAnneal.cSetBounds
    {c : CapWord} {am : AnnealMem} (reqLen : Nat) (rep : Bool)
    (href : CapRefinesAnneal c am) :
    CapRefinesAnneal (c.cSetBounds reqLen rep) am :=
  CapRefinesAnneal.of_derivedMonotone (CapWord.cSetBounds_monotone c reqLen rep) href

theorem CapRefinesAnneal.cAndPerm
    {c : CapWord} {am : AnnealMem} (mask : Perms)
    (href : CapRefinesAnneal c am) :
    CapRefinesAnneal (c.cAndPerm mask) am :=
  CapRefinesAnneal.of_derivedMonotone (CapWord.cAndPerm_monotone c mask) href

theorem CapRefinesAnneal.cIncOffset
    {c : CapWord} {am : AnnealMem} (delta : BitVec 64) (rep : Bool)
    (href : CapRefinesAnneal c am) :
    CapRefinesAnneal (c.cIncOffset delta rep) am :=
  CapRefinesAnneal.of_derivedMonotone (CapWord.cIncOffset_monotone c delta rep) href

/-- Fundamental spatial/provenance bridge theorem (loads):
    Whenever a capability `c` satisfies `CapRefinesAnneal c am` and passes the
    CHERI hardware load checks (`c.tag`, `c.isUnsealed`, `c.perms.canLoad`, `c.inBounds width`),
    Anneal's abstract provenance-and-bounds check `am.canRead c.allocId c.addr.toNat width`
    is guaranteed to succeed (`= true`). -/
theorem cheri_load_check_implies_anneal_canRead
    {c : CapWord} {am : AnnealMem} {width : Nat}
    (href : CapRefinesAnneal c am)
    (htag : c.tag = true)
    (hunsealed : c.isUnsealed = true)
    (hbounds : c.inBounds width = true) :
    am.canRead c.allocId c.addr.toNat width = true := by
  obtain ⟨id, alloc, hid, halloc, hlive, hbase, htop, _⟩ := href htag hunsealed
  simp only [CapWord.inBounds, CapBounds.containsRange, decide_eq_true_eq] at hbounds
  have hlo : alloc.base ≤ c.addr.toNat := Nat.le_trans hbase hbounds.1
  have hhi : c.addr.toNat + width ≤ alloc.base + alloc.len := Nat.le_trans hbounds.2 htop
  simp [AnnealMem.canRead, hid, halloc, hlive, hlo, hhi]

/-- Fundamental spatial/provenance bridge theorem (stores):
    Whenever a capability `c` satisfies `CapRefinesAnneal c am` and passes the
    CHERI hardware store checks (`c.tag`, `c.isUnsealed`, `c.perms.canStore`, `c.inBounds width`),
    Anneal's abstract provenance, mutability, and bounds check
    `am.canWrite c.allocId c.addr.toNat width` is guaranteed to succeed (`= true`). -/
theorem cheri_store_check_implies_anneal_canWrite
    {c : CapWord} {am : AnnealMem} {width : Nat}
    (href : CapRefinesAnneal c am)
    (htag : c.tag = true)
    (hunsealed : c.isUnsealed = true)
    (hstore : c.perms.canStore = true)
    (hbounds : c.inBounds width = true) :
    am.canWrite c.allocId c.addr.toNat width = true := by
  obtain ⟨id, alloc, hid, halloc, hlive, hbase, htop, hwritable⟩ := href htag hunsealed
  have hwr := hwritable hstore
  simp only [CapWord.inBounds, CapBounds.containsRange, decide_eq_true_eq] at hbounds
  have hlo : alloc.base ≤ c.addr.toNat := Nat.le_trans hbase hbounds.1
  have hhi : c.addr.toNat + width ≤ alloc.base + alloc.len := Nat.le_trans hbounds.2 htop
  simp [AnnealMem.canWrite, hid, halloc, hlive, hwr, hlo, hhi]

/-- Coupled CHERI + Anneal state for `BridgeTransition` verification. -/
structure CoupledCapState where
  cap : CapWord
  cheriMem : CapMem
  annealMem : AnnealMem

/-- CHERI 1-byte store step on `CoupledCapState`: traps on capability violation,
    otherwise updates both `cheriMem` (clearing the enclosing capability tag)
    and `annealMem`. -/
def cheriByteStoreStep (b : BitVec 8) (s : CoupledCapState) : StepResult CoupledCapState :=
  if s.cap.tag && s.cap.isUnsealed && s.cap.perms.canStore && s.cap.inBounds 1 then
    let addr := s.cap.addr.toNat
    .next {
      cap := s.cap
      cheriMem := s.cheriMem.writeRawByte addr b
      annealMem := {
        s.annealMem with
        bytes := fun a => if a = addr then b else s.annealMem.bytes a
      }
    }
  else
    .trap

/-- `BridgeTransition` proving that every non-trapping CHERI byte store
    satisfies Anneal's `canWrite` spatial/provenance safety check, preserves
    `CapRefinesAnneal`, and strips the enclosing capability tag. -/
def cheriByteStoreBridge (b : BitVec 8) : BridgeTransition CoupledCapState where
  pre := fun s => CapRefinesAnneal s.cap s.annealMem
  step := cheriByteStoreStep b
  nextRel := fun s s' =>
    s.annealMem.canWrite s.cap.allocId s.cap.addr.toNat 1 = true ∧
    CapRefinesAnneal s'.cap s'.annealMem ∧
    s'.cheriMem.capTags (capGranule s.cap.addr.toNat) = false
  sound := by
    intro s hpre
    unfold cheriByteStoreStep
    by_cases hcond : (s.cap.tag && s.cap.isUnsealed && s.cap.perms.canStore && s.cap.inBounds 1) = true
    · simp only [hcond, ↓reduceIte]
      simp only [Bool.and_eq_true] at hcond
      rcases hcond with ⟨⟨⟨htag, hunsealed⟩, hstore⟩, hbounds⟩
      refine ⟨?_, ?_, ?_⟩
      · exact cheri_store_check_implies_anneal_canWrite hpre htag hunsealed hstore hbounds
      · exact hpre
      · exact CapMem.writeRawByte_strips_enclosing_cap_tag s.cheriMem s.cap.addr.toNat b
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]

theorem cheriByteStoreBridge_never_stuck (b : BitVec 8) {s : CoupledCapState}
    (hpre : CapRefinesAnneal s.cap s.annealMem) :
    (cheriByteStoreBridge b).step s ≠ .stuck :=
  (cheriByteStoreBridge b).no_stuck hpre

/-- CHERI 16-byte capability store step on `CoupledCapState`: stores a capability
    `val` through authority `s.cap`, preserving `val.tag` iff `val.tag = true` and
    `s.cap.perms.canStoreCap = true`. -/
def cheriCapStoreStep (val : CapWord) (s : CoupledCapState) : StepResult CoupledCapState :=
  match s.cheriMem.writeCapGranule s.cap val with
  | .next m' => .next { s with cheriMem := m' }
  | .done => .done
  | .trap => .trap
  | .stuck => .stuck

/-- `BridgeTransition` for 16-byte capability stores: proves that every non-trapping
    CHERI capability store refines Anneal's 16-byte `canWrite` check, preserves
    `CapRefinesAnneal` on the authority capability, and sets the target granule tag
    to `val.tag`. -/
def cheriCapStoreBridge (val : CapWord) : BridgeTransition CoupledCapState where
  pre := fun s => CapRefinesAnneal s.cap s.annealMem
  step := cheriCapStoreStep val
  nextRel := fun s s' =>
    s.annealMem.canWrite s.cap.allocId s.cap.addr.toNat 16 = true ∧
    CapRefinesAnneal s'.cap s'.annealMem ∧
    s'.cheriMem.capTags (capGranule s.cap.addr.toNat) = val.tag
  sound := by
    intro s hpre
    unfold cheriCapStoreStep CapMem.writeCapGranule
    by_cases hcond :
        (s.cap.tag && s.cap.isUnsealed && s.cap.perms.canStore &&
         (!val.tag || s.cap.perms.canStoreCap) &&
         decide (s.cap.addr.toNat % 16 = 0) && s.cap.inBounds 16) = true
    · simp only [hcond, ↓reduceIte]
      simp only [Bool.and_eq_true] at hcond
      rcases hcond with ⟨⟨⟨⟨⟨htag, hunsealed⟩, hstore⟩, _⟩, _⟩, hbounds⟩
      refine ⟨?_, ?_, ?_⟩
      · exact cheri_store_check_implies_anneal_canWrite hpre htag hunsealed hstore hbounds
      · exact hpre
      · simp
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]

theorem cheriCapStoreBridge_never_stuck (val : CapWord) {s : CoupledCapState}
    (hpre : CapRefinesAnneal s.cap s.annealMem) :
    (cheriCapStoreBridge val).step s ≠ .stuck :=
  (cheriCapStoreBridge val).no_stuck hpre

end CheriCapabilityBridge

/-! ## Axiom Audit -/

/-- info: 'SailArmX86CheriRiscvProbe.SailTinyArmModel.tinyArmBridge_never_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms SailTinyArmModel.tinyArmBridge_never_stuck

/-- info: 'SailArmX86CheriRiscvProbe.SailTinyX86DecodeAudit.tinyX86_rip_relative_discrepancy' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms SailTinyX86DecodeAudit.tinyX86_rip_relative_discrepancy

/-- info: 'SailArmX86CheriRiscvProbe.CheriCapabilityBridge.CapRefinesAnneal.cSetBounds' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CheriCapabilityBridge.CapRefinesAnneal.cSetBounds

/-- info: 'SailArmX86CheriRiscvProbe.CheriCapabilityBridge.CapMem.readCapGranule_after_writeRawByte_untagged' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CheriCapabilityBridge.CapMem.readCapGranule_after_writeRawByte_untagged

/-- info: 'SailArmX86CheriRiscvProbe.CheriCapabilityBridge.cheri_load_check_implies_anneal_canRead' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CheriCapabilityBridge.cheri_load_check_implies_anneal_canRead

/-- info: 'SailArmX86CheriRiscvProbe.CheriCapabilityBridge.cheri_store_check_implies_anneal_canWrite' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CheriCapabilityBridge.cheri_store_check_implies_anneal_canWrite

/-- info: 'SailArmX86CheriRiscvProbe.CheriCapabilityBridge.cheriByteStoreBridge_never_stuck' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms CheriCapabilityBridge.cheriByteStoreBridge_never_stuck

/-- info: 'SailArmX86CheriRiscvProbe.CheriCapabilityBridge.cheriCapStoreBridge_never_stuck' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CheriCapabilityBridge.cheriCapStoreBridge_never_stuck

end SailArmX86CheriRiscvProbe
